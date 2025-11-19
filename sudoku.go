package main

import (
	"bufio"
	"bytes"
	"crypto/aes"
	"crypto/cipher"
	crand "crypto/rand"
	"crypto/sha256"
	"encoding/binary"
	"encoding/json"
	"errors"
	"fmt"
	"io"
	"log"
	mrand "math/rand"
	"net"
	"os"
	"sort"
	"sync"
	"time"

	"golang.org/x/crypto/chacha20poly1305"
)

// ==========================================
// 1. 配置与日志
// ==========================================

type Config struct {
	Mode             string `json:"mode"`              // 运行模式："client" 或 "server"
	LocalPort        int    `json:"local_port"`        // 本地监听端口，如 1080
	ServerAddress    string `json:"server_address"`    // 服务器地址，如 "1.2.3.4:8080"
	FallbackAddr     string `json:"fallback_address"`  // 回落地址，如 "127.0.0.1:80"
	Key              string `json:"key"`               // 协议密钥
	AEAD             string `json:"aead"`              // 加密方式："aes-128-gcm", "chacha20-poly1305", "none"
	SuspiciousAction string `json:"suspicious_action"` // 可疑行为处理："fallback"(回落) 或 "silent"(静默)
	PaddingMin       int    `json:"padding_min"`       // 最小填充百分比 (0-100)
	PaddingMax       int    `json:"padding_max"`       // 最大填充百分比 (0-100)
}

const (
	HandshakeTimeout = 5 * time.Second // 握手超时时间
	IOBufferSize     = 32 * 1024       // IO缓冲区大小：32KB，用于提高吞吐量
)

var (
	encodeTable [256][][4]byte  // 编码表
	decodeMap   map[uint32]byte // 解码映射表
	config      Config          // 全局配置
	logger      *log.Logger     // 日志记录器
)

func init() {
	logger = log.New(os.Stdout, "", log.LstdFlags|log.Lshortfile)
}

// ==========================================
// 2. 数独引擎（O(1)混淆）
// ==========================================

// Grid 表示一个4x4数独网格
type Grid [16]uint8

// generateAllGrids 生成所有有效的4x4数独网格
func generateAllGrids() []Grid {
	var grids []Grid
	var g Grid
	var backtrack func(int)
	backtrack = func(idx int) {
		if idx == 16 {
			grids = append(grids, g)
			return
		}
		row, col := idx/4, idx%4
		br, bc := (row/2)*2, (col/2)*2
		for num := uint8(1); num <= 4; num++ {
			valid := true
			for i := 0; i < 4; i++ {
				if g[row*4+i] == num || g[i*4+col] == num {
					valid = false
					break
				}
			}
			if valid {
				for r := 0; r < 2; r++ {
					for c := 0; c < 2; c++ {
						if g[(br+r)*4+(bc+c)] == num {
							valid = false
							break
						}
					}
				}
			}
			if valid {
				g[idx] = num
				backtrack(idx + 1)
				g[idx] = 0
			}
		}
	}
	backtrack(0)
	return grids
}

// initTables 初始化编码和解码表
func initTables(key string) {
	start := time.Now()
	allGrids := generateAllGrids()

	h := sha256.New()
	h.Write([]byte(key))
	seed := int64(binary.BigEndian.Uint64(h.Sum(nil)[:8]))
	rng := mrand.New(mrand.NewSource(seed))

	shuffledGrids := make([]Grid, 288)
	copy(shuffledGrids, allGrids)
	rng.Shuffle(len(shuffledGrids), func(i, j int) {
		shuffledGrids[i], shuffledGrids[j] = shuffledGrids[j], shuffledGrids[i]
	})

	decodeMap = make(map[uint32]byte)

	var combinations [][]int
	var combine func(int, int, []int)
	combine = func(s, k int, c []int) {
		if k == 0 {
			tmp := make([]int, len(c))
			copy(tmp, c)
			combinations = append(combinations, tmp)
			return
		}
		for i := s; i <= 16-k; i++ {
			c = append(c, i)
			combine(i+1, k-1, c)
			c = c[:len(c)-1]
		}
	}
	combine(0, 4, []int{})

	for byteVal := 0; byteVal < 256; byteVal++ {
		targetGrid := shuffledGrids[byteVal]
		for _, positions := range combinations {
			var currentHints [4]byte
			for i, pos := range positions {
				val := targetGrid[pos]
				hint := byte(((val - 1) << 5) | (uint8(pos) & 0x0F))
				currentHints[i] = hint
			}

			matchCount := 0
			for _, g := range allGrids {
				match := true
				for _, h := range currentHints {
					pos := h & 0x0F
					val := ((h >> 5) & 0x03) + 1
					if g[pos] != val {
						match = false
						break
					}
				}
				if match {
					matchCount++
					if matchCount > 1 {
						break
					}
				}
			}

			if matchCount == 1 {
				encodeTable[byteVal] = append(encodeTable[byteVal], currentHints)
				key := packHintsToKey(currentHints)
				decodeMap[key] = byte(byteVal)
			}
		}
	}
	logger.Printf("[Init] Sudoku Tables initialized in %v. Cipher: %s", time.Since(start), config.AEAD)
}

// packHintsToKey 将提示打包成键值
func packHintsToKey(hints [4]byte) uint32 {
	cleanHints := [4]byte{}
	for i, h := range hints {
		cleanHints[i] = h & 0x6F
	}
	s := cleanHints[:]
	sort.Slice(s, func(i, j int) bool {
		return (s[i] & 0x0F) < (s[j] & 0x0F)
	})
	return binary.BigEndian.Uint32(s)
}

// ==========================================
// 3. 传输层
// ==========================================

// SudokuConn 是对net.Conn的封装，提供数独混淆功能
type SudokuConn struct {
	net.Conn                 // 底层连接
	reader     *bufio.Reader // 读取缓冲区
	recorder   *bytes.Buffer // 记录器，用于记录握手阶段的数据
	recording  bool          // 是否正在记录
	recordLock sync.Mutex    // 记录锁

	// 读取状态
	rawBuf      []byte // 从网络读取的原始数据缓冲区
	pendingData []byte // 已解码但尚未被消费的数据
	hintBuf     []byte // 存储不完整提示的临时缓冲区

	// 写入状态
	rng         *mrand.Rand // 每个连接的本地随机数生成器
	paddingRate float32     // 此连接的目标填充率
}

// NewSudokuConn 创建一个新的SudokuConn
func NewSudokuConn(c net.Conn, record bool) *SudokuConn {

	var seedBytes [8]byte
	if _, err := crand.Read(seedBytes[:]); err != nil {
		// 极端情况降级为时间种子
		binary.BigEndian.PutUint64(seedBytes[:], uint64(time.Now().UnixNano()))
	}
	seed := int64(binary.BigEndian.Uint64(seedBytes[:]))
	localRng := mrand.New(mrand.NewSource(seed))

	pMin := float32(config.PaddingMin) / 100.0
	pRange := float32(config.PaddingMax-config.PaddingMin) / 100.0
	pRate := pMin + localRng.Float32()*pRange

	sc := &SudokuConn{
		Conn:        c,
		reader:      bufio.NewReaderSize(c, IOBufferSize),
		rawBuf:      make([]byte, IOBufferSize),
		pendingData: make([]byte, 0, 4096),
		hintBuf:     make([]byte, 0, 4),
		rng:         localRng,
		paddingRate: pRate,
	}
	if record {
		sc.recorder = new(bytes.Buffer)
		sc.recording = true
	}
	return sc
}

// StopRecording 停止记录并释放内存
func (sc *SudokuConn) StopRecording() {
	sc.recordLock.Lock()
	sc.recording = false
	sc.recorder = nil
	sc.recordLock.Unlock()
}

// GetBufferedAndRecorded 返回已记录和缓冲的数据
// 对于回落逻辑确保不丢失数据至关重要
func (sc *SudokuConn) GetBufferedAndRecorded() []byte {
	sc.recordLock.Lock()
	defer sc.recordLock.Unlock()

	var recorded []byte
	if sc.recorder != nil {
		recorded = sc.recorder.Bytes()
	}

	// 检查bufio中缓存的内容
	buffered := sc.reader.Buffered()
	if buffered > 0 {
		peeked, _ := sc.reader.Peek(buffered)
		// 合并已记录和缓冲的数据
		full := make([]byte, len(recorded)+len(peeked))
		copy(full, recorded)
		copy(full[len(recorded):], peeked)
		return full
	}
	return recorded
}

// Write 通过减少分配和使用块逻辑优化写入性能
func (sc *SudokuConn) Write(p []byte) (n int, err error) {
	if len(p) == 0 {
		return 0, nil
	}

	// 预分配输出缓冲区
	// 估计：len*4（提示）+ 填充。6倍的安全系数可覆盖50%的填充
	outCapacity := len(p) * 6
	out := make([]byte, 0, outCapacity)

	pads := []byte{0x80, 0x10, 0x90} // 用作填充的无效提示

	for _, b := range p {
		// 字节前随机填充
		// 使用本地随机数生成器速度快
		if sc.rng.Float32() < sc.paddingRate {
			out = append(out, pads[sc.rng.Intn(3)])
		}

		puzzles := encodeTable[b]
		puzzle := puzzles[sc.rng.Intn(len(puzzles))]

		// 打乱提示顺序（内联Fisher-Yates算法提高速度）
		// 由于是4个元素的数组，我们可以简单地手动循环
		perm := []int{0, 1, 2, 3}
		sc.rng.Shuffle(4, func(i, j int) { perm[i], perm[j] = perm[j], perm[i] })

		for _, idx := range perm {
			// 提示组内的内部填充
			if sc.rng.Float32() < sc.paddingRate {
				out = append(out, pads[sc.rng.Intn(3)])
			}
			out = append(out, puzzle[idx])
		}
	}

	// 尾部填充
	if sc.rng.Float32() < sc.paddingRate {
		out = append(out, pads[sc.rng.Intn(3)])
	}

	_, err = sc.Conn.Write(out)
	// 根据io.Writer契约返回原始长度
	return len(p), err
}

// Read 优化块读取而非逐字节读取
func (sc *SudokuConn) Read(p []byte) (n int, err error) {
	// 1. 如果有待处理的解码数据，则立即返回
	if len(sc.pendingData) > 0 {
		n = copy(p, sc.pendingData)
		// 移动pendingData
		// 如果为空，重置切片为0以重用底层数组
		if n == len(sc.pendingData) {
			sc.pendingData = sc.pendingData[:0]
		} else {
			sc.pendingData = sc.pendingData[n:]
		}
		return n, nil
	}

	// 2. 从网络读取一块数据
	// 我们持续读取直到产生至少1字节的输出或遇到错误
	for {
		// 如果pendingData在上一次循环迭代中被填充
		if len(sc.pendingData) > 0 {
			break
		}

		nr, rErr := sc.reader.Read(sc.rawBuf)
		if nr > 0 {
			chunk := sc.rawBuf[:nr]

			// 记录（复制逻辑以避免长时间持有锁）
			sc.recordLock.Lock()
			if sc.recording {
				sc.recorder.Write(chunk)
			}
			sc.recordLock.Unlock()

			// 处理数据块
			for _, b := range chunk {
				// 过滤填充：有效提示位7和4为0。填充有1。
				// 掩码0x90 (10010000)。如果结果!=0，则为填充
				if (b & 0x90) != 0 {
					continue
				}

				sc.hintBuf = append(sc.hintBuf, b)
				if len(sc.hintBuf) == 4 {
					key := packHintsToKey([4]byte{sc.hintBuf[0], sc.hintBuf[1], sc.hintBuf[2], sc.hintBuf[3]})
					val, ok := decodeMap[key]
					if !ok {
						return 0, errors.New("INVALID_SUDOKU_MAP_MISS")
					}
					sc.pendingData = append(sc.pendingData, val)
					sc.hintBuf = sc.hintBuf[:0] // 重置长度，保持容量
				}
			}
		}

		if rErr != nil {
			return 0, rErr
		}

		// 有数据，跳出循环返回数据
		if len(sc.pendingData) > 0 {
			break
		}
		// 否则继续循环从网络读取更多数据
	}

	n = copy(p, sc.pendingData)
	if n == len(sc.pendingData) {
		sc.pendingData = sc.pendingData[:0]
	} else {
		sc.pendingData = sc.pendingData[n:]
	}
	return n, nil
}

// ==========================================
// 4. 加密层（AEAD）
// ==========================================

// CipherConn 是对net.Conn的封装，提供AEAD加密功能
type CipherConn struct {
	net.Conn               // 底层连接
	aead      cipher.AEAD  // AEAD密码接口
	readBuf   bytes.Buffer // 读取缓冲区
	nonceSize int          // Nonce大小
}

// NewCipherConn 创建一个新的CipherConn
func NewCipherConn(c net.Conn, key string, method string) (*CipherConn, error) {
	if method == "none" {
		return &CipherConn{Conn: c, aead: nil}, nil
	}

	h := sha256.New()
	h.Write([]byte(key))
	keyBytes := h.Sum(nil)

	var aead cipher.AEAD
	var err error

	switch method {
	case "aes-128-gcm":
		block, _ := aes.NewCipher(keyBytes[:16])
		aead, err = cipher.NewGCM(block)
	case "chacha20-poly1305":
		aead, err = chacha20poly1305.New(keyBytes)
	default:
		return nil, fmt.Errorf("unsupported cipher: %s", method)
	}
	if err != nil {
		return nil, err
	}

	return &CipherConn{
		Conn:      c,
		aead:      aead,
		nonceSize: aead.NonceSize(),
	}, nil
}

// Write 实现加密写入
func (cc *CipherConn) Write(p []byte) (int, error) {
	if cc.aead == nil {
		return cc.Conn.Write(p)
	}

	maxPayload := 65535 - cc.nonceSize - cc.aead.Overhead()
	totalWritten := 0

	// 使用bytes.Buffer构建帧以确保对底层连接的原子写入
	var frameBuf bytes.Buffer
	header := make([]byte, 2)
	nonce := make([]byte, cc.nonceSize)

	for len(p) > 0 {
		chunkSize := len(p)
		if chunkSize > maxPayload {
			chunkSize = maxPayload
		}
		chunk := p[:chunkSize]
		p = p[chunkSize:]

		if _, err := io.ReadFull(crand.Reader, nonce); err != nil {
			return totalWritten, err
		}

		ciphertext := cc.aead.Seal(nil, nonce, chunk, nil)

		frameLen := len(nonce) + len(ciphertext)
		binary.BigEndian.PutUint16(header, uint16(frameLen))

		frameBuf.Reset()
		frameBuf.Write(header)
		frameBuf.Write(nonce)
		frameBuf.Write(ciphertext)

		if _, err := cc.Conn.Write(frameBuf.Bytes()); err != nil {
			return totalWritten, err
		}
		totalWritten += chunkSize
	}
	return totalWritten, nil
}

// Read 实现解密读取
func (cc *CipherConn) Read(p []byte) (int, error) {
	if cc.aead == nil {
		return cc.Conn.Read(p)
	}

	if cc.readBuf.Len() > 0 {
		return cc.readBuf.Read(p)
	}

	// 读取帧头（2字节）
	header := make([]byte, 2)
	if _, err := io.ReadFull(cc.Conn, header); err != nil {
		return 0, err
	}
	frameLen := int(binary.BigEndian.Uint16(header))

	// 读取帧体
	body := make([]byte, frameLen)
	if _, err := io.ReadFull(cc.Conn, body); err != nil {
		return 0, err
	}

	if len(body) < cc.nonceSize {
		return 0, errors.New("frame too short")
	}
	nonce := body[:cc.nonceSize]
	ciphertext := body[cc.nonceSize:]

	plaintext, err := cc.aead.Open(nil, nonce, ciphertext, nil)
	if err != nil {
		return 0, errors.New("decryption failed")
	}

	cc.readBuf.Write(plaintext)
	return cc.readBuf.Read(p)
}

// ==========================================
// 5. 连接逻辑
// ==========================================

// handleSuspicious 处理可疑连接，通过恢复缓冲数据实现回落
func handleSuspicious(sConn *SudokuConn, rawConn net.Conn) {
	action := config.SuspiciousAction
	remoteAddr := rawConn.RemoteAddr().String()

	if action == "silent" {
		logger.Printf("[Silent] Suspicious %s. Tarpit.", remoteAddr)
		io.Copy(io.Discard, rawConn)
		time.Sleep(5 * time.Second)
		rawConn.Close()
		return
	}

	if config.FallbackAddr == "" {
		rawConn.Close()
		return
	}

	logger.Printf("[Fallback] %s -> %s", remoteAddr, config.FallbackAddr)
	dst, err := net.DialTimeout("tcp", config.FallbackAddr, 3*time.Second)
	if err != nil {
		rawConn.Close()
		return
	}

	// 关键：获取在bufio中缓冲或记录的数据
	badData := sConn.GetBufferedAndRecorded()

	// 将不良数据转发到上游
	if len(badData) > 0 {
		if _, err := dst.Write(badData); err != nil {
			dst.Close()
			rawConn.Close()
			return
		}
	}

	// 启动全双工桥接
	var wg sync.WaitGroup
	wg.Add(2)

	// 客户端 -> 回落服务器
	go func() {
		defer wg.Done()
		defer dst.Close() // 向上游发送FIN
		io.Copy(dst, rawConn)
	}()

	// 回落服务器 -> 客户端
	go func() {
		defer wg.Done()
		defer rawConn.Close() // 向客户端发送FIN
		io.Copy(rawConn, dst)
	}()

	wg.Wait()
}

// handleServerConnection 处理服务器连接
func handleServerConnection(rawConn net.Conn) {
	// 1. 数独层
	sConn := NewSudokuConn(rawConn, true)

	// 2. 加密层
	cConn, err := NewCipherConn(sConn, config.Key, config.AEAD)
	if err != nil {
		rawConn.Close()
		return
	}

	// 3. 握手
	handshakeBuf := make([]byte, 16)
	rawConn.SetReadDeadline(time.Now().Add(HandshakeTimeout))
	_, err = io.ReadFull(cConn, handshakeBuf)
	rawConn.SetReadDeadline(time.Time{})

	if err != nil {
		logger.Printf("[Security] Handshake fail: %v", err)
		// 触发回落
		handleSuspicious(sConn, rawConn)
		return
	}

	// 4. 验证时间戳
	ts := int64(binary.BigEndian.Uint64(handshakeBuf[:8]))
	if abs(time.Now().Unix()-ts) > 60 {
		logger.Printf("[Security] Time skew/Replay")
		handleSuspicious(sConn, rawConn)
		return
	}

	sConn.StopRecording()
	handleSocks5(cConn)
}

// abs 计算绝对值
func abs(x int64) int64 {
	if x < 0 {
		return -x
	}
	return x
}

// handleSocks5 处理SOCKS5协议
func handleSocks5(conn net.Conn) {
	defer conn.Close()
	buf := make([]byte, 262)

	// 协商阶段
	if _, err := io.ReadFull(conn, buf[:2]); err != nil {
		return
	}
	if buf[0] != 0x05 {
		return
	}
	nMethods := int(buf[1])
	if _, err := io.ReadFull(conn, buf[:nMethods]); err != nil {
		return
	}
	conn.Write([]byte{0x05, 0x00})

	// 请求阶段
	if _, err := io.ReadFull(conn, buf[:4]); err != nil {
		return
	}
	if buf[1] != 0x01 {
		return
	} // 仅支持CONNECT方法

	var destAddr string
	switch buf[3] {
	case 0x01: // IPv4
		if _, err := io.ReadFull(conn, buf[:4]); err != nil {
			return
		}
		portBuf := make([]byte, 2)
		if _, err := io.ReadFull(conn, portBuf); err != nil {
			return
		}
		destAddr = fmt.Sprintf("%s:%d", net.IP(buf[:4]).String(), binary.BigEndian.Uint16(portBuf))
	case 0x03: // 域名
		if _, err := io.ReadFull(conn, buf[:1]); err != nil {
			return
		}
		dLen := int(buf[0])
		domainBuf := make([]byte, dLen)
		if _, err := io.ReadFull(conn, domainBuf); err != nil {
			return
		}
		portBuf := make([]byte, 2)
		if _, err := io.ReadFull(conn, portBuf); err != nil {
			return
		}
		destAddr = fmt.Sprintf("%s:%d", string(domainBuf), binary.BigEndian.Uint16(portBuf))
	default:
		return
	}
	logger.Printf("[SOCKS5] Connecting to %s", destAddr)
	target, err := net.DialTimeout("tcp", destAddr, 10*time.Second)
	if err != nil {
		logger.Printf("[SOCKS5] Connect failed: %v", err)
		return
	}
	defer target.Close()

	conn.Write([]byte{0x05, 0x00, 0x00, 0x01, 0, 0, 0, 0, 0, 0})

	// 数据桥接
	var wg sync.WaitGroup
	wg.Add(2)
	go func() { io.Copy(target, conn); target.Close(); wg.Done() }()
	go func() { io.Copy(conn, target); conn.Close(); wg.Done() }()
	wg.Wait()
}

// ==========================================
// 6. 客户端/服务器主循环
// ==========================================

// runClient 运行客户端
func runClient() {
	l, err := net.Listen("tcp", fmt.Sprintf(":%d", config.LocalPort))
	if err != nil {
		logger.Fatal(err)
	}
	logger.Printf("Client on :%d -> %s", config.LocalPort, config.ServerAddress)

	for {
		c, err := l.Accept()
		if err != nil {
			continue
		}
		go func(local net.Conn) {
			defer local.Close()
			remoteRaw, err := net.Dial("tcp", config.ServerAddress)
			if err != nil {
				return
			}
			defer remoteRaw.Close()

			sConn := NewSudokuConn(remoteRaw, false)
			cConn, err := NewCipherConn(sConn, config.Key, config.AEAD)
			if err != nil {
				return
			}

			handshake := make([]byte, 16)
			binary.BigEndian.PutUint64(handshake[:8], uint64(time.Now().Unix()))
			crand.Read(handshake[8:])
			if _, err := cConn.Write(handshake); err != nil {
				return
			}

			go io.Copy(cConn, local)
			io.Copy(local, cConn)
		}(c)
	}
}

// runServer 运行服务器
func runServer() {
	l, err := net.Listen("tcp", fmt.Sprintf(":%d", config.LocalPort))
	if err != nil {
		logger.Fatal(err)
	}
	logger.Printf("Server on :%d (Fallback: %s)", config.LocalPort, config.FallbackAddr)

	for {
		c, err := l.Accept()
		if err != nil {
			continue
		}
		go handleServerConnection(c)
	}
}

// main 主函数
func main() {
	f, err := os.Open("config.json")
	if err != nil {
		log.Fatal(err)
	}
	if err := json.NewDecoder(f).Decode(&config); err != nil {
		log.Fatal(err)
	}
	f.Close()

	initTables(config.Key)

	if config.Mode == "client" {
		runClient()
	} else {
		runServer()
	}
}
