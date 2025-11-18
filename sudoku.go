package main

import (
	"bytes"
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
)

// ==========================================
// 1. Config
// ==========================================

type Config struct {
	Mode          string `json:"mode"`
	LocalPort     int    `json:"local_port"`
	ServerAddress string `json:"server_address"`
	FallbackAddr  string `json:"fallback_address"` // 新增：回落地址
	Key           string `json:"key"`
}

const (
	HandshakeTimeout = 10 * time.Second // 握手必须快，否则回落
)

var (
	encodeTable [256][][4]byte
	decodeMap   map[uint32]byte
	config      Config
)

// ==========================================
// 2. Sudoku Engine (O(1) Pre-computation)
// ==========================================

type Grid [16]uint8

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
					valid = false; break
				}
			}
			if valid {
				for r := 0; r < 2; r++ {
					for c := 0; c < 2; c++ {
						if g[(br+r)*4+(bc+c)] == num {
							valid = false; break
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

func initTables(key string) {
	start := time.Now()
	// ... (Engine logic same as before)
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
	
	// Precompute combinations C(16,4)
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
			// 我们只存储核心信息：Pos(4bit) 和 Val-1(2bit)
			// 实际网络传输时会填充随机噪声
			for i, pos := range positions {
				val := targetGrid[pos]
				// 存储格式：High 4 = Pos, Low 4 = Val-1 (Bit 2,3 are 0 for now)
				currentHints[i] = byte((uint8(pos) << 4) | (val - 1))
			}

			matchCount := 0
			for _, g := range allGrids {
				match := true
				for _, h := range currentHints {
					pos := h >> 4
					val := (h & 0x0F) + 1
					if g[pos] != val { match = false; break }
				}
				if match {
					matchCount++
					if matchCount > 1 { break }
				}
			}

			if matchCount == 1 {
				encodeTable[byteVal] = append(encodeTable[byteVal], currentHints)
				key := packHintsToKey(currentHints)
				decodeMap[key] = byte(byteVal)
			}
		}
	}
	log.Printf("Tables initialized in %v", time.Since(start))
}

func packHintsToKey(hints [4]byte) uint32 {
	// 解码时，我们只关心 High 4 bits (Pos) 和 Low 2 bits (Val)
	// 中间的 Bits 2,3 是噪声，必须清洗掉
	cleanHints := [4]byte{}
	for i, h := range hints {
		pos := h & 0xF0
		val := h & 0x03 // 清洗噪声，只留最低2位
		cleanHints[i] = pos | val
	}
	
	// 排序
	s := cleanHints[:]
	sort.Slice(s, func(i, j int) bool {
		return (s[i] >> 4) < (s[j] >> 4)
	})
	return binary.BigEndian.Uint32(s)
}

// ==========================================
// 3. Protocol Layer with Noise Injection
// ==========================================

type SudokuConn struct {
	net.Conn
	readBuf bytes.Buffer
	tmpBuf  []byte
}

func NewSudokuConn(c net.Conn) *SudokuConn {
	return &SudokuConn{Conn: c, tmpBuf: make([]byte, 4096)}
}

func (sc *SudokuConn) Write(p []byte) (n int, err error) {
	if len(p) == 0 { return 0, nil }
	out := make([]byte, 0, len(p)*4)
	
	for _, b := range p {
		puzzles := encodeTable[b]
		if len(puzzles) == 0 { return 0, errors.New("table miss") }
		
		// 2. O(1) 随机选择一个谜题用于混淆
		// 使用 fast rand (math/rand is fine for obfuscation selection)
		puzzle := puzzles[mrand.Intn(len(puzzles))]
		
		// 3. 混淆 Hint 顺序 (可选)
		// 虽然 Puzzle 是一组集合，但为了让网络流量看起来更随机，我们打乱发送这4个Hint的顺序
		// Decoder 会重新排序，所以这里乱序是安全的
		perm := mrand.Perm(4)
		for _, idx := range perm {
			out = append(out, puzzle[idx])
		}	
		/* ====下面是防止深度包检测的算法，暂不启用=====

		// 构造带噪声的谜题
		// basePuzzle[i] 格式: [Pos 4bit] [00] [Val 2bit]
		// 我们要在中间的 [00] 填入随机位
		// var noisyPuzzle [4]byte
		// for i, h := range basePuzzle {
		// 	// 生成 2 bit 随机噪声 (0-3) << 2
		// 	noise := byte(mrand.Intn(4)) << 2
		// 	noisyPuzzle[i] = h | noise 
		// }

		// 乱序发送 Hints
		// perm := mrand.Perm(4)
		// for _, idx := range perm {
		// 	out = append(out, noisyPuzzle[idx])
		// }

		========================================*/
	}
	_, err = sc.Conn.Write(out)
	return len(p), err
}

func (sc *SudokuConn) Read(p []byte) (n int, err error) {
	// 这里的 Read 逻辑需要配合 Fallback。
	// 如果解码失败，我们不能简单的 return error，
	// 而是应该让上层知道“这不是数独流量”。
	// 但为了接口兼容，这里如果是标准 SudokuConn 使用，还是返回 error。
	// Fallback 的探测逻辑会在 handleServerConnection 中手动处理。
	
	if sc.readBuf.Len() >= 4 { return sc.decodeNext(p) }
	
	rn, rerr := sc.Conn.Read(sc.tmpBuf)
	if rn > 0 { sc.readBuf.Write(sc.tmpBuf[:rn]) }
	
	if sc.readBuf.Len() >= 4 { return sc.decodeNext(p) }
	if rerr != nil { return 0, rerr }
	
	return sc.Read(p)
}

func (sc *SudokuConn) decodeNext(p []byte) (int, error) {
	total := 0
	for total < len(p) && sc.readBuf.Len() >= 4 {
		chunk := sc.readBuf.Next(4)
		var hints [4]byte
		copy(hints[:], chunk)
		
		// packHintsToKey 会自动忽略 Bit 2/3 的噪声
		key := packHintsToKey(hints)
		
		val, ok := decodeMap[key]
		if !ok {
			return total, errors.New("INVALID_SUDOKU")
		}
		p[total] = val
		total++
	}
	return total, nil
}

// ==========================================
// 4. Anti-Replay & Handshake
// ==========================================

var (
	nonceCache = make(map[string]int64)
	cacheLock  sync.Mutex
)

func cleanupCache() {
	for {
		time.Sleep(1 * time.Minute)
		now := time.Now().Unix()
		cacheLock.Lock()
		for k, ts := range nonceCache {
			if now-ts > 90 { delete(nonceCache, k) }
		}
		cacheLock.Unlock()
	}
}

// ==========================================
// 5. SOCKS5 & Fallback Logic
// ==========================================

// 将流量转发到 Fallback 地址 (Nginx)
func forwardToFallback(badData []byte, src net.Conn, fallbackAddr string) {
	if fallbackAddr == "" {
		src.Close()
		return
	}
	
	log.Printf("[Fallback] Redirecting suspicious traffic from %s to %s", src.RemoteAddr(), fallbackAddr)
	
	dst, err := net.Dial("tcp", fallbackAddr)
	if err != nil {
		log.Printf("[Fallback] Failed to dial fallback: %v", err)
		src.Close()
		return
	}
	defer dst.Close()
	defer src.Close()
	
	// 1. 先把已经读出来的“脏数据”（导致数独解码失败的数据）发给 Nginx
	if len(badData) > 0 {
		dst.Write(badData)
	}
	
	// 2. 管道双向转发剩余流量
	go io.Copy(dst, src)
	io.Copy(src, dst)
}

// 服务端核心处理逻辑
func handleServerConnection(rawConn net.Conn) {
	// 设定一个较短的读取超时，防止 DoS
	rawConn.SetReadDeadline(time.Now().Add(HandshakeTimeout))
	
	// 我们需要“偷看”一下数据，来决定是 Fallback 还是 处理 Sudoku
	// 握手包大小 = 16 bytes (App layer) * 4 (Encoding) = 64 bytes
	// 我们尝试读取 64 字节
	
	headerBuf := make([]byte, 64)
	n, err := io.ReadFull(rawConn, headerBuf)
	
	// 恢复 Timeout
	rawConn.SetReadDeadline(time.Time{})
	
	if err != nil {
		// 连 64 字节都读不够，或者是 EOF，直接关掉或回落
		if n > 0 {
			forwardToFallback(headerBuf[:n], rawConn, config.FallbackAddr)
		} else {
			rawConn.Close()
		}
		return
	}

	// 尝试解码这 64 字节
	// 我们手动模拟 SudokuConn 的解码过程来验证
	decodedHandshake := make([]byte, 16) // 64 / 4 = 16
	
	for i := 0; i < 16; i++ {
		chunk := headerBuf[i*4 : (i+1)*4]
		var hints [4]byte
		copy(hints[:], chunk)
		
		key := packHintsToKey(hints)
		val, ok := decodeMap[key]
		if !ok {
			// 解码失败！说明这不是数独协议，可能是探测包 (HTTP GET...)
			forwardToFallback(headerBuf, rawConn, config.FallbackAddr)
			return
		}
		decodedHandshake[i] = val
	}
	
	// 解码成功，现在校验时间戳和Nonce (防重放)
	ts := int64(binary.BigEndian.Uint64(decodedHandshake[:8]))
	nonce := string(decodedHandshake[8:])
	now := time.Now().Unix()
	
	if ts < now-60 || ts > now+60 {
		log.Printf("[Security] Replay/Timeout: ts skew")
		forwardToFallback(headerBuf, rawConn, config.FallbackAddr) // 即使是格式正确但重放的包，也回落，迷惑攻击者
		return
	}
	
	cacheLock.Lock()
	if _, exists := nonceCache[nonce]; exists {
		cacheLock.Unlock()
		log.Printf("[Security] Replay Detected")
		forwardToFallback(headerBuf, rawConn, config.FallbackAddr)
		return
	}
	nonceCache[nonce] = ts
	cacheLock.Unlock()
	
	// =====================================
	// 验证通过！进入正式模式
	// =====================================
	
	// 我们已经读了 64 字节的握手包，SOCKS5 数据在后面。
	// 我们需要构造一个 SudokuConn，但这个 SudokuConn 不需要再处理握手包了。
	// 且它只需要处理后续的数据。
	
	sConn := NewSudokuConn(rawConn)
	// 把 rawConn 交给 SOCKS5 处理
	handleSocks5(sConn)
}

func handleSocks5(conn net.Conn) {
	defer conn.Close()
	
	// 标准 SOCKS5 实现 (同上个版本，略微精简)
	buf := make([]byte, 262) // Enough for header
	if _, err := io.ReadFull(conn, buf[:2]); err != nil { return }
	
	// VER, NMETHODS
	if buf[0] != 0x05 { return }
	nMethods := int(buf[1])
	if _, err := io.ReadFull(conn, buf[:nMethods]); err != nil { return }
	conn.Write([]byte{0x05, 0x00}) // No Auth
	
	// Request
	if _, err := io.ReadFull(conn, buf[:4]); err != nil { return }
	var target string
	switch buf[3] {
	case 0x01: // IPv4
		if _, err := io.ReadFull(conn, buf[:4]); err != nil { return }
		target = net.IP(buf[:4]).String()
	case 0x03: // Domain
		if _, err := io.ReadFull(conn, buf[:1]); err != nil { return }
		domainLen := int(buf[0])
		if _, err := io.ReadFull(conn, buf[:domainLen]); err != nil { return }
		target = string(buf[:domainLen])
	case 0x04: // IPv6
		if _, err := io.ReadFull(conn, buf[:16]); err != nil { return }
		target = net.IP(buf[:16]).String()
	}
	
	if _, err := io.ReadFull(conn, buf[:2]); err != nil { return }
	port := binary.BigEndian.Uint16(buf[:2])
	destAddr := fmt.Sprintf("%s:%d", target, port)
	
	dest, err := net.DialTimeout("tcp", destAddr, 5*time.Second)
	if err != nil { return }
	defer dest.Close()
	conn.Write([]byte{0x05, 0x00, 0x00, 0x01, 0,0,0,0, 0,0})
	
	go io.Copy(dest, conn)
	io.Copy(conn, dest)
}

// ==========================================
// 6. Client & Main
// ==========================================

func runClient() {
	l, err := net.Listen("tcp", fmt.Sprintf(":%d", config.LocalPort))
	if err != nil { log.Fatal(err) }
	log.Printf("Client on :%d", config.LocalPort)
	
	for {
		c, err := l.Accept()
		if err != nil { continue }
		go func(local net.Conn) {
			defer local.Close()
			remote, err := net.Dial("tcp", config.ServerAddress)
			if err != nil { return }
			defer remote.Close()
			
			sConn := NewSudokuConn(remote)
			
			// 发送握手 (Client 不需要 Fallback)
			handshake := make([]byte, 16)
			binary.BigEndian.PutUint64(handshake[:8], uint64(time.Now().Unix()))
			crand.Read(handshake[8:])
			sConn.Write(handshake)
			
			go io.Copy(sConn, local)
			io.Copy(local, sConn)
		}(c)
	}
}

func runServer() {
	l, err := net.Listen("tcp", fmt.Sprintf(":%d", config.LocalPort))
	if err != nil { log.Fatal(err) }
	log.Printf("Server on :%d (Fallback -> %s)", config.LocalPort, config.FallbackAddr)
	go cleanupCache()
	
	for {
		c, err := l.Accept()
		if err != nil { continue }
		go handleServerConnection(c)
	}
}

func main() {
	mrand.Seed(time.Now().UnixNano())
	f, _ := os.Open("config.json")
	json.NewDecoder(f).Decode(&config)
	if config.Key == "" { log.Fatal("Key needed") }
	initTables(config.Key)
	
	if config.Mode == "client" {
		runClient()
	} else {
		runServer()
	}
}
