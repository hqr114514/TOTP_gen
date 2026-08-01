#include <cstdint>
#include <cstring>
#include <ctime>
#include <iostream>
#include <stdexcept>
#include <string>
#include <vector>
#include <thread>
#include <chrono>
#include <cstdio>
#include <conio.h>
#ifdef _WIN32
#define CLEAR "cls"
#else
#define CLEAR "clear"
#endif
using std::string;
using std::vector;
const string BASE32_ALPHABET = "ABCDEFGHIJKLMNOPQRSTUVWXYZ234567";
static inline vector<uint8_t> base32_decode(const string &encoded) {
	vector<uint8_t> result;
	uint32_t buffer = 0;
	int32_t bits_left = 0;
	for(char ch : encoded) {
		if(ch == '=')
			break; // 忽略填充
		size_t pos = BASE32_ALPHABET.find(ch);
		if(pos == string::npos)
			throw std::runtime_error("Invalid Base32 character");
		buffer = (buffer << 5) | static_cast<uint32_t>(pos);
		bits_left += 5;
		if(bits_left >= 8) {
			result.push_back(
				static_cast<uint8_t>((buffer >> (bits_left - 8)) & 0xFF));
			bits_left -= 8;
		}
	}
	return result;
}
static inline uint32_t rotl32(uint32_t x, int32_t n) {
	return (x << n) | (x >> (32 - n));
}
static inline void sha1_block(uint8_t data[64], uint32_t H[5]) {
	uint32_t W[80] = { 0 };
	// 1. 将 64 字节转为 16 个 32 位大端字
	for(uint32_t t = 0; t < 16; ++t) {
		W[t] = (static_cast<uint32_t>(data[t * 4]) << 24) |
			(static_cast<uint32_t>(data[t * 4 + 1]) << 16) |
			(static_cast<uint32_t>(data[t * 4 + 2]) << 8) |
			static_cast<uint32_t>(data[t * 4 + 3]);
	}
	// 2. 扩展
	for(uint32_t t = 16; t < 80; ++t) {
		W[t] = rotl32(W[t - 3] ^ W[t - 8] ^ W[t - 14] ^ W[t - 16], 1);
	}
	// 3. 初始化工作变量
	uint32_t a = H[0], b = H[1], c = H[2], d = H[3], e = H[4];
	// 4. 80 轮主循环
	for(uint32_t t = 0; t < 80; ++t) {
		uint32_t f, k;
		if(t < 20) {
			f = (b & c) | ((~b) & d);
			k = 0x5A827999;
		}
		else if(t < 40) {
			f = b ^ c ^ d;
			k = 0x6ED9EBA1;
		}
		else if(t < 60) {
			f = (b & c) | (b & d) | (c & d);
			k = 0x8F1BBCDC;
		}
		else {
			f = b ^ c ^ d;
			k = 0xCA62C1D6;
		}
		uint32_t temp = rotl32(a, 5) + f + e + k + W[t];
		e = d;
		d = c;
		c = rotl32(b, 30);
		b = a;
		a = temp;
	}
	// 5. 加到初始哈希值
	H[0] += a;
	H[1] += b;
	H[2] += c;
	H[3] += d;
	H[4] += e;
	return;
}
// SHA‑1 主函数：输入字节数组，输出 20 字节哈希
static inline vector<uint8_t> sha1(const vector<uint8_t> &input) {
	uint32_t H[5] = { 0x67452301, 0xEFCDAB89, 0x98BADCFE, 0x10325476, 0xC3D2E1F0 };
	uint64_t total_bits = input.size() * 8;
	size_t idx = 0;
	// 处理完整 64 字节块
	while(idx + 64 <= input.size()) {
		uint8_t block[64];
		std::memcpy(block, input.data() + idx, 64);
		sha1_block(block, H);
		idx += 64;
	}
	// 处理剩余数据（含填充）
	uint8_t last[64] = { 0 };
	size_t remain = input.size() - idx;
	std::memcpy(last, input.data() + idx, remain);
	last[remain] = 0x80; // 补 1 位
	if(remain >= 56) {  // 不够放长度，需额外一块
		sha1_block(last, H);
		std::memset(last, 0, 64);
	}
	// 写入长度（大端 8 字节）
	for(uint32_t i = 0; i < 8; ++i) {
		last[56 + i] = static_cast<uint8_t>((total_bits >> (56 - 8 * i)) & 0xFF);
	}
	sha1_block(last, H);
	// 输出大端 20 字节
	vector<uint8_t> out(20);
	for(int64_t i = 0ll; i < 5ll; ++i) {
		out[i << 2] = static_cast<uint8_t>((H[i] >> 24) & 0xFF);
		out[(i << 2) + 1] = static_cast<uint8_t>((H[i] >> 16) & 0xFF);
		out[(i << 2) + 2] = static_cast<uint8_t>((H[i] >> 8) & 0xFF);
		out[(i << 2) + 3] = static_cast<uint8_t>(H[i] & 0xFF);
	}
	return out;
}
static inline vector<uint8_t> hmac_sha1(const vector<uint8_t> &key, const vector<uint8_t> &data) {
	constexpr size_t BLOCK_SIZE = 64;
	vector<uint8_t> k(key);
	if(k.size() > BLOCK_SIZE) {
		k = sha1(k); // 如果密钥超过块大小，先哈希
	}
	if(k.size() < BLOCK_SIZE) {
		k.resize(BLOCK_SIZE, 0); // 补零到块大小
	}
	// 内填充
	vector<uint8_t> inner(BLOCK_SIZE);
	for(size_t i = 0; i < BLOCK_SIZE; ++i)
		inner[i] = k[i] ^ 0x36;
	inner.insert(inner.end(), data.begin(), data.end());
	vector<uint8_t> inner_hash = sha1(inner);

	// 外填充
	vector<uint8_t> outer(BLOCK_SIZE);
	for(size_t i = 0; i < BLOCK_SIZE; ++i)
		outer[i] = k[i] ^ 0x5C;
	outer.insert(outer.end(), inner_hash.begin(), inner_hash.end());
	return sha1(outer);
}

// ========== 4. TOTP 生成 ==========
static inline uint32_t generate_totp(const string &secret_base32) {
	auto secret = base32_decode(secret_base32);
	uint64_t counter = static_cast<uint64_t>(std::time(nullptr)) / 30;
	// 转大端 8 字节
	uint8_t counter_bytes[8] = { 0 };
	for(int32_t i = 7; i >= 0; --i) {
		counter_bytes[i] = static_cast<uint8_t>(counter & 0xFF);
		counter >>= 8;
	}
	vector<uint8_t> counter_vec(counter_bytes, counter_bytes + 8);
	auto hash = hmac_sha1(secret, counter_vec);
	// 动态截断
	int offset = hash[19] & 0x0F;
	uint32_t binary = (hash[offset] & 0x7F) << 24 |
		              (hash[offset + 1] & 0xFF) << 16 |
		              (hash[offset + 2] & 0xFF) << 8 | (hash[offset + 3] & 0xFF);
	return binary % 1000000;
}
int main(int argc, char **argv) {
	const char *secret = "";
	try {
		while(true) {
			// 1. 生成当前周期的验证码
			uint32_t code = generate_totp(secret);
			int remain = 30 - (std::time(nullptr) % 30); // 当前剩余秒数（1~30）
			// 清屏并显示初始值
			system(CLEAR);
			printf("%06u\n", code);
			printf("Valid for %d seconds\n", remain);
			// 2. 内层循环：每秒刷新剩余秒数，直到新周期开始
			while(true) {
				if(_kbhit()) {
					char ch = _getch();
					if(ch == 'q' || ch == 'Q') return 0;
				}
				std::this_thread::sleep_for(std::chrono::milliseconds(1000));
				int new_remain = 30 - (std::time(nullptr) % 30);
				// 如果剩余秒数增加了（从1跳到30）或从30递减到1？只要变化就刷新
				if(new_remain != remain) {
					remain = new_remain;
					system(CLEAR);
					printf("%06u\n", code);
					printf("Valid for %d seconds\n", remain);
				}
				// 当剩余秒数变为 30 时，说明新周期开始，退出内层循环
				if(remain == 30) break;
			}
		}
	} catch(const std::exception &e) {
		std::cerr << "Error: " << e.what() << std::endl;
		return 1;
	}
	return 0;
}
