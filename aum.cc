/*
 * aum.c
 *
 *  Created on: 05/01/2017
 *      Author: ernesto
 */

#include <iostream>
#include <string>
#include <sstream>
#include <stdlib.h>
#include <set>
#include <algorithm>
#include <sys/stat.h>
#include <unordered_map>
#include <ctime>
#include <assert.h>

#include "hashmap.h"
#include "probing_hashmap.h"
#include "tombstone_hashmap.h"
#include "backshift_hashmap.h"
#include "bitmap_hashmap.h"
#include "shadow_hashmap.h"

typedef struct hash_map_entry {
	uint32_t size_key;
	uint32_t size_value;
	char *data;
} hm_entry;

typedef struct hash_map_cubeta {
	uint64_t hash;
	hm_entry *entry;
} hm_cubeta;

typedef struct hash_map_robin_hood_back_shift {
	hm_cubeta *buckets_;
	uint64_t num_buckets_;
	uint64_t num_buckets_used_;

	uint64_t probing_max_;
} hm_rr_bs_tabla;

int hash_map_robin_hood_back_shift_init(hm_rr_bs_tabla *ht, int num_cubetas) {
	ht->num_buckets_ = num_cubetas;
	ht->buckets_ = (hm_cubeta *) calloc(ht->num_buckets_, sizeof(hm_cubeta));
	/*
	 monitoring_ = new hashmap::Monitoring(num_buckets_, num_buckets_,
	 static_cast<HashMap*>(this));
	 */
	ht->num_buckets_used_ = 0;
	ht->probing_max_ = num_cubetas;
	return 0;
}

#define	FORCE_INLINE inline __attribute__((always_inline))

FORCE_INLINE uint64_t getblock64(const uint64_t * p, int i) {
	return p[i];
}

inline uint32_t rotl32(uint32_t x, int8_t r) {
	return (x << r) | (x >> (32 - r));
}

inline uint64_t rotl64(uint64_t x, int8_t r) {
	return (x << r) | (x >> (64 - r));
}

#define	ROTL32(x,y)	rotl32(x,y)
#define ROTL64(x,y)	rotl64(x,y)

#define BIG_CONSTANT(x) (x##LLU)

FORCE_INLINE uint64_t fmix64(uint64_t k) {
	k ^= k >> 33;
	k *= BIG_CONSTANT(0xff51afd7ed558ccd);
	k ^= k >> 33;
	k *= BIG_CONSTANT(0xc4ceb9fe1a85ec53);
	k ^= k >> 33;

	return k;
}

void MurmurHash3_x64_128(const void * key, const int len, const uint32_t seed,
		void * out) {
	const uint8_t * data = (const uint8_t*) key;
	const int nblocks = len / 16;

	uint64_t h1 = seed;
	uint64_t h2 = seed;

	const uint64_t c1 = BIG_CONSTANT(0x87c37b91114253d5);
	const uint64_t c2 = BIG_CONSTANT(0x4cf5ad432745937f);

	//----------
	// body

	const uint64_t * blocks = (const uint64_t *) (data);

	for (int i = 0; i < nblocks; i++) {
		uint64_t k1 = getblock64(blocks, i * 2 + 0);
		uint64_t k2 = getblock64(blocks, i * 2 + 1);

		k1 *= c1;
		k1 = ROTL64(k1, 31);
		k1 *= c2;
		h1 ^= k1;

		h1 = ROTL64(h1, 27);
		h1 += h2;
		h1 = h1 * 5 + 0x52dce729;

		k2 *= c2;
		k2 = ROTL64(k2, 33);
		k2 *= c1;
		h2 ^= k2;

		h2 = ROTL64(h2, 31);
		h2 += h1;
		h2 = h2 * 5 + 0x38495ab5;
	}

	//----------
	// tail

	const uint8_t * tail = (const uint8_t*) (data + nblocks * 16);

	uint64_t k1 = 0;
	uint64_t k2 = 0;

	switch (len & 15) {
	case 15:
		k2 ^= ((uint64_t) tail[14]) << 48;
	case 14:
		k2 ^= ((uint64_t) tail[13]) << 40;
	case 13:
		k2 ^= ((uint64_t) tail[12]) << 32;
	case 12:
		k2 ^= ((uint64_t) tail[11]) << 24;
	case 11:
		k2 ^= ((uint64_t) tail[10]) << 16;
	case 10:
		k2 ^= ((uint64_t) tail[9]) << 8;
	case 9:
		k2 ^= ((uint64_t) tail[8]) << 0;
		k2 *= c2;
		k2 = ROTL64(k2, 33);
		k2 *= c1;
		h2 ^= k2;

	case 8:
		k1 ^= ((uint64_t) tail[7]) << 56;
	case 7:
		k1 ^= ((uint64_t) tail[6]) << 48;
	case 6:
		k1 ^= ((uint64_t) tail[5]) << 40;
	case 5:
		k1 ^= ((uint64_t) tail[4]) << 32;
	case 4:
		k1 ^= ((uint64_t) tail[3]) << 24;
	case 3:
		k1 ^= ((uint64_t) tail[2]) << 16;
	case 2:
		k1 ^= ((uint64_t) tail[1]) << 8;
	case 1:
		k1 ^= ((uint64_t) tail[0]) << 0;
		k1 *= c1;
		k1 = ROTL64(k1, 31);
		k1 *= c2;
		h1 ^= k1;
	};

	//----------
	// finalization

	h1 ^= len;
	h2 ^= len;

	h1 += h2;
	h2 += h1;

	h1 = fmix64(h1);
	h2 = fmix64(h2);

	h1 += h2;
	h2 += h1;

	((uint64_t*) out)[0] = h1;
	((uint64_t*) out)[1] = h2;
}

uint64_t hash_function_caca(const char *key) {
	static char hash[16];
	static uint64_t output;
	MurmurHash3_x64_128(key, strlen(key), 0, hash);
	memcpy(&output, hash, 8);
	return output;
}

int hash_map_robin_hood_back_shift_llena_distancia_a_indice_inicio(
		hm_rr_bs_tabla *ht, uint64_t index_stored, uint64_t *distance) {
	if (ht->buckets_[index_stored].entry == NULL)
		return -1;
	uint64_t index_init = ht->buckets_[index_stored].hash % ht->num_buckets_;
	if (index_init <= index_stored) {
		*distance = index_stored - index_init;
	} else {
		*distance = index_stored + (ht->num_buckets_ - index_init);
	}
	return 0;
}

int hash_map_robin_hood_back_shift_obten(hm_rr_bs_tabla *ht, const char* key,
		char **value) {
	uint64_t hash = hash_function_caca(key);
	uint64_t index_init = hash % ht->num_buckets_;
	uint64_t probe_distance = 0;
	bool found = false;
	uint32_t i;
	for (i = 0; i < ht->probing_max_; i++) {
		uint64_t index_current = (index_init + i) % ht->num_buckets_;
		hash_map_robin_hood_back_shift_llena_distancia_a_indice_inicio(ht,
				index_current, &probe_distance);
		if (ht->buckets_[index_current].entry == NULL || i > probe_distance) {
			break;
		}

		if (strlen(key) == ht->buckets_[index_current].entry->size_key
				&& memcmp(ht->buckets_[index_current].entry->data, key,
						strlen(key)) == 0) {
			*value = ht->buckets_[index_current].entry->data + strlen(key);
			found = true;
			break;
		}
	}

	if (found)
		return 0;

	return 1;
}

int hash_map_robin_hood_back_shift_pon(hm_rr_bs_tabla *ht, const char *key,
		const char *value) {
	if (ht->num_buckets_used_ == ht->num_buckets_) {
		return 1;
	}
	ht->num_buckets_used_ += 1;

	uint64_t hash = hash_function_caca(key);
	uint64_t index_init = hash % ht->num_buckets_;

	char *data = (char *) calloc(strlen(key) + strlen(value) + 2, sizeof(char));
	memcpy(data, key, strlen(key));
	memcpy(data + strlen(key), value, strlen(value));

	hm_entry *entry = (hm_entry *) calloc(1, sizeof(hm_entry));
	entry->size_key = strlen(key);
	entry->size_value = strlen(value);
	entry->data = data;

	uint64_t index_current = index_init;
	uint64_t probe_distance = 0;
	uint64_t probe_current = 0;
	hm_entry *entry_temp = NULL;
	uint64_t hash_temp = 0;
	uint64_t i;

	for (i = 0; i < ht->probing_max_; i++) {
		index_current = (index_init + i) % ht->num_buckets_;
		if (ht->buckets_[index_current].entry == NULL) {
			ht->buckets_[index_current].entry = entry;
			ht->buckets_[index_current].hash = hash;
			break;
		} else {
			hash_map_robin_hood_back_shift_llena_distancia_a_indice_inicio(ht,
					index_current, &probe_distance);
			if (probe_current > probe_distance) {
				// Swapping the current bucket with the one to insert
				entry_temp = ht->buckets_[index_current].entry;
				hash_temp = ht->buckets_[index_current].hash;
				ht->buckets_[index_current].entry = entry;
				ht->buckets_[index_current].hash = hash;
				entry = entry_temp;
				hash = hash_temp;
				probe_current = probe_distance;
			}
		}
		probe_current++;
	}

	return 0;
}

std::string concatenate(std::string const& str, int i) {
	std::stringstream s;
	s << str << i;
	return s.str();
}

int main(int argc, char **argv) {
	bool has_error = false;
	int num_items = 67860441 / 100;
	hashmap::HashMap *hm = new hashmap::BackshiftHashMap(num_items);

	time_t rawtime;
	struct tm * timeinfo;
	char buffer[8000];

	hm->Open();
	std::string value_out("value_out");

	int num_items_reached = 0;

	std::unordered_map<std::string, std::string> caca;

	time(&rawtime);
	timeinfo = localtime(&rawtime);
	strftime(buffer, 8000, "%d-%m-%Y %I:%M:%S\n", timeinfo);
	std::string str(buffer);
	std::cout << str;

	for (int i = 0; i < num_items; i++) {
		value_out = "value_out";
		std::string key = concatenate("key", i);
		std::string value = concatenate("value", i);
		caca[key] = value;
		if (!(i % 100000)) {
			printf("caca %d\n", i);
		}
		value_out = caca[key];
		assert(!strcmp(value.c_str(), value_out.c_str()));
	}

	time(&rawtime);
	timeinfo = localtime(&rawtime);
	strftime(buffer, 8000, "%d-%m-%Y %I:%M:%S\n", timeinfo);
	std::string str1(buffer);
	std::cout << str1;

	hm_rr_bs_tabla *ht = (hm_rr_bs_tabla*) calloc(1, sizeof(hm_rr_bs_tabla));

	hash_map_robin_hood_back_shift_init(ht, num_items << 2);

	for (int i = 0; i < num_items; i++) {
		char *value_out_1 = NULL;
		std::string key = concatenate("key", i);
		std::string value = concatenate("value", i);

		hash_map_robin_hood_back_shift_pon(ht, key.c_str(), value.c_str());
		if (!(i % 100000)) {
			printf("caca c %d\n", i);
		}

		hash_map_robin_hood_back_shift_obten(ht, key.c_str(), &value_out_1);
		assert(!strcmp(value.c_str(), value_out_1));
	}

	/*
	 for (int i = 0; i < num_items; i++) {
	 value_out = "value_out";
	 std::string key = concatenate("key", i);
	 std::string value = concatenate("value", i);
	 int ret_put = hm->Put(key, value);
	 if (!(i % 1000000)) {
	 printf("caca %d\n", i);
	 }
	 hm->Get(key, &value_out);

	 if (ret_put != 0) {
	 std::cout << "Insertion stopped due to clustering at step: " << i
	 << std::endl;
	 std::cout << "Load factor: " << (double) i / num_items << std::endl;
	 num_items_reached = i;
	 break;
	 }
	 }
	 */

	time(&rawtime);
	timeinfo = localtime(&rawtime);
	strftime(buffer, 8000, "%d-%m-%Y %I:%M:%S\n", timeinfo);
	std::string str2(buffer);
	std::cout << str2;

	has_error = false;
	for (int i = 0; i < num_items_reached; i++) {
		value_out = "value_out";
		std::string key = concatenate("key", i);
		std::string value = concatenate("value", i);
		int ret_get = hm->Get(key, &value_out);
		if (ret_get != 0 || value != value_out) {
			std::cout << "Final check: error at step [" << i << "]"
					<< std::endl;
			has_error = true;
			break;
		}
	}

	if (!has_error) {
		std::cout << "Final check: OK" << std::endl;
	}

	has_error = false;
	for (int i = 0; i < num_items_reached; i++) {
		std::string key = concatenate("key", i);
		std::string value = concatenate("value", i);
		int ret_remove = hm->Remove(key);
		if (ret_remove != 0) {
			std::cout << "Remove: error at step [" << i << "]" << std::endl;
			has_error = true;
			break;
		}
		int ret_get = hm->Get(key, &value_out);
		if (ret_get == 0) {
			std::cout << "Remove: error at step [" << i
					<< "] -- can get after remove" << std::endl;
			has_error = true;
			break;
		}
	}

	if (!has_error) {
		std::cout << "Removing items: OK" << std::endl;
	}

	return 0;
}

