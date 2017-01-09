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
	long llave;
	long valor;
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

static inline int hash_map_robin_hood_back_shift_llena_distancia_a_indice_inicio(
		hm_rr_bs_tabla *ht, uint64_t index_stored, uint64_t *distance) {
	hm_cubeta cubeta = ht->buckets_[index_stored];

	*distance = 0;

	if (cubeta.entry == NULL)
		return -1;

	uint64_t num_cubetas = ht->num_buckets_;

	uint64_t index_init = cubeta.hash % num_cubetas;
	if (index_init <= index_stored) {
		*distance = index_stored - index_init;
	} else {
		*distance = index_stored + (num_cubetas - index_init);
	}
	return 0;
}

int hash_map_robin_hood_back_shift_obten(hm_rr_bs_tabla *ht, const long key,
		long *value) {
	uint64_t num_cubetas = ht->num_buckets_;
	uint64_t prob_max = ht->probing_max_;

//	uint64_t hash = hash_function_caca(key);
	uint64_t hash = key % num_cubetas;
	uint64_t index_init = hash;
	uint64_t probe_distance = 0;
	bool found = false;
	uint32_t i;
	for (i = 0; i < prob_max; i++) {
		uint64_t index_current = (index_init + i) % num_cubetas;
		hm_entry *entrada = ht->buckets_[index_current].entry;

		hash_map_robin_hood_back_shift_llena_distancia_a_indice_inicio(ht,
				index_current, &probe_distance);
		if (entrada == NULL || i > probe_distance) {
			break;
		}

		if (entrada->llave == key) {
			*value = entrada->valor;
			found = true;
			break;
		}
	}

	if (found)
		return 0;

	return 1;
}

int hash_map_robin_hood_back_shift_pon(hm_rr_bs_tabla *ht, long key,
		long value) {

	uint64_t num_cubetas = ht->num_buckets_;
	uint64_t prob_max = ht->probing_max_;
	hm_cubeta *cubetas = ht->buckets_;

	if (ht->num_buckets_used_ == num_cubetas) {
		return 1;
	}
	ht->num_buckets_used_ += 1;

//	uint64_t hash = hash_function_caca(key);
	uint64_t hash = key % num_cubetas;
	uint64_t index_init = hash;

	hm_entry *entry = (hm_entry *) calloc(1, sizeof(hm_entry));
	entry->llave = key;
	entry->valor = value;

	uint64_t index_current = index_init;
	uint64_t probe_current = 0;
	uint64_t probe_distance;
	hm_entry *entry_temp;
	uint64_t hash_temp;
	uint64_t i;

	for (i = 0; i < prob_max; i++) {
		index_current = (index_init + i) % num_cubetas;
		hm_cubeta *cubeta = cubetas + index_current;

		if (cubeta->entry == NULL) {
			cubeta->entry = entry;
			cubeta->hash = hash;
			break;
		} else {
			hash_map_robin_hood_back_shift_llena_distancia_a_indice_inicio(ht,
					index_current, &probe_distance);
			if (probe_current > probe_distance) {
				// Swapping the current bucket with the one to insert
				entry_temp = cubeta->entry;
				hash_temp = cubeta->hash;
				cubeta->entry = entry;
				cubeta->hash = hash;
				entry = entry_temp;
				hash = hash_temp;
				probe_current = probe_distance;
			}
		}
		probe_current++;
	}

	return 0;
}

int hash_map_robin_hood_back_shift_borra(hm_rr_bs_tabla *ht, const long key) {
	uint64_t num_cubetas = ht->num_buckets_;
	uint64_t prob_max = ht->probing_max_;

	uint64_t hash = key % num_cubetas;
	uint64_t index_init = hash;
	bool found = false;
	uint64_t index_current = 0;
	uint64_t probe_distance = 0;
	hm_entry *entrada = NULL;

	for (uint64_t i = 0; i < num_cubetas; i++) {
		index_current = (index_init + i) % num_cubetas;
		entrada = ht->buckets_[index_current].entry;

		hash_map_robin_hood_back_shift_llena_distancia_a_indice_inicio(ht,
				index_current, &probe_distance);
		if (entrada == NULL || i > probe_distance) {
			break;
		}

		if (entrada->llave == key) {
			found = true;
			break;
		}
	}

	if (found) {
		free(entrada);

		uint64_t i = 1;
		uint64_t index_previous = 0, index_swap = 0;

		for (i = 1; i < num_cubetas; i++) {
			index_previous = (index_current + i - 1) % num_cubetas;
			index_swap = (index_current + i) % num_cubetas;

			hm_cubeta *cubeta_swap = ht->buckets_ + index_swap;
			hm_cubeta *cubeta_previous = ht->buckets_ + index_previous;

			if (cubeta_swap->entry == NULL) {
				cubeta_previous->entry = NULL;
				break;
			}
			uint64_t distance;
			if (hash_map_robin_hood_back_shift_llena_distancia_a_indice_inicio(
					ht, index_swap, &distance) != 0) {
				fprintf(stderr, "Error in FillDistanceToInitIndex()");
			}
			if (!distance) {
				cubeta_previous->entry = NULL;
				break;
			}
			cubeta_previous->entry = cubeta_swap->entry;
			cubeta_previous->hash = cubeta_swap->hash;
		}
		return 0;
	}

	return 1;
}

std::string concatenate(std::string const& str, int i) {
	std::stringstream s;
	s << str << i;
	return s.str();
}

void solo_rencor() {
	time_t rawtime;
	struct tm * timeinfo;
	char buffer[8000];

	time(&rawtime);
	timeinfo = localtime(&rawtime);
	strftime(buffer, 8000, "%d-%m-%Y %I:%M:%S\n", timeinfo);
	std::string str(buffer);
	std::cout << str;

}

int main(int argc, char **argv) {
	bool has_error = false;
	int num_items = 67860441 / 100;
	int muestre = 100000;

	long value_out = 0;

	int num_items_reached = 0;

	std::unordered_map<long, long> caca;

	solo_rencor();

	for (int i = 0; i < num_items; i++) {
		value_out = 0;
		long key = i;
		long value = i;
		caca[key] = value;
		if (!(i % muestre)) {
			printf("caca %d\n", i);
		}
		value_out = caca[key];
		assert(value == value_out);
	}

	solo_rencor();

	hm_rr_bs_tabla *ht = (hm_rr_bs_tabla*) calloc(1, sizeof(hm_rr_bs_tabla));

	hash_map_robin_hood_back_shift_init(ht, num_items << 2);

	for (int i = 0; i < num_items; i++) {
		value_out = 0;
		long key = i;
		long value = i;

		int ret_put = hash_map_robin_hood_back_shift_pon(ht, key, value);
		if (!(i % muestre)) {
			printf("caca c %d\n", i);
		}

		hash_map_robin_hood_back_shift_obten(ht, key, &value_out);
		if (ret_put != 0) {
			std::cout << "Insertion stopped due to clustering at step: " << i
					<< std::endl;
			std::cout << "Load factor: " << (double) i / num_items << std::endl;
			num_items_reached = i;
			break;
		}
		assert(value == value_out);
	}
	assert(!num_items_reached);
	if (!num_items_reached) {
		num_items_reached = num_items;
	}

	solo_rencor();

	for (int i = 0; i < num_items_reached; i++) {
		value_out = 0;
		long key = i;
		long value = i;

		value_out = caca[key];
		if (!(i % muestre)) {
			printf("caca obten nomas %d\n", i);
		}
		assert(value == value_out);
	}

	solo_rencor();

	has_error = false;
	for (int i = 0; i < num_items_reached; i++) {
		value_out = 0;
		long key = i;
		long value = i;

		int ret_get = hash_map_robin_hood_back_shift_obten(ht, key, &value_out);
		if (!(i % muestre)) {
			printf("caca obten nomas c %d\n", i);
		}
		if (ret_get != 0 || value != value_out) {
			std::cout << "Final check: error at step [" << i << "]"
					<< std::endl;
			has_error = true;
			break;
		}
	}

	solo_rencor();

	if (!has_error) {
		std::cout << "Final check: OK" << std::endl;
	}

	has_error = false;

	for (int i = 0; i < num_items_reached; i++) {
		long key = i;

		caca.erase(key);
		if (!(i % muestre)) {
			printf("caca borra %d\n", i);
		}
		assert(caca.find(key) == caca.end());
	}

	solo_rencor();
	has_error = false;

	for (int i = 0; i < num_items_reached; i++) {
		long key = i;
		hash_map_robin_hood_back_shift_borra(ht, key);
		if (!(i % muestre)) {
			printf("caca borra c %d\n", i);
		}
		assert(hash_map_robin_hood_back_shift_obten(ht, key, &value_out));
	}

	solo_rencor();

	if (!has_error) {
		std::cout << "Removing items: OK" << std::endl;
	}

	return 0;
}

