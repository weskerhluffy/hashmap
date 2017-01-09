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

typedef int tipo_dato;
typedef unsigned int natural;
typedef long long entero_largo;
typedef unsigned long long bitch_vector;

#define assert_timeout(condition) assert(condition);

#if 1

typedef unsigned int khint32_t;

typedef unsigned long long khint64_t;
typedef khint32_t khint_t;
typedef khint_t khiter_t;
static const double __ac_HASH_UPPER = 0.77;
static inline khint_t __ac_X31_hash_string(const char *s) {
	khint_t h = (khint_t) *s;
	if (h)
		for (++s; *s; ++s)
			h = (h << 5) - h + (khint_t) *s;
	return h;
}
static inline khint_t __ac_Wang_hash(khint_t key) {
	key += ~(key << 15);
	key ^= (key >> 10);
	key += (key << 3);
	key ^= (key >> 6);
	key += ~(key << 11);
	key ^= (key >> 16);
	return key;
}
typedef const char *kh_cstr_t;
typedef struct kh_caca_s {
	khint_t n_buckets, size, n_occupied, upper_bound;
	khint32_t *flags;
	khint64_t *keys;
	long long *vals;
	natural tam_inicial;
} kh_caca_t;

#define kh_key(h, x) ((h)->keys[x])
#define kh_val(h, x) ((h)->vals[x])
#define kh_value(h, x) ((h)->vals[x])
#define kh_begin(h) (khint_t)(0)
#define kh_end(h) ((h)->n_buckets)
#define kh_size(h) ((h)->size)
#define kh_exist(h, x) (!__ac_iseither((h)->flags, (x)))

#define __ac_isempty(flag, i) ((flag[i>>4]>>((i&0xfU)<<1))&2)
#define __ac_isdel(flag, i) ((flag[i>>4]>>((i&0xfU)<<1))&1)
#define __ac_iseither(flag, i) ((flag[i>>4]>>((i&0xfU)<<1))&3)
#define __ac_set_isdel_false(flag, i) (flag[i>>4]&=~(1ul<<((i&0xfU)<<1)))
#define __ac_set_isempty_false(flag, i) (flag[i>>4]&=~(2ul<<((i&0xfU)<<1)))
#define __ac_set_isboth_false(flag, i) (flag[i>>4]&=~(3ul<<((i&0xfU)<<1)))
#define __ac_set_isdel_true(flag, i) (flag[i>>4]|=1ul<<((i&0xfU)<<1))
#define __ac_fsize(m) ((m) < 16? 1 : (m)>>4)

static inline __attribute__ ((__unused__)) int kh_resize_caca(kh_caca_t *h,
		khint_t new_n_buckets);

static inline __attribute__ ((__unused__)) kh_caca_t *kh_init_caca(
		natural tam_inicial) {
	natural tam_inicial_redondeado = 0;
	natural max_profundidad = 0;
	kh_caca_t *mierda = (kh_caca_t*) calloc(1, sizeof(kh_caca_t));
	assert_timeout(mierda);
	while ((tam_inicial >> max_profundidad)) {
		max_profundidad++;
	}
	tam_inicial_redondeado = (1 << max_profundidad);
	mierda->tam_inicial = tam_inicial_redondeado << 1;
	assert_timeout(kh_resize_caca(mierda, mierda->n_buckets + 1) >= 0);

	return mierda;
}
static inline __attribute__ ((__unused__)) void kh_destroy_caca(kh_caca_t *h) {
	if (h) {
		free((void *) h->keys);
		free(h->flags);
		free((void *) h->vals);
		free(h);
	}
}

static inline __attribute__ ((__unused__)) khint_t kh_get_caca(
		const kh_caca_t *h, khint64_t key) {
	khint_t k, i, last, mask, step = 0;
	mask = h->n_buckets - 1;
	k = (khint32_t) ((key) >> 33 ^ (key) ^ (key) << 11);
	i = k & mask;
	last = i;
	khint32_t bandera_caca;
	khint32_t *flags = h->flags;
	khint64_t *keys = h->keys;
	while (!((bandera_caca = (flags[i >> 4] >> ((i & 0xfU) << 1))) & 2)
			&& ((bandera_caca & 1) || !((keys[i]) == (key)))) {
		i = (i + (++step)) & mask;
		if (i == last)
			return h->n_buckets;
	}
	return ((flags[i >> 4] >> ((i & 0xfU) << 1)) & 3) ? h->n_buckets : i;
}

static inline __attribute__ ((__unused__)) int kh_resize_caca(kh_caca_t *h,
		khint_t new_n_buckets) {
	khint32_t *new_flags = 0;
	khint_t j = 1;
	{
		(--(new_n_buckets), (new_n_buckets) |= (new_n_buckets) >> 1, (new_n_buckets) |=
				(new_n_buckets) >> 2, (new_n_buckets) |= (new_n_buckets) >> 4, (new_n_buckets) |=
				(new_n_buckets) >> 8, (new_n_buckets) |= (new_n_buckets) >> 16, ++(new_n_buckets));
		if (new_n_buckets < 4)
			new_n_buckets = 4;
		if (h->size >= (khint_t) (new_n_buckets * __ac_HASH_UPPER + 0.5))
			j = 0;
		else {
			new_flags = (khint32_t*) malloc(
					((new_n_buckets) < 16 ? 1 : (new_n_buckets) >> 4)
							* sizeof(khint32_t));
			if (!new_flags)
				return -1;
			__builtin___memset_chk(new_flags, 0xaa,
					((new_n_buckets) < 16 ? 1 : (new_n_buckets) >> 4)
							* sizeof(khint32_t),
					__builtin_object_size(new_flags, 0));
			if (h->n_buckets < new_n_buckets) {
				khint64_t *new_keys = (khint64_t*) realloc((void *) h->keys,
						new_n_buckets * sizeof(khint64_t));
				if (!new_keys) {
					free(new_flags);
					return -1;
				}
				h->keys = new_keys;
				if (1) {
					long long *new_vals = (long long*) realloc((void *) h->vals,
							new_n_buckets * sizeof(long long));
					if (!new_vals) {
						free(new_flags);
						return -1;
					}
					h->vals = new_vals;
				}
			}
		}
	}
	if (j) {
		for (j = 0; j != h->n_buckets; ++j) {
			if (((h->flags[j >> 4] >> ((j & 0xfU) << 1)) & 3) == 0) {
				khint64_t key = h->keys[j];
				long long val;
				khint_t new_mask;
				new_mask = new_n_buckets - 1;
				if (1)
					val = h->vals[j];
				(h->flags[j >> 4] |= 1ul << ((j & 0xfU) << 1));
				while (1) {
					khint_t k, i, step = 0;
					k = (khint32_t) ((key) >> 33 ^ (key) ^ (key) << 11);
					i = k & new_mask;
					while (!((new_flags[i >> 4] >> ((i & 0xfU) << 1)) & 2))
						i = (i + (++step)) & new_mask;
					(new_flags[i >> 4] &= ~(2ul << ((i & 0xfU) << 1)));
					if (i < h->n_buckets
							&& ((h->flags[i >> 4] >> ((i & 0xfU) << 1)) & 3)
									== 0) {
						{
							khint64_t tmp = h->keys[i];
							h->keys[i] = key;
							key = tmp;
						}
						if (1) {
							long long tmp = h->vals[i];
							h->vals[i] = val;
							val = tmp;
						}
						(h->flags[i >> 4] |= 1ul << ((i & 0xfU) << 1));
					} else {
						h->keys[i] = key;
						if (1)
							h->vals[i] = val;
						break;
					}
				}
			}
		}
		if (h->n_buckets > new_n_buckets) {
			h->keys = (khint64_t*) realloc((void *) h->keys,
					new_n_buckets * sizeof(khint64_t));
			if (1)
				h->vals = (long long*) realloc((void *) h->vals,
						new_n_buckets * sizeof(long long));
		}
		free(h->flags);
		h->flags = new_flags;
		h->n_buckets = new_n_buckets;
		h->n_occupied = h->size;
		h->upper_bound = (khint_t) (h->n_buckets * __ac_HASH_UPPER + 0.5);
	}
	return 0;
}

/*! @function
 @abstract     Insert a key to the hash table.
 @param  name  Name of the hash table [symbol]
 @param  h     Pointer to the hash table [khash_t(name)*]
 @param  k     Key [type of keys]
 @param  r     Extra return code: -1 if the operation failed;
 0 if the key is present in the hash table;
 1 if the bucket is empty (never used); 2 if the element in
 the bucket has been deleted [int*]
 @return       Iterator to the inserted element [khint_t]
 */
static inline __attribute__ ((__unused__)) khint_t kh_put_caca(kh_caca_t *h,
		khint64_t key, int *ret) {
	khint_t x;
	if (h->n_occupied >= h->upper_bound) {
		if (kh_resize_caca(h, h->n_buckets + 1) < 0) {
			*ret = -1;
			return h->n_buckets;
		}
	}
	khint_t k, i, site, last, mask = h->n_buckets - 1, step = 0;
	x = site = h->n_buckets;
	k = (khint32_t) ((key) >> 33 ^ (key) ^ (key) << 11);
	i = k & mask;
	khint32_t *flags = h->flags;
	khint64_t *keys = h->keys;
	khint32_t banderilla_loca = (flags[i >> 4] >> ((i & 0xfU) << 1));
	if ((banderilla_loca & 2))
		x = i;
	else {
		last = i;
		while (!((banderilla_loca = flags[i >> 4] >> ((i & 0xfU) << 1)) & 2)
				&& ((banderilla_loca & 1) || !((keys[i]) == (key)))) {
			if ((banderilla_loca & 1))
				site = i;
			i = (i + (++step)) & mask;
			if (i == last) {
				x = site;
				break;
			}
		}
		if (x == h->n_buckets) {
			if ((banderilla_loca & 2) && site != h->n_buckets)
				x = site;
			else
				x = i;
		}
	}

	banderilla_loca = (flags[x >> 4] >> ((x & 0xfU) << 1));
	if ((banderilla_loca & 2)) {
		keys[x] = key;
		(flags[x >> 4] &= ~(3ul << ((x & 0xfU) << 1)));
		++h->size;
		++h->n_occupied;
		*ret = 1;
	} else if ((banderilla_loca & 1)) {
		keys[x] = key;
		(flags[x >> 4] &= ~(3ul << ((x & 0xfU) << 1)));
		++h->size;
		*ret = 2;
	} else
		*ret = 0;
	return x;
}
static inline __attribute__ ((__unused__)) void kh_del_caca(kh_caca_t *h,
		khint_t x) {
	if (x != h->n_buckets && !((h->flags[x >> 4] >> ((x & 0xfU) << 1)) & 3)) {
		(h->flags[x >> 4] |= 1ul << ((x & 0xfU) << 1));
		--h->size;
	}
}

char *kh_shit_dumpear(kh_caca_t *h, char *buf) {
	*buf = '\0';
#ifndef ONLINE_JUDGE
	for (int k = kh_begin(h); k != kh_end(h); ++k) {
		if (kh_exist(h, k)) {
			char *buf_tmp = (char[1000] ) { 0 };
			sprintf(buf_tmp, "%u -> %u\n", (natural) kh_key(h,k),
			(natural)(kh_val(h,k)));
			strcat(buf, buf_tmp);
		}
	}
#endif
	return buf;
}

#endif

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
	int factor_redux = 100;
	int num_items = 67860441 / factor_redux;
	int muestre = 10000000 / factor_redux;

	long value_out = 0;

	int num_items_reached = 0;



	hm_rr_bs_tabla *ht = (hm_rr_bs_tabla*) calloc(1, sizeof(hm_rr_bs_tabla));

	hash_map_robin_hood_back_shift_init(ht, num_items << 2);

	kh_caca_t *mierda = kh_init_caca(num_items << 2);

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

	for (int i = 0; i < num_items; i++) {
		value_out = 0;
		long key = i;
		long value = i;
		khiter_t iter;

		int ret_put = 0;
		iter = kh_put_caca(mierda, key, &ret_put);
		kh_val(mierda,iter)=value;
		if (!(i % muestre)) {
			printf("caca c ant %d\n", i);
		}

		hash_map_robin_hood_back_shift_obten(ht, key, &value_out);
		iter = kh_get_caca(mierda, key);
		value_out = kh_val(mierda,iter);
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

	for (int i = 0; i < num_items_reached; i++) {
		value_out = 0;
		long key = i;
		long value = i;
		khiter_t iter;

		int ret_get;
		iter = kh_get_caca(mierda, key);
		if (!(i % muestre)) {
			printf("caca obten nomas c ant %d\n", i);
		}
		value_out = kh_val(mierda,iter);
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

	for (int i = 0; i < num_items_reached; i++) {
		long key = i;
		kh_del_caca(mierda, key);
		if (!(i % muestre)) {
			printf("caca borra c ant %d\n", i);
		}
//		assert(hash_map_robin_hood_back_shift_obten(ht, key, &value_out));
	}

	solo_rencor();

	if (!has_error) {
		std::cout << "Removing items: OK" << std::endl;
	}

	return 0;
}

