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

#include "hashmap.h"
#include "probing_hashmap.h"
#include "tombstone_hashmap.h"
#include "backshift_hashmap.h"
#include "bitmap_hashmap.h"
#include "shadow_hashmap.h"

std::string concatenate(std::string const& str, int i) {
	std::stringstream s;
	s << str << i;
	return s.str();
}

int main(int argc, char **argv) {
	bool has_error = false;
	int num_items = 67860441/1000;
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
		if (!(i % 1000000)) {
			printf("caca %d\n", i);
		}
//		value_out = caca[key];

	}

	time(&rawtime);
	timeinfo = localtime(&rawtime);
	strftime(buffer, 8000, "%d-%m-%Y %I:%M:%S\n", timeinfo);
	std::string str1(buffer);
	std::cout << str1;

	for (int i = 0; i < num_items; i++) {
		value_out = "value_out";
		std::string key = concatenate("key", i);
		std::string value = concatenate("value", i);
		int ret_put = hm->Put(key, value);
		if (!(i % 1000000)) {
			printf("caca %d\n", i);
		}
		/*
		hm->Get(key, &value_out);

		if (ret_put != 0) {
			std::cout << "Insertion stopped due to clustering at step: " << i
					<< std::endl;
			std::cout << "Load factor: " << (double) i / num_items << std::endl;
			num_items_reached = i;
			break;
		}
		*/
	}

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

