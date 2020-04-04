/**
 * @file cache.c
 * @brief CS{4/6}290 / ECE{4/6}100 Spring 2019 Project 1 cache simulator
 *
 * Fill in the functions to complete the cache simulator
 *
 * @author <Won Jun Lee>
 */

#include <cstdarg>
#include <cinttypes>
#include <cstdio>
#include <cstdbool>
#include <cstdlib>
#include <cstring>
#include <cmath>

#include "cache.hpp"

// Use this for printing errors while debugging your code
// Most compilers support the __LINE__ argument with a %d argument type
// Example: print_error_exit("Error: Could not allocate memory %d", __LINE__);
static inline void print_error_exit(const char *msg, ...)
{
    va_list argptr;
    va_start(argptr, msg);
    fprintf(stderr, msg, argptr);
    va_end(argptr);
    exit(EXIT_FAILURE);
}

// Define data structures and globals you might need for simulating the cache hierarchy below

// TODO
uint64_t blockNum_l1_data;
uint64_t blockNum_l1_inst;
uint64_t blockNum_l2;
uint64_t offsetBit;
uint64_t tagBit_l1_data;
uint64_t tagBit_l1_inst;
uint64_t tagBit_l2;
uint64_t indexBit_l1_data;
uint64_t indexBit_l1_inst;
uint64_t indexBit_l2;
uint64_t indexNum_l1_data;
uint64_t indexNum_l1_inst;
uint64_t indexNum_l2;
uint64_t wayNum_l1_data;
uint64_t wayNum_l1_inst;
uint64_t wayNum_l2;
uint64_t MAX = 0;
uint64_t tmp;

uint64_t count = 1;


enum write_policy wp;
enum replacement_policy rp;

typedef struct block {
    bool valid;
    bool dirty;
    uint64_t tag;
    uint64_t history;
} block;

typedef struct info {
    bool eviction;
    bool dirty;
    uint64_t tag;
    uint64_t index;
    uint64_t set;
    uint64_t addr;
    uint64_t history;
} info;

block** l1_data_cache;
block** l1_inst_cache;
block** l2_cache;

uint64_t restore_addr_l1_inst(uint64_t, uint64_t);
uint64_t restore_addr_l1_data(uint64_t, uint64_t);
uint64_t restore_addr_l2(uint64_t, uint64_t);


/**
 *Helper functions to extract tag and index from physical address
 *
 */
uint64_t find_index_l1_data(uint64_t addr) {
    uint64_t tmp = 1;
    tmp = tmp << indexBit_l1_data;
    tmp -= 1;
    addr = addr >> offsetBit;
    return addr & tmp;
}
uint64_t find_tag_l1_data(uint64_t addr) {
    return addr >> (indexBit_l1_data + offsetBit);
}
uint64_t find_index_l1_inst(uint64_t addr) {
    uint64_t tmp = 1;
    tmp = tmp << indexBit_l1_inst;
    tmp -= 1;
    addr = addr >> offsetBit;
    return addr & tmp;
}
uint64_t find_tag_l1_inst(uint64_t addr) {
    return addr >> (indexBit_l1_inst + offsetBit);
}
uint64_t find_index_l2(uint64_t addr) {
    uint64_t tmp = 1;
    tmp = tmp << indexBit_l2;
    tmp -= 1;
    addr = addr >> offsetBit;
    return addr & tmp;
}
uint64_t find_tag_l2(uint64_t addr) {
    return addr >> (indexBit_l2 + offsetBit);
}

/**
 *Helper functions to restore physical address from tag and index
 *
 */
uint64_t restore_addr_l1_inst(uint64_t tag, uint64_t index) {
    uint64_t addr = tag << (offsetBit + indexBit_l1_inst);
    addr += index << offsetBit;
    return addr;
}
uint64_t restore_addr_l1_data(uint64_t tag, uint64_t index) {
    uint64_t addr = tag << (offsetBit + indexBit_l1_data);
    addr += index << offsetBit;
    return addr;
}
uint64_t restore_addr_l2(uint64_t tag, uint64_t index) {
    uint64_t addr = tag << (offsetBit + indexBit_l2);
    addr += index << offsetBit;
    return addr;
}

//helper functions to set replacement policy
void l1inst_set_rp (uint64_t index, uint64_t set) {
    switch(rp) {
        case LRU:
        case FIFO:
            count++;
            l1_inst_cache[index][set].history = count;
            break;
        case LFU:
            l1_inst_cache[index][set].history = 1;
            break;
    }
}
void l1data_set_rp (uint64_t index, uint64_t set) {
    switch(rp) {
        case LRU:
        case FIFO:
            count++;
            l1_data_cache[index][set].history = count;
            break;
        case LFU:
            l1_data_cache[index][set].history = 1;
            break;
    }
}
void l2_set_rp (uint64_t index, uint64_t set) {
    switch(rp) {
        case LRU:
        case FIFO:
            count++;
            l2_cache[index][set].history = count;
            break;
        case LFU:
            l2_cache[index][set].history = 1;
            break;
    }
}

//helper functions to update replacement policy
void l1inst_update_rp (uint64_t index, uint64_t set) {
    switch(rp) {
        case LRU:
            count++;
            l1_inst_cache[index][set].history = count;
            break;
        case LFU:
            l1_inst_cache[index][set].history++;
            break;
        case FIFO:
            break;
    }
}
void l1data_update_rp (uint64_t index, uint64_t set) {
    switch(rp) {
        case LRU:
            count++;
            l1_data_cache[index][set].history = count;
            break;
        case LFU:
            l1_data_cache[index][set].history++;
            break;
        case FIFO:
            break;
    }
}
void l2_update_rp (uint64_t index, uint64_t set) {
    switch(rp) {
        case LRU:
            count++;
            l2_cache[index][set].history = count;
            break;
        case LFU:
            l2_cache[index][set].history++;
            break;
        case FIFO:
            break;
    }
}

/**
 * Function to check hit/miss in L1 cache
 * Returns hit/miss in boolean
 *
 */
bool l1_check(uint64_t addr, char type, struct sim_stats_t *sim_stats) {
    bool hit = false;
    uint64_t tag;
    uint64_t index;
    switch (type) {
        case 'I':
            tag = find_tag_l1_inst(addr);
            index = find_index_l1_inst(addr);
            sim_stats->l1inst_num_accesses++;
            for (uint64_t i = 0; i < wayNum_l1_inst; i++) {
                if (l1_inst_cache[index][i].valid && l1_inst_cache[index][i].tag == tag) {
                    hit = true;
                    l1inst_update_rp(index, i);
                    break;
                }
            }
            if (!hit) {
                sim_stats->l1inst_num_misses++;
            }
            break;
        case 'S':
            tag = find_tag_l1_data(addr);
            index = find_index_l1_data(addr);
            sim_stats->l1data_num_accesses++;
            sim_stats->l1data_num_accesses_stores++;
            for (uint64_t i = 0; i < wayNum_l1_data; i++) {
                if (l1_data_cache[index][i].valid && l1_data_cache[index][i].tag == tag) {
                    hit = true;
                    //set dirty if not WTWNA
                    if (wp != WTWNA) {
                        l1_data_cache[index][i].dirty = true;    
                    }
                    l1data_update_rp(index, i);
                    break;
                }
            }
            if (!hit && wp != WTWNA) {
                sim_stats->l1data_num_misses++;
                sim_stats->l1data_num_misses_stores++;
            }
            break;
        case 'L':
            tag = find_tag_l1_data(addr);
            index = find_index_l1_data(addr);
            sim_stats->l1data_num_accesses++;
            sim_stats->l1data_num_accesses_loads++;
            for (uint64_t i = 0; i < wayNum_l1_data; i++) {
                if (l1_data_cache[index][i].valid && l1_data_cache[index][i].tag == tag) {
                    hit = true;
                    l1data_update_rp(index, i);
                    break;
                }
            }
            if (!hit) {
                sim_stats->l1data_num_misses++;
                sim_stats->l1data_num_misses_loads++;
            }
            break;
    }
    return hit;
}

/**
 * Function to check hit/miss in L2 cache
 * Returns hit/miss in boolean
 *
 */
bool l2_check(uint64_t addr, char type, struct sim_stats_t *sim_stats) {
    uint64_t tag = find_tag_l2(addr);
    uint64_t index = find_index_l2(addr);
    bool hit = false;
    sim_stats->l2unified_num_accesses++;
    for (uint64_t i = 0; i < wayNum_l2;i++) {
        if (l2_cache[index][i].valid && l2_cache[index][i].tag == tag) {
            hit = true;
            l2_update_rp(index,i);
            break;
        }
    }
    switch (type) {
        case 'I':
            sim_stats->l2unified_num_accesses_insts++;
            if (!hit) {
                sim_stats->l2unified_num_misses_insts++;
                sim_stats->l2unified_num_misses++;
            }

            break;
        case 'S':
            sim_stats->l2unified_num_accesses_stores++;
            if (!hit && wp != WTWNA) {
                sim_stats->l2unified_num_misses_stores++;
                sim_stats->l2unified_num_misses++;
            }
            break;
        case 'L':
            sim_stats->l2unified_num_accesses_loads++;
            if (!hit) {
                sim_stats->l2unified_num_misses_loads++;
                sim_stats->l2unified_num_misses++;
            }
            break;
    }
    return hit;
}

void mem_access(struct sim_stats_t *sim_stats) {
    sim_stats->l2unified_num_bytes_transferred += (uint64_t)1 << offsetBit;
}
/**
 * Function to load data blocks to L1 cache
 * Returns victim's info
 *
 */
info l1_replace(uint64_t addr, char type, struct sim_stats_t *sim_stats) {
    info victim;
    victim.eviction = true;//assume there will be victim
    victim.dirty = false;
    victim.history = MAX;
    victim.tag = MAX;
    uint64_t index;
    uint64_t tag;
    switch (type) {
        case 'I':
            index = find_index_l1_inst(addr);
            tag = find_tag_l1_inst(addr);
            for (uint64_t i = 0; i < wayNum_l1_inst && victim.eviction; i++) {
                //check invalid block
                if (!l1_inst_cache[index][i].valid) {
                    //found invalid block
                    //no need for eviction
                    victim.eviction = false;
                    //set true
                    l1_inst_cache[index][i].valid = true;
                    //set tag
                    l1_inst_cache[index][i].tag = tag;
                    //set replacement policy
                    l1inst_set_rp(index,i);
                    break;
                }
                //find victim
                if(l1_inst_cache[index][i].valid && l1_inst_cache[index][i].history <= victim.history) {
                    //in case LFU tie, choose lowest tag
                    if (l1_inst_cache[index][i].history == victim.history) {
                        if (l1_inst_cache[index][i].tag < victim.tag) {
                            victim.tag = l1_inst_cache[index][i].tag;
                            victim.dirty = l1_inst_cache[index][i].dirty;
                            victim.history = l1_inst_cache[index][i].history;
                            victim.set = i;    
                        }
                    }
                    else {
                        victim.tag = l1_inst_cache[index][i].tag;
                        victim.dirty = l1_inst_cache[index][i].dirty;
                        victim.history = l1_inst_cache[index][i].history;
                        victim.set = i;
                    }
                }
            }
            if (victim.eviction) {
                sim_stats->l1inst_num_evictions++;
                l1_inst_cache[index][victim.set].tag = tag;
                l1inst_set_rp(index, victim.set);
                victim.addr = restore_addr_l1_inst(victim.tag, index);
            }
            break;

        case 'S':
        case 'L':
            index = find_index_l1_data(addr);
            tag = find_tag_l1_data(addr);
            for (uint64_t i = 0; i < wayNum_l1_data; i++) {
                //check invalid block
                if (!l1_data_cache[index][i].valid) {
                    //found invalid block
                    //set valid
                    l1_data_cache[index][i].valid = true;
                    //set tag
                    l1_data_cache[index][i].tag = tag;
                    //no need for eviction
                    victim.eviction = false;
                    victim.dirty = false;
                    //set dirty if store
                    if (type == 'S' && wp != WTWNA) {
                        l1_data_cache[index][i].dirty = true;
                    }
                    //set replacement policy
                    l1data_set_rp(index, i);
                    break;
                }
                //find victim
                if(l1_data_cache[index][i].valid && l1_data_cache[index][i].history <= victim.history) {
                    //in case LFU tie, choose lowest tag
                    if (l1_data_cache[index][i].history == victim.history) {
                        if (l1_data_cache[index][i].tag < victim.tag) {
                            victim.tag = l1_data_cache[index][i].tag;
                            victim.dirty = l1_data_cache[index][i].dirty;
                            victim.history = l1_data_cache[index][i].history;
                            victim.set = i;    
                        }
                    }
                    else {
                        victim.tag = l1_data_cache[index][i].tag;
                        victim.dirty = l1_data_cache[index][i].dirty;
                        victim.history = l1_data_cache[index][i].history;
                        victim.set = i;
                    }
                }
            }
            if (victim.eviction) {
                sim_stats->l1data_num_evictions++;
                l1_data_cache[index][victim.set].tag = tag;
                l1data_set_rp(index, victim.set);
                l1_data_cache[index][victim.set].dirty = false;
                victim.addr = restore_addr_l1_data(victim.tag, index);
                //set dirty if store
                if (type == 'S' && wp != WTWNA) {
                    l1_data_cache[index][victim.set].dirty = true;
                }
            }
            break;
    }
    return victim;
}
/**
 * Function to load data blocks to L2 cache
 * Returns victim's info
 *
 */
info l2_replace(uint64_t addr, char type, struct sim_stats_t *sim_stats, bool dirty) {
    info victim;
    victim.eviction = true;//assume there will be victim
    victim.dirty = false;
    victim.history = MAX;
    victim.tag = MAX;
    uint64_t index = find_index_l2(addr);
    uint64_t tag = find_tag_l2(addr);
    victim.index = index;

    for (uint64_t i = 0; i < wayNum_l2; i++) {
        //search invalid block
        if (!l2_cache[index][i].valid) {
            victim.eviction = false;
            l2_cache[index][i].valid = true;
            l2_cache[index][i].dirty = dirty;
            l2_cache[index][i].tag = tag;
            l2_set_rp(index,i);
            break;
        }
        //if a block already exists
        if (l2_cache[index][i].tag == tag) {
            victim.eviction = false;
            l2_cache[index][i].dirty = dirty;
            l2_update_rp(index,i);
            break;
        }
    }
    if (victim.eviction) {
        for (uint64_t i = 0; i < wayNum_l2; i++) {
            //search victim
            if (l2_cache[index][i].valid && l2_cache[index][i].history <= victim.history) {
                //check for tie
                if (l2_cache[index][i].history == victim.history) {
                    if (l2_cache[index][i].tag < victim.tag) {
                        victim.tag = l2_cache[index][i].tag;
                        victim.set = i;
                        victim.history = l2_cache[index][i].history;
                        victim.dirty = l2_cache[index][i].dirty;
                    }
                }
                else {
                    victim.tag = l2_cache[index][i].tag;
                    victim.set = i;
                    victim.history = l2_cache[index][i].history;
                    victim.dirty = l2_cache[index][i].dirty;
                }
            }
        }
        sim_stats->l2unified_num_evictions++;
        l2_cache[index][victim.set].tag = tag;
        l2_cache[index][victim.set].dirty = dirty;
        l2_set_rp(index,victim.set);
    }
    return victim;
}


/**
 * Function to initialize any data structures you might need for simulating the cache hierarchy. Use
 * the sim_conf structure for initializing dynamically allocated memory.
 *
 * @param sim_conf Pointer to simulation configuration structure
 *
 */
void sim_init(struct sim_config_t *sim_conf)
{
    // TODO
    //set MAX
    //printf("***initialize start***\n");
    MAX = ~MAX;

    //initialize variables
    offsetBit = sim_conf->l1data.b;
    indexBit_l1_data = (uint64_t) sim_conf->l1data.c - sim_conf->l1data.b - sim_conf->l1data.s;
    indexBit_l1_inst = (uint64_t) sim_conf->l1inst.c - sim_conf->l1inst.b - sim_conf->l1inst.s;
    indexBit_l2 = (uint64_t) sim_conf->l2unified.c - sim_conf->l2unified.b - sim_conf->l2unified.s;
    indexNum_l1_data = (uint64_t) pow(2, indexBit_l1_data);
    indexNum_l1_inst = (uint64_t) pow(2, indexBit_l1_inst);
    indexNum_l2 = (uint64_t) pow(2, indexBit_l2);
    wayNum_l1_data = (uint64_t) pow(2, sim_conf->l1data.s);
    wayNum_l1_inst = (uint64_t) pow(2, sim_conf->l1inst.s);
    wayNum_l2 = (uint64_t) pow(2, sim_conf->l2unified.s);
    tagBit_l1_data = 64 - indexBit_l1_data - offsetBit;
    tagBit_l1_inst = 64 - indexBit_l1_inst - offsetBit;
    tagBit_l2 = 64 - indexBit_l2 - offsetBit;
    wp = sim_conf->wp;
    rp = sim_conf->rp;
    
    //debugging
    /*
    printf("offsetBit: %llu\n", offsetBit);
    printf("indexBit_l1_data: %llu\n", indexBit_l1_data);
    printf("indexBit_l1_inst: %llu\n", indexBit_l1_inst);
    printf("indexBit_l2: %llu\n", indexBit_l2);
    printf("indexNum_l1_data: %llu\n", indexNum_l1_data);
    printf("indexNum_l1_inst: %llu\n", indexNum_l1_inst);
    printf("indexNum_l2: %llu\n", indexNum_l2);
    printf("wayNum_l1_data: %llu\n", wayNum_l1_data);
    printf("wayNum_l1_inst: %llu\n", wayNum_l1_inst);
    printf("wayNum_l2: %llu\n", wayNum_l2);
    printf("tagBit_l1_data: %llu\n", tagBit_l1_data);
    printf("tagBit_l1_inst: %llu\n", tagBit_l1_inst);
    printf("tagBit_l2: %llu\n", tagBit_l2);
    */
    //printf("max: %llu\n", MAX);
    

    //allocate space for cache

    l1_data_cache = (block**) malloc(indexNum_l1_data * sizeof(block*));
    l1_inst_cache = (block**) malloc(indexNum_l1_inst * sizeof(block*));
    l2_cache = (block**) malloc(indexNum_l2 * sizeof(block*));

    //initialize cache block variables
    //printf("***l1_data***\n");
    for (uint64_t i = 0; i < indexNum_l1_data; i++) {
        l1_data_cache[i] = (block*) malloc (wayNum_l1_data * sizeof(block));
        for (uint64_t j = 0; j < wayNum_l1_data; j++) {
            l1_data_cache[i][j].valid = false;
            l1_data_cache[i][j].dirty = false;
            l1_data_cache[i][j].history = MAX;
        }
    }
    //printf("***l1_inst***\n");
    for (uint64_t i = 0; i < indexNum_l1_inst; i++) {
        l1_inst_cache[i] = (block*) malloc (wayNum_l1_inst * sizeof(block));
        for (uint64_t j = 0; j < wayNum_l1_inst; j++) {
            l1_inst_cache[i][j].valid = false;
            l1_inst_cache[i][j].dirty = false;
            l1_inst_cache[i][j].history = MAX;
        }
    }
    //printf("***l2***\n");
    for (uint64_t i = 0; i < indexNum_l2; i++) {
        l2_cache[i] = (block*) malloc (wayNum_l2 * sizeof(block));
        for (uint64_t j = 0; j < wayNum_l2; j++) {
            l2_cache[i][j].valid = false;
            l2_cache[i][j].dirty = false;
            l2_cache[i][j].history = MAX;
        }
    }
    //printf("***initialize end***\n");
}

/**
 * Function to perform cache accesses, one access at a time. The print_debug function should be called
 * if the debug flag is true
 *
 * @param addr The address being accessed by the processor
 * @param type The type of access - Load (L), Store (S) or Instruction (I)
 * @param sim_stats Pointer to simulation statistics structure - Should be populated here
 * @param sim_conf Pointer to the simulation configuration structure - Don't modify it in this function
 */
void cache_access(uint64_t addr, char type, struct sim_stats_t *sim_stats, struct sim_config_t *sim_conf)
{
    bool l1_hit;
    bool l2_hit;
    info l1_victim;
    info l2_victim1;
    info l2_victim2;


    //check L1 cache
    l1_hit = l1_check(addr, type, sim_stats);
    if (!l1_hit || (type == 'S' && wp == WTWNA)) {
        //L1 MISS
        l2_hit = l2_check(addr, type, sim_stats);
        if ((type == 'S' && wp == WTWNA)) {
            //just write through
            mem_access(sim_stats);
        }
        else if(l2_hit) {
            //L2 HIT
            //load to L1
            l1_victim = l1_replace(addr, type, sim_stats);
            //if there is dirty vicitm from L1
            if (l1_victim.eviction && l1_victim.dirty) {
                //save dirty victim in L2
                l2_victim1 = l2_replace(l1_victim.addr, type, sim_stats, true);
                //if there is dirty victim from L2
                if (l2_victim1.eviction && l2_victim1.dirty) {
                    //write back
                    sim_stats->l2unified_num_write_backs++;
                    mem_access(sim_stats);
                }
            }
        }
        else {
            //L2 MISS
            //fetch data from main memory
            mem_access(sim_stats);
            //load to L2
            l2_victim1 = l2_replace(addr, type, sim_stats, false);
            //if there is dirty victim from L2
            if (l2_victim1.eviction && l2_victim1.dirty) {
                //write back
                sim_stats->l2unified_num_write_backs++;
                mem_access(sim_stats);
            }
            //load to L1
            l1_victim = l1_replace(addr, type, sim_stats);
            //if there is dirty victim from L1
            if (l1_victim.eviction && l1_victim.dirty) {
                //save dirty victim in L2
                //make sure not to evict just added block
                
                if (rp == LFU) {
                    //for LFU
                    //set MRU history to MAX to prevent eviction
                    //special thanks to TAs 
                    uint64_t MRU_index = find_index_l2(addr);
                    uint64_t MRU_tag = find_tag_l2(addr);
                    uint64_t MRU_way;
                    for (uint64_t i = 0; i < wayNum_l2;i++) {
                        if (l2_cache[MRU_index][i].tag == MRU_tag)
                            MRU_way = i;
                    }
                    tmp = l2_cache[MRU_index][MRU_way].history;
                    l2_cache[MRU_index][MRU_way].history = MAX;
                    l2_victim2 = l2_replace(l1_victim.addr, type, sim_stats, true);
                    l2_cache[MRU_index][MRU_way].history = tmp;
                }
                else {
                    l2_victim2 = l2_replace(l1_victim.addr, type, sim_stats, true);
                }
                
                //l2_victim2 = l2_replace(l1_victim.addr, type, sim_stats, true, true);
                //if there is dirty victim from L2
                if (l2_victim2.eviction && l2_victim2.dirty) {
                    //write back
                    sim_stats->l2unified_num_write_backs++;
                    mem_access(sim_stats);
                }
            }
        }
    }
}

/**
 * Function to cleanup dynamically allocated simulation memory, and perform any calculations
 * that might be required
 *
 * @param stats Pointer to the simulation structure - Final calculations should be performed here
 */
void sim_cleanup(struct sim_stats_t *sim_stats, struct sim_config_t *sim_conf)
{
    // TODO
    if (sim_conf->l1inst.s > MAX_S) {
        sim_stats->l1inst_hit_time = (double)L1_ACCESS_TIME[4][sim_conf->l1inst.c - 9];
    }
    else {
        sim_stats->l1inst_hit_time = (double)L1_ACCESS_TIME[sim_conf->l1inst.s][sim_conf->l1inst.c - 9];
    }
    if (sim_conf->l1data.s > MAX_S) {
        sim_stats->l1data_hit_time = (double)L1_ACCESS_TIME[4][sim_conf->l1data.c - 9];
    }
    else {
        sim_stats->l1data_hit_time = (double)L1_ACCESS_TIME[sim_conf->l1data.s][sim_conf->l1data.c - 9];
    }
    if (sim_conf->l2unified.s > MAX_S) {
        sim_stats->l2unified_hit_time = (double)L2_ACCESS_TIME[4][sim_conf->l2unified.c - 17];
    }
    else {
        sim_stats->l2unified_hit_time = (double)L2_ACCESS_TIME[sim_conf->l2unified.s][sim_conf->l2unified.c - 17];
    }

    sim_stats->l1inst_miss_rate = (double)sim_stats->l1inst_num_misses / (double)sim_stats->l1inst_num_accesses;
    sim_stats->l1data_miss_rate = (double)sim_stats->l1data_num_misses / (double)sim_stats->l1data_num_accesses;
    sim_stats->l2unified_miss_rate = (double)sim_stats->l2unified_num_misses / (double)sim_stats->l2unified_num_accesses;
    sim_stats->l2unified_miss_penalty = 80.0;
    

    sim_stats->l2unified_AAT = sim_stats->l2unified_hit_time + sim_stats->l2unified_miss_rate * sim_stats->l2unified_miss_penalty;
    sim_stats->l1inst_miss_penalty = sim_stats->l2unified_AAT;
    sim_stats->l1data_miss_penalty = sim_stats->l1inst_miss_penalty;
    sim_stats->l1inst_AAT = sim_stats->l1inst_hit_time + sim_stats->l1inst_miss_rate * sim_stats->l2unified_AAT;
    sim_stats->l1data_AAT = sim_stats->l1data_hit_time + sim_stats->l1data_miss_rate * sim_stats->l2unified_AAT;
    sim_stats->inst_avg_access_time = sim_stats->l1inst_AAT;
    sim_stats->data_avg_access_time = sim_stats->l1data_AAT;
    sim_stats->avg_access_time = (sim_stats->l1inst_AAT * sim_stats->l1inst_num_accesses + sim_stats->l1data_AAT * sim_stats->l1data_num_accesses) / (sim_stats->l1data_num_accesses + sim_stats->l1inst_num_accesses);
    //free memory
    for (uint64_t i = 0; i < indexNum_l1_data; i++)
        free(l1_data_cache[i]);
    free(l1_data_cache);
    for (uint64_t i = 0; i < indexNum_l1_inst; i++)
        free(l1_inst_cache[i]);
    free(l1_inst_cache);
    for (uint64_t i = 0; i < indexNum_l2; i++)
        free(l2_cache[i]);
    free(l2_cache);
}
