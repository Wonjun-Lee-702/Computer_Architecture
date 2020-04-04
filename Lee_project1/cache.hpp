/**
 * @file cache.h
 * @brief Header for the CS{4/6}290 / ECE{4/6}100 Spring 2019 Project 1 framework
 *
 * Header file for the cache simulator containing a bunch of struct definitions,
 * constants, defaults, etc. Don't modify any code in this file!
 *
 * @author Anirudh Jain
 */

#ifndef CACHE_H
#define CACHE_H


#include <cstdarg>
#include <cinttypes>
#include <cstdio>
#include <cstdbool>
#include <cstdlib>
#include <cstring>


// Constants
enum write_policy {WBWA = 1, WTWNA = 2};
enum replacement_policy {LRU = 1, LFU = 2, FIFO = 3};

static const char *const write_policy_map[] = {"NA", "WBWA", "WTWNA"};
static const char *const replacement_policy_map[] = {"NA", "LRU", "LFU", "FIFO"};

static const char LOAD = 'L';
static const char STORE = 'S';
static const char INST = 'I';
static const uint8_t TRUE = 1;
static const uint8_t FALSE = 0;

// Access time constants
static const uint16_t MAX_S = 3;
static const uint64_t MIN_L1_C = 9;
static const uint64_t MAX_L1_C = 15;
static const double L1_ACCESS_TIME[5][7] = {
    {1, 1, 2, 2, 2, 2, 2},  // DM
    {1, 2, 2, 2, 2, 3, 3},  // 2W
    {2, 2, 2, 3, 3, 3, 4},  // 4W
    {2, 3, 3, 3, 3 ,3, 4},  // 8W
    {4, 4, 4, 5, 5, 6, 6}   // FA
};

static const uint64_t MIN_L2_C = 17;
static const uint64_t MAX_L2_C = 21;
static const double L2_ACCESS_TIME[5][5] = {
    {7, 8, 8, 9, 9},        // DM
    {7, 8, 9, 10, 11},      // 2W
    {8, 9, 10, 11, 12},     // 4W
    {10, 12, 13, 14, 15},   // 8W
    {15, 16, 18, 20, 22}    // FA
};

// Struct for storing per Cache parameters
struct cache_config_t {
    uint64_t c;
    uint64_t b; // We assume that both the caches have the exact same block size
    uint64_t s;
};

// Struct for tracking the simulation parameters
struct sim_config_t {
    struct cache_config_t l1data;
    struct cache_config_t l1inst;
    struct cache_config_t l2unified;
    enum write_policy wp; // write policy
    enum replacement_policy rp; // replacement policy
};

// Struct for keeping track of simulation statistics
struct sim_stats_t {

    // L1 Instruction Cache statistics
    uint64_t l1inst_num_accesses;           // Total L1 Inst Accesses
    uint64_t l1inst_num_misses;             // Total L1 Inst Misses
    uint64_t l1inst_num_evictions;          // Total blocks evicted from L1-Instruction cache

    double l1inst_hit_time;                 // L1 Inst Hit Time
    double l1inst_miss_penalty;             // L1 Inst Miss Penalty
    double l1inst_miss_rate;                // L1 Inst Miss Rate
    double l1inst_AAT;                      // L1 Inst Average Access Time

    // L1 Data Cache statistics
    uint64_t l1data_num_accesses;           // Total L1 Data Accesses
    uint64_t l1data_num_accesses_loads;     // L1 Data Accesses which are Loads
    uint64_t l1data_num_accesses_stores;    // L1 Data Accesses which are Stores
    uint64_t l1data_num_misses;             // Total L1 Data Misses
    uint64_t l1data_num_misses_loads;       // L1 Data Misses which are Loads
    uint64_t l1data_num_misses_stores;      // L1 Data Misses which are Stores
    uint64_t l1data_num_evictions;          // Total blocks evicted from L1-Data cache

    double l1data_hit_time;                 // L1 Data Hit Time
    double l1data_miss_penalty;             // L1 Data Miss Penalty
    double l1data_miss_rate;                // L1 Data Miss Rate
    double l1data_AAT;                      // L1 Data Average Access Time

    // Unified L2 Cache statistics
    uint64_t l2unified_num_accesses;        // Total L2 Accesses
    uint64_t l2unified_num_accesses_insts;  // L2 Accesses which are instructions
    uint64_t l2unified_num_accesses_loads;  // L2 Accesses which are Loads
    uint64_t l2unified_num_accesses_stores; // L2 Accesses which are Stores
    uint64_t l2unified_num_misses;          // Total L2 Misses
    uint64_t l2unified_num_misses_insts;    // L2 Misses that are instructions
    uint64_t l2unified_num_misses_loads;    // L2 Misses that are Loads
    uint64_t l2unified_num_misses_stores;   // L2 Misses that are Stores
    uint64_t l2unified_num_evictions;       // Total blocks evicted from the L2 cache
    uint64_t l2unified_num_write_backs;     // Total write backs from L2 to Main Memory
    uint64_t l2unified_num_bytes_transferred; // Total bytes written from L2 to Main Memory

    double l2unified_hit_time;              // L2 Hit Time
    double l2unified_miss_penalty;          // L2 Miss Penalty
    double l2unified_miss_rate;             // L2 Miss Rate
    double l2unified_AAT;                   // L2 Average Access Time

    // Performance Statistics
    double inst_avg_access_time;            // Average Access Time per access for Instructions
    double data_avg_access_time;            // Average Access Time per access for Data (Loads and Stores)
    double avg_access_time;                 // Average Access Time per access - A weighed average of instruction and data accesses
};

// Visible functions
void sim_init(struct sim_config_t *sim_conf);
void cache_access(uint64_t addr, char type, struct sim_stats_t *sim_stats, struct sim_config_t *sim_conf);
void sim_cleanup(struct sim_stats_t *sim_stats, struct sim_config_t *sim_conf);

#endif // CACHE_H
