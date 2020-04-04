/**
 * @file cache_driver.c
 * @brief Trace reader and driver for the CS{4/6}290 / ECE{4/6}100 Spring 2020 Project 1
 *
 * Project 1 trace reader and driver. Don't modify any code in this file!
 *
 * @author Anirudh Jain
 */

#include <getopt.h>
#include <unistd.h>


#include <cstdarg>
#include <cinttypes>
#include <cstdio>
#include <cstdbool>
#include <cstdlib>
#include <cstring>
#include <string>

#include "util/jsmn.h"
#include "cache.hpp"


// Print error usage
static void print_err_usage(std::string err)
{
    fprintf(stderr, "%s\n", err.c_str());

    fprintf(stderr, "./cachesim -c <configuration file> -i <trace file>\n");
    fprintf(stderr, "Look at default.conf for example configuration file\n");

    exit(EXIT_FAILURE);
}

static inline void print_error_exit(const char *msg, ...)
{
    va_list argptr;
    va_start(argptr, msg);
    fprintf(stderr, msg, argptr);
    va_end(argptr);
    exit(EXIT_FAILURE);
}

// Function to print the run configuration
static void print_sim_config(struct sim_config_t *sim_conf)
{
    fprintf(stdout, "SIMULATION CONFIGURATION\n");
    fprintf(stdout, "L1 Instruction Cache:  (C=%" PRIu64 ", B=%" PRIu64 ", S=%" PRIu64 ")\n", sim_conf->l1inst.c, sim_conf->l1inst.b, sim_conf->l1inst.s);
    fprintf(stdout, "L1 Data Cache:         (C=%" PRIu64 ", B=%" PRIu64 ", S=%" PRIu64 ")\n", sim_conf->l1data.c, sim_conf->l1data.b, sim_conf->l1data.s);
    fprintf(stdout, "L2 Unified Cache:      (C=%" PRIu64 ", B=%" PRIu64 ", S=%" PRIu64 ")\n", sim_conf->l2unified.c, sim_conf->l2unified.b, sim_conf->l2unified.s);
    fprintf(stdout, "Replacement Policy:    %s\n", replacement_policy_map[sim_conf->rp]);
    fprintf(stdout, "Write Policy:          %s\n", write_policy_map[sim_conf->wp]);
}

static void print_sim_output(struct sim_stats_t *sim_stats)
{
    printf("\nSIMULATION OUTPUT\n");

    // L1 Instruction Stats
    printf("L1 Instruction Accesses             %" PRIu64 "\n", sim_stats->l1inst_num_accesses);
    printf("L1 Instruction Misses               %" PRIu64 "\n", sim_stats->l1inst_num_misses);
    printf("L1 Instruction Evictions            %" PRIu64 "\n", sim_stats->l1inst_num_evictions);
    printf("L1 Instruction Hit Time             %.8f\n", sim_stats->l1inst_hit_time);
    printf("L1 Instruction Miss Penalty         %.8f\n", sim_stats->l1inst_miss_penalty);
    printf("L1 Instruction Miss Rate            %.8f\n", sim_stats->l1inst_miss_rate);
    printf("L1 Instruction Avg Access Time      %.8f\n", sim_stats->l1inst_AAT);

    // L1 Data Stats
    printf("L1 Data Accesses                    %" PRIu64 "\n", sim_stats->l1data_num_accesses);
    printf("L1 Data Load Accesses               %" PRIu64 "\n", sim_stats->l1data_num_accesses_loads);
    printf("L1 Data Store Accesses              %" PRIu64 "\n", sim_stats->l1data_num_accesses_stores);
    printf("L1 Data Misses                      %" PRIu64 "\n", sim_stats->l1data_num_misses);
    printf("L1 Data Load Misses                 %" PRIu64 "\n", sim_stats->l1data_num_misses_loads);
    printf("L1 Data Store Misses                %" PRIu64 "\n", sim_stats->l1data_num_misses_stores);
    printf("L1 Data Evictions                   %" PRIu64 "\n", sim_stats->l1data_num_evictions);
    printf("L1 Data Hit Time                    %.8f\n", sim_stats->l1data_hit_time);
    printf("L1 Data Miss Penalty                %.8f\n", sim_stats->l1data_miss_penalty);
    printf("L1 Data Miss Rate                   %.8f\n", sim_stats->l1data_miss_rate);
    printf("L1 Data Avg Access Time             %.8f\n", sim_stats->l1data_AAT);

    // L2 Stats
    printf("L2 Accesses                         %" PRIu64 "\n", sim_stats->l2unified_num_accesses);
    printf("L2 Instruction Accesses             %" PRIu64 "\n", sim_stats->l2unified_num_accesses_insts);
    printf("L2 Load Accesses                    %" PRIu64 "\n", sim_stats->l2unified_num_accesses_loads);
    printf("L2 Store Accesses                   %" PRIu64 "\n", sim_stats->l2unified_num_accesses_stores);
    printf("L2 Misses                           %" PRIu64 "\n", sim_stats->l2unified_num_misses);
    printf("L2 Instruction Misses               %" PRIu64 "\n", sim_stats->l2unified_num_misses_insts);
    printf("L2 Load Misses                      %" PRIu64 "\n", sim_stats->l2unified_num_misses_loads);
    printf("L2 Store Misses                     %" PRIu64 "\n", sim_stats->l2unified_num_misses_stores);
    printf("L2 Evictions                        %" PRIu64 "\n", sim_stats->l2unified_num_evictions);
    printf("L2 Write Backs                      %" PRIu64 "\n", sim_stats->l2unified_num_write_backs);
    printf("L2 Bytes Transferred                %" PRIu64 "\n", sim_stats->l2unified_num_bytes_transferred);
    printf("L2 Hit Time                         %.8f\n", sim_stats->l2unified_hit_time);
    printf("L2 Miss Penalty                     %.8f\n", sim_stats->l2unified_miss_penalty);
    printf("L2 Miss Rate                        %.8f\n", sim_stats->l2unified_miss_rate);
    printf("L2 Avg Access Time                  %.8f\n", sim_stats->l2unified_AAT);

    // Performance Statistics
    printf("Instruction Avg Access Time         %.8f\n", sim_stats->inst_avg_access_time);
    printf("Data (Load/Store) Avg Access Time   %.8f\n", sim_stats->data_avg_access_time);
    printf("Overall Average Access Time         %.8f\n", sim_stats->avg_access_time);
}

// Helper to compare json token strings
static int jsoneq(const char *json, jsmntok_t *tok, const char *s)
{
  if (tok->type == JSMN_STRING && (int)strlen(s) == tok->end - tok->start &&
      strncmp(json + tok->start, s, (size_t) (tok->end - tok->start)) == 0) {
    return 0;
  }
  return -1;
}

// Helper to parse a cache configuration -- does not check for error
static void parse_cache(const char *buffer, jsmntok_t *t, int index, struct cache_config_t *cache)
{
    char *ptr;
    if (jsoneq(buffer, &t[index], "C") == 0 && t[index + 1].type == JSMN_PRIMITIVE) {
        cache->c = (uint64_t) strtol(buffer + t[index + 1].start, &ptr, 10);
        index += 2;
    }

    if (jsoneq(buffer, &t[index], "B") == 0 && t[index + 1].type == JSMN_PRIMITIVE) {
        cache->b = (uint64_t) strtol(buffer + t[index + 1].start, &ptr, 10);
        index += 2;
    }

    if (jsoneq(buffer, &t[index], "S") == 0 && t[index + 1].type == JSMN_PRIMITIVE) {
        cache->s = (uint64_t) strtol(buffer + t[index + 1].start, &ptr, 10);
    }
}

// Helper for parsing a configuration file -- tries to check for basic errors
// Don't trust it with a file that is not a valid JSON.
static void parse_config(FILE *fin, struct sim_config_t *sim_conf)
{
    jsmn_parser p;
    jsmntok_t t[128]; // Not expecting a really large input so this should work
    jsmn_init(&p);

    char buffer[1024]; // For reading configuration file contents

    // Read config file contents
    if (fin) {
        size_t len = fread(buffer, sizeof(char), 1024, fin);
        if (ferror(fin) != 0) {
            print_err_usage("Error reading input configuration file");
        }
        buffer[len++] = '\0';
        fclose(fin);
    }

    // Tokenize the JSON configuration file
    int r = jsmn_parse(&p, buffer, strlen(buffer), t, sizeof(t) / sizeof(t[0]));
    if (r < 0 || (r < 1 || t[0].type != JSMN_OBJECT) ) {
        print_err_usage("Could not parse the configuration file");
    }

    for (int i = 1; i < r;) {

        if (jsoneq(buffer, &t[i], "L1 Instruction") == 0) {
            if (t[i + 1].type != JSMN_OBJECT) {
                print_err_usage("L1 Instruction Cache configuration error");
            }
            parse_cache(buffer, t, i + 2, &(sim_conf->l1inst));
            i += 8;
        } else if (jsoneq(buffer, &t[i], "L1 Data") == 0) {
            if (t[i + 1].type != JSMN_OBJECT) {
                print_err_usage("L1 Data Cache configuration error");
            }
            parse_cache(buffer, t, i + 2, &(sim_conf->l1data));
            i += 8;
        } else if (jsoneq(buffer, &t[i], "L2 Unified") == 0) {
            if (t[i + 1].type != JSMN_OBJECT) {
                print_err_usage("L2 Unified Cache configuration error");
            }
            parse_cache(buffer, t, i + 2, &(sim_conf->l2unified));
            i += 8;
        } else if (jsoneq(buffer, &t[i], "Replacement Policy") == 0) {
            if (t[i + 1].type != JSMN_STRING) {
                print_err_usage("Replacement Policy configuration error");
            } else {
                if (strncmp("LRU", buffer + t[i + 1].start, 3) == 0) {
                    sim_conf->rp = LRU;
                } else if (strncmp("LFU", buffer + t[i + 1].start, 3) == 0) {
                    sim_conf->rp = LFU;
                } else if (strncmp("FIFO", buffer + t[i + 1].start, 4) == 0) {
                    sim_conf->rp = FIFO;
                } else {
                    sim_conf->rp = LRU; // Default is LRU
                }
            }
            i += 2;
        } else if (jsoneq(buffer, &t[i], "Write Policy") == 0) {
            if (t[i + 1].type != JSMN_STRING) {
                print_err_usage("Write Policy configuration error");
            } else {
                if (strncmp("WBWA", buffer + t[i + 1].start, 4) == 0) {
                    sim_conf->wp = WBWA;
                } else if (strncmp("WTWNA", buffer + t[i + 1].start, 5) == 0) {
                    sim_conf->wp = WTWNA;
                } else {
                    sim_conf->wp = WBWA; // Default is write back write allocate
                }
            }
            i += 2;
        } else {
            i++; // just continue on incase something cannot be read
        }
    }
}

// Helper to verify that the input cache configuration is valid
static void verify_config(const struct sim_config_t *sim_conf)
{
    // Make sure block sizes are the same
    if (!((sim_conf->l1data.b == sim_conf->l1inst.b) &&  (sim_conf->l1data.b == sim_conf->l2unified.b))) {
        print_error_exit("Block sizes across caches must be the same\n");
    }

    // Ensure L1 size is within bounds
    if (sim_conf->l1data.c < MIN_L1_C || sim_conf->l1data.c > MAX_L1_C || sim_conf->l1inst.c < MIN_L1_C || sim_conf->l1inst.c > MAX_L1_C) {
        print_error_exit("L1 Data and Instruction caches cannot be smaller than 512B nor larger than 32KiB\n");
    }

    // Ensure L2 size is within bounds
    if (sim_conf->l2unified.c < MIN_L2_C || sim_conf->l2unified.c > MAX_L2_C) {
        print_error_exit("L2 cache cannot be smaller than 128KiB nor larger than 2MiB");
    }

    // Ensure L2 is bigger than L1 caches combined
    if ((1ul << sim_conf->l2unified.c) < ((1ul << sim_conf->l1data.c) + (1ul << sim_conf->l1inst.c))) {
        print_error_exit("The unified L2 cannot be smaller than the L1 caches\n");
    }
}

// This function does no error checking and uses magic numbers
static void setup_hit_times(struct sim_stats_t *sim_stats, const struct sim_config_t *sim_conf)
{
    // L1 Instruction
    if (sim_conf->l1inst.s <= MAX_S) {
        sim_stats->l1inst_hit_time = L1_ACCESS_TIME[sim_conf->l1inst.s][(sim_conf->l1inst.c - MIN_L1_C)];
    } else {
        sim_stats->l1inst_hit_time = L1_ACCESS_TIME[MAX_S+1][(sim_conf->l1inst.c - MIN_L1_C)];
    }

    // L1 Data
    if (sim_conf->l1data.s <= MAX_S) {
        sim_stats->l1data_hit_time = L1_ACCESS_TIME[sim_conf->l1data.s][(sim_conf->l1data.c - MIN_L1_C)];
    } else {
        sim_stats->l1data_hit_time = L1_ACCESS_TIME[MAX_S+1][(sim_conf->l1data.c - MIN_L1_C)];
    }

    // L2 Unified
    if (sim_conf->l2unified.s <= MAX_S) {
        sim_stats->l2unified_hit_time = L2_ACCESS_TIME[sim_conf->l2unified.s][(sim_conf->l2unified.c - MIN_L2_C)];
    } else {
        sim_stats->l2unified_hit_time = L2_ACCESS_TIME[MAX_S+1][(sim_conf->l2unified.c - MIN_L2_C)];
    }
}

// Drive the cache simulator
int main(int argc, char *const argv[])
{
    if (argc < 5) {
        print_err_usage("Input configuration file not provided");
    }

    FILE *fin = stdin; // config file
    FILE *trace = NULL; // trace file

    struct sim_config_t sim_conf;

    struct sim_stats_t sim_stats;
    memset(&sim_stats, 0, sizeof(sim_stats));

    int opt;
    while (-1 != (opt = getopt(argc, argv, "c:C:i:I:h"))) {
        switch (opt) {
            case 'c':
            case 'C':
                fin = fopen(optarg, "r");
                if (fin == NULL) {
                    print_err_usage("Could not open input configuration file");
                }
                parse_config(fin, &sim_conf); // read the json config file
                verify_config(&sim_conf); // verify that the configuration is legal
                setup_hit_times(&sim_stats, &sim_conf); // setup hit times from the hit times table
                break;

            case 'i':
            case 'I':
                trace = fopen(optarg, "r");
                if (trace == NULL) {
                    print_err_usage("Could not open the input trace file");
                }
                break;

            case 'h':
                print_err_usage("");
                break;
            default:
                print_err_usage("Invalid argument to program");
                break;
        }
    }

    // Print sim configuration
    print_sim_config(&sim_conf);

    // setup the cache structures
    sim_init(&sim_conf);

    // Run the simulator -- one access at a time
    char type;
    uint64_t addr;
    while (!feof(trace)) {
        int ret = fscanf(trace, "%c %" PRIx64 "\n", &type, &addr);
        if (ret == 2) {
            cache_access(addr, type, &sim_stats, &sim_conf);
        }
    }

    fclose(trace);

    sim_cleanup(&sim_stats, &sim_conf);

    print_sim_output(&sim_stats);

    return 0;
}
