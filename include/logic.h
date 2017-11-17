
#include <stdint.h>

#ifndef _LOGIC_H
#define _LOGIC_H

// Check that bool, true and false aren't defined as macros
#if defined(bool) || defined(true) || defined(false)
#error "stdbool.h is incompatible with the boolean logic extension, and should not be included"
#endif

// Provide our own definitions for boolean constructs to be used at the program level
typedef _Bool bool;
static const bool true = 1;
static const bool false = 0;

// Define macros in case these are checked for existance prior to being defined in other places
#define bool bool
#define true true
#define false false
#define __bool_true_false_are_defined 1

// Definitions used for NAND translation
// Enum is accessable by the compiler, while a #define is not
enum {
  NUM_INPUTS = 64,
  NUM_GATES = 1024,
  NUM_OUTPUTS = 32,
  MAX_CRITICAL_PATH_LENGTH = 256,
  
  NUM_CHANNELS = NUM_INPUTS + NUM_GATES,
  INPUT_DATA_SIZE = NUM_INPUTS / 2
};

// Functions used for software NAND translation
typedef unsigned channel_t;
typedef uint32_t data_t;

void soft_gate_config(channel_t gate, channel_t input1, channel_t input2);
void soft_output_config(channel_t output, channel_t input);
data_t soft_invoke(data_t val1, data_t val2);

#endif
