
#include <stdint.h>

#ifndef _LOGIC_H
#define _LOGIC_H

/* Check that bool, true and false aren't defined as macros */
#if defined(bool) || defined(true) || defined(false)
#error "stdbool.h is incompatible with the boolean logic extension, and should not be included"
#endif

/* Provide our own definitions for boolean constructs to be used at the program level */
/* _Bool was introduced in C99, so use a uint8_t for older versions of C */
#if defined(__STDC_VERSION__) && __STDC_VERSION__ >= 199901L
typedef _Bool bool;
#else
typedef uint8_t bool;
#endif

static const bool true = 1;
static const bool false = 0;

/* Define macros in case these are checked for existance prior to being defined in other places */
#define bool bool
#define true true
#define false false
#define __bool_true_false_are_defined 1

/* Definitions used for NAND translation */
/* Enum is accessable by the compiler, while a #define is not */
enum {
  WORD_SIZE = 32,
  NUM_DIRECT_INPUTS = 64,
  NUM_DIRECT_OUTPUTS = 32,
  NUM_STATIC_CHANNELS = 128,
  NUM_GATES = 2048,
  MAX_CRITICAL_PATH_LENGTH = 256,

  NUM_INPUTS = NUM_DIRECT_INPUTS + NUM_STATIC_CHANNELS,
  NUM_OUTPUTS = NUM_DIRECT_OUTPUTS + NUM_STATIC_CHANNELS,
  NUM_CHANNELS = NUM_INPUTS + NUM_GATES,
  
  CRITICAL_PATH_PER_CYCLE = 32,
};

#endif
