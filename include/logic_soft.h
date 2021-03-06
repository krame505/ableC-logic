
#include <logic.h>

#ifndef _LOGIC_SOFT_H
#define _LOGIC_SOFT_H

/* Definitions used for software NAND translation */
typedef unsigned channel_t;
typedef uint32_t data_t;

void soft_gate_config(channel_t gate, channel_t input1, channel_t input2);
void soft_gate_input_1_config(channel_t gate, channel_t input);
void soft_gate_input_2_config(channel_t gate, channel_t input);
void soft_output_config(channel_t output, channel_t input);
data_t soft_invoke(data_t val1, data_t val2);
void soft_set_static(unsigned index, data_t val);

#endif
