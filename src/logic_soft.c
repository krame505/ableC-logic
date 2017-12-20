
#include <logic_soft.h>
#include <stdio.h>
#include <stdlib.h>

typedef struct {
  channel_t input1;
  channel_t input2;
} gate_t;

gate_t gate_config[NUM_GATES] = {0};
channel_t output_config[NUM_OUTPUTS] = {0};
bool static_data[NUM_STATIC_CHANNELS] = {0};

#define DATA_HIGH_BIT (1lu << INPUT_DATA_SIZE - 1)

void soft_gate_config(channel_t channel, channel_t input1, channel_t input2) {
  if (channel < NUM_INPUTS) {
    fprintf(stderr, "Fatal error in soft_gate_config: Channel index %u less than minimum configurable channel %d\n", channel, NUM_INPUTS);
    exit(1);
  }
  if (channel >= NUM_CHANNELS) {
    fprintf(stderr, "Fatal error in soft_gate_config: Channel index %u exceeds max number of channels %d\n", channel, NUM_CHANNELS);
    exit(1);
  }
  if (input1 >= NUM_CHANNELS) {
    fprintf(stderr, "Fatal error in soft_gate_config: Input 1 index %u exceeds max number of channels %d\n", input1, NUM_CHANNELS);
    exit(1);
  }
  if (input2 >= NUM_CHANNELS) {
    fprintf(stderr, "Fatal error in soft_gate_config: Input 2 index %u exceeds max number of channels %d\n", input2, NUM_CHANNELS);
    exit(1);
  }
#ifdef DEBUG
  fprintf(stderr, "[%4u] := [%4u] NAND [%4u]\n", channel, input1, input2);
#endif
  gate_config[channel - NUM_INPUTS] = (gate_t){input1, input2};
}

void soft_gate_input_1_config(channel_t channel, channel_t input) {
  if (channel < NUM_INPUTS) {
    fprintf(stderr, "Fatal error in soft_gate_input_1_config: Channel index %u less than minimum configurable channel %d\n", channel, NUM_INPUTS);
    exit(1);
  }
  if (channel >= NUM_CHANNELS) {
    fprintf(stderr, "Fatal error in soft_gate_input_1_config: Channel index %u exceeds max number of channels %d\n", channel, NUM_CHANNELS);
    exit(1);
  }
  if (input >= NUM_CHANNELS) {
    fprintf(stderr, "Fatal error in soft_gate_input_1_config: Input 1 index %u exceeds max number of channels %d\n", input, NUM_CHANNELS);
    exit(1);
  }
#ifdef DEBUG
  fprintf(stderr, "[%4u] := [%4u] NAND _\n", channel, input);
#endif
  gate_config[channel - NUM_INPUTS].input1 = input;
}

void soft_gate_input_2_config(channel_t channel, channel_t input) {
  if (channel < NUM_INPUTS) {
    fprintf(stderr, "Fatal error in soft_gate_input_2_config: Channel index %u less than minimum configurable channel %d\n", channel, NUM_INPUTS);
    exit(1);
  }
  if (channel >= NUM_CHANNELS) {
    fprintf(stderr, "Fatal error in soft_gate_input_2_config: Channel index %u exceeds max number of channels %d\n", channel, NUM_CHANNELS);
    exit(1);
  }
  if (input >= NUM_CHANNELS) {
    fprintf(stderr, "Fatal error in soft_gate_input_2_config: Input 2 index %u exceeds max number of channels %d\n", input, NUM_CHANNELS);
    exit(1);
  }
#ifdef DEBUG
  fprintf(stderr, "[%4u] := _ NAND [%4u]\n", channel, input);
#endif
  gate_config[channel - NUM_INPUTS].input2 = input;
}

void soft_output_config(channel_t output, channel_t channel) {
  if (output >= NUM_OUTPUTS) {
    fprintf(stderr, "Fatal error in soft_output_config: Output index %u exceeds max number of outputs %d\n", channel, NUM_OUTPUTS);
    exit(1);
  }
  if (channel >= NUM_CHANNELS) {
    fprintf(stderr, "Fatal error in soft_output_config: Channel index %u exceeds max number of channels %d\n", channel, NUM_CHANNELS);
    exit(1);
  }
#ifdef DEBUG
  fprintf(stderr, "[[%2u]] := [%4u]\n", output, channel);
#endif
  output_config[output] = channel;
}

data_t soft_invoke(data_t val1, data_t val2) {
#ifdef DEBUG
  fprintf(stderr, "Inputs: %d, %d\n", val1, val2);
#endif
  bool data[NUM_CHANNELS];
  channel_t i = 0;
  for (; i < INPUT_DATA_SIZE; i++) {
#ifdef DEBUG
    fprintf(stderr, "[%4d] <- %d\n", i, (val1 & DATA_HIGH_BIT) != 0);
#endif
    data[i] = (val1 & DATA_HIGH_BIT) != 0;
    val1 <<= 1;
  }
  for (; i < INPUT_DATA_SIZE * 2; i++) {
#ifdef DEBUG
    fprintf(stderr, "[%4u] <- %d\n", i, (val2 & DATA_HIGH_BIT) != 0);
#endif
    data[i] = (val2 & DATA_HIGH_BIT) != 0;
    val2 <<= 1;
  }
  for (; i < NUM_CHANNELS; i++) {
#ifdef DEBUG
    fprintf(stderr, "[%4u] <- [%4u] NAND [%4u] = %d NAND %d = %d\n", i, gate_config[i - NUM_INPUTS].input1, gate_config[i - NUM_INPUTS].input2, data[gate_config[i - NUM_INPUTS].input1], data[gate_config[i - NUM_INPUTS].input2], !(data[gate_config[i - NUM_INPUTS].input1] && data[gate_config[i - NUM_INPUTS].input2]));
#endif
    data[i] = !(data[gate_config[i - NUM_INPUTS].input1] && data[gate_config[i - NUM_INPUTS].input2]);
  }
  data_t result = 0;
  for (i = 0; i < NUM_DIRECT_OUTPUTS; i++) {
#ifdef DEBUG
    fprintf(stderr, "[[%2u]] <- [%4u] = %d\n", i, output_config[i], data[output_config[i]]);
#endif
    result <<= 1;
    result |= data[output_config[i]];
  }
  for (; i < NUM_OUTPUTS; i++) {
#ifdef DEBUG
    fprintf(stderr, "[[%2u]] <- [%4u] = %d\n", i, output_config[i], data[output_config[i]]);
#endif
    static_data[i - NUM_DIRECT_OUTPUTS] = data[output_config[i]];
  }
#ifdef DEBUG
  fprintf(stderr, "Output: %d\n", result);
#endif
  return result;
}

data_t soft_invoke_static(data_t val1) {
#ifdef DEBUG
  fprintf(stderr, "Input: %d\n", val1);
#endif
  bool data[NUM_CHANNELS];
  channel_t i = 0;
  for (; i < INPUT_DATA_SIZE; i++) {
#ifdef DEBUG
    fprintf(stderr, "[%4d] <- %d\n", i, (val1 & DATA_HIGH_BIT) != 0);
#endif
    data[i] = (val1 & DATA_HIGH_BIT) != 0;
    val1 <<= 1;
  }
  for (; i < INPUT_DATA_SIZE * 2; i++) {
#ifdef DEBUG
    fprintf(stderr, "[%4u] <- %d\n", i, static_data[i - NUM_DIRECT_INPUTS]);
#endif
    data[i] = static_data[i - NUM_DIRECT_INPUTS];
  }
  for (; i < NUM_CHANNELS; i++) {
#ifdef DEBUG
    fprintf(stderr, "[%4u] <- [%4u] NAND [%4u] = %d NAND %d = %d\n", i, gate_config[i - NUM_INPUTS].input1, gate_config[i - NUM_INPUTS].input2, data[gate_config[i - NUM_INPUTS].input1], data[gate_config[i - NUM_INPUTS].input2], !(data[gate_config[i - NUM_INPUTS].input1] && data[gate_config[i - NUM_INPUTS].input2]));
#endif
    data[i] = !(data[gate_config[i - NUM_INPUTS].input1] && data[gate_config[i - NUM_INPUTS].input2]);
  }
  data_t result = 0;
  for (i = 0; i < NUM_DIRECT_OUTPUTS; i++) {
#ifdef DEBUG
    fprintf(stderr, "[[%2u]] <- [%4u] = %d\n", i, output_config[i], data[output_config[i]]);
#endif
    result <<= 1;
    result |= data[output_config[i]];
  }
  for (; i < NUM_OUTPUTS; i++) {
#ifdef DEBUG
    fprintf(stderr, "[[%2u]] <- [%4u] = %d\n", i, output_config[i], data[output_config[i]]);
#endif
    static_data[i - NUM_DIRECT_OUTPUTS] = data[output_config[i]];
  }
#ifdef DEBUG
  fprintf(stderr, "Output: %d\n", result);
#endif
  return result;
}
