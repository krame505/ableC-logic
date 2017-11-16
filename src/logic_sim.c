#include <logic.h>
#include <stdio.h>

typedef struct {
  channel_t input1;
  channel_t input2;
} gate_t;

gate_t gate_config[NUM_GATES];
channel_t output_config[NUM_OUTPUTS];

#define DATA_HIGH_BIT (1lu << INPUT_DATA_SIZE - 1)

void soft_gate_config(channel_t channel, channel_t input1, channel_t input2) {
  gate_config[channel - NUM_INPUTS] = (gate_t){input1, input2};
}

void soft_output_config(channel_t output, channel_t channel) {
  output_config[output] = channel;
}

data_t soft_invoke(data_t val1, data_t val2) {
  //fprintf(stderr, "Inputs: %d, %d\n", val1, val2);
  bool data[NUM_CHANNELS];
  channel_t i = 0;
  for (; i < INPUT_DATA_SIZE; i++) {
    //fprintf(stderr, "[%4d] <- %d\n", i, (val1 & DATA_HIGH_BIT) != 0);
    data[i] = (val1 & DATA_HIGH_BIT) != 0;
    val1 <<= 1;
  }
  for (; i < INPUT_DATA_SIZE * 2; i++) {
    //fprintf(stderr, "[%4d] <- %d\n", i, (val2 & DATA_HIGH_BIT) != 0);
    data[i] = (val2 & DATA_HIGH_BIT) != 0;
    val2 <<= 1;
  }
  for (; i < NUM_CHANNELS; i++) {
    //fprintf(stderr, "[%4d] <- [%4d] NAND [%4d] = %d NAND %d = %d\n", i, gate_config[i - NUM_INPUTS].input1, gate_config[i - NUM_INPUTS].input2, data[gate_config[i - NUM_INPUTS].input1], data[gate_config[i - NUM_INPUTS].input2], !(data[gate_config[i - NUM_INPUTS].input1] && data[gate_config[i - NUM_INPUTS].input2]));
    data[i] = !(data[gate_config[i - NUM_INPUTS].input1] && data[gate_config[i - NUM_INPUTS].input2]);
  }
  data_t result = 0;
  for (i = 0; i < NUM_OUTPUTS; i++) {
    //fprintf(stderr, "[[%d]] <- [%d] = %d\n", i, output_config[i], data[output_config[i]]);
    result <<= 1;
    result |= data[output_config[i]];
  }
  //fprintf(stderr, "Output: %d\n", result);
  return result;
}
