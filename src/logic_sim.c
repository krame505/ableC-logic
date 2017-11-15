#include <logic.h>

typedef struct {
  channel_t input1;
  channel_t input2;
} gate_t;

gate_t gate_config[NUM_GATES];
channel_t output_config[NUM_OUTPUTS];

void soft_gate_config(channel_t channel, channel_t input1, channel_t input2) {
  gate_config[channel - NUM_INPUTS] = (gate_t){input1, input2};
}

void soft_output_config(channel_t output, channel_t channel) {
  output_config[output] = channel;
}

data_t soft_invoke(data_t val1, data_t val2) {
  bool data[NUM_CHANNELS];
  channel_t i = 0;
  for (; i < sizeof(data_t); i++) {
    data[i] = val1 & 1;
    val1 >>= 1;
  }
  for (; i < sizeof(data_t); i++) {
    data[i] = val2 & 1;
    val1 >>= 1;
  }
  for (; i < NUM_CHANNELS; i++) {
    data[i] = !(data[gate_config[i - NUM_INPUTS].input1] && data[gate_config[i - NUM_INPUTS].input2]);
  }
  data_t result = 0;
  for (i = 0; i < sizeof(data_t); i++) {
    result |= data[output_config[i]];
    result <<= 1;
  }
  return result;
}
