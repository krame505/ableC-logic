#include <logic_soft.h>

int main() {
  // Test that soft_gate_config gives an error for an invalid channel index
  soft_gate_config(1, -2, 3);

  return 0;
}
