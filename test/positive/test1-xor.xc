#include <logic.xh>

#include <stdio.h>

logic unsigned:32 xor_(unsigned:32 a, unsigned:32 b) {
  return a ^ b;
}

int main() {
  uint32_t a = 1234;
  uint32_t b = 5678;

  uint32_t result1 = logic host call xor_(a, b);
  printf("result1: %d\n", result1);
  
  uint32_t result2 = logic soft call xor_(a, b);
  printf("result2: %d\n", result2);

  return result1 != result2;
}
