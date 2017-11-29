#include <logic.xh>
#include <logic_soft.h>

#include <stdio.h>

logic signed:32 add(signed:32 a, signed:32 b) {
  return a + b;
}

int main() {
  int32_t a = 42;
  int32_t b = -142;

  int32_t result1 = add(a, b);
  printf("result1: %d\n", result1);
  
  int32_t result2 = logic soft call add(a, b);
  printf("result2: %d\n", result2);

  return result1 != result2;
}
