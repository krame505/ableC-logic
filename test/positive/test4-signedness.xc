#include <logic.xh>
#include <logic_soft.h>

#include <stdio.h>

logic signed:32 foo(unsigned:32 a, signed:32 b) {
  signed:16 c = b[15..0];
  return 1 + (a + b);
}

int main() {
  int32_t a = 42;
  int32_t b = -142;
  
  int32_t result1 = logic host call foo(a, b);
  printf("result1: %d\n", result1);
  
  int32_t result2 = logic trans call foo(a, b);
  printf("result2: %d\n", result2);

  return result1 != result2;
}
