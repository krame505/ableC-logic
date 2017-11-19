#include <logic.xh>

#include <stdio.h>

logic signed:32 foo(signed:32 a, signed:32 b) {
  signed:19 c = a[7..0];
  signed:3 d = b[2..0];
  return c + d;
}

int main() {
  int32_t a = -8;
  int32_t b = -2;
  
  int32_t result1 = logic host call foo(a, b);
  printf("result1: %d\n", result1);
  
  int32_t result2 = logic soft call foo(a, b);
  printf("result2: %d\n", result2);

  return result1 != result2;
}
