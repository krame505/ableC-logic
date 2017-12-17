#include <logic.xh>
#include <logic_soft.h>

#include <stdio.h>

logic signed:32 foo(signed:32 a, signed:32 b) {
  signed:8 c = a[0];
  unsigned:16 d = c;
  return d;
}

int main() {
  int32_t a = 1;
  int32_t b = 0;

  int32_t result1 = logic host call foo(a, b);
  printf("result1: %d\n", result1);
  
  int32_t result2 = logic trans call foo(a, b);
  printf("result2: %d\n", result2);

  return result1 != result2;
}
