#include <logic.xh>
#include <logic_soft.h>

#include <stdio.h>

logic unsigned:32 foo(unsigned:32 a, unsigned:32 b) {
  return ((a, a, a, a, a) + (b, b, b, b, b))[..128];
}

int main() {
  int a = 1234;
  int b = 5678;

  int result1 = logic host call foo(a, b);
  printf("result1: %d\n", result1);
  
  int result2 = logic trans call foo(a, b);
  printf("result2: %d\n", result2);

  return result1 != result2;
}
