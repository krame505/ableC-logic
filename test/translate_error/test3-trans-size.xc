#include <logic.xh>
#include <logic_soft.h>

#include <stdio.h>

logic unsigned:32 foo(unsigned:32 a, unsigned:32 b) {
  return a ^ b ^ a ^ b ^ a ^ a ^ b ^ a ^ b ^ a ^ b ^ a ^ b ^ a ^ b ^ a ^ b ^ a ^ b;
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
