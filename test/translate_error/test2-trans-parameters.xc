#include <logic.xh>
#include <logic_soft.h>

#include <stdio.h>

logic unsigned:16 xor_(unsigned:128 a, unsigned:256 b) {
  return a ^ b;
}

int main() {
  int a = 1234;
  int b = 5678;

  int result1 = logic host call xor_(a, b);
  printf("result1: %d\n", result1);
  
  int result2 = logic trans call xor_(a, b);
  printf("result2: %d\n", result2);

  return result1 != result2;
}
