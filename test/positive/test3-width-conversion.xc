#include <logic.xh>

#include <stdio.h>

logic unsigned:8 foo() {
  signed:8 x = 4;
  unsigned:16 y = x;
  return y[15..8];
}

int main() {
  uint32_t result = logic host call foo();
  printf("result: %d\n", result);

  return result != 0;
}
