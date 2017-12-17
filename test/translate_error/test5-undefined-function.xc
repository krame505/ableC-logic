#include <logic.xh>
#include <logic_soft.h>

#include <stdio.h>

logic unsigned:32 foo(unsigned:32 a, unsigned:32 b) {
  return bar();
}

int main() {
  uint32_t result = logic trans call foo(123, 456);
  printf("result: %d\n", result);

  return result != 0;
}
