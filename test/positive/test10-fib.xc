#include <logic.xh>
#include <logic_soft.h>

#include <stdio.h>

logic signed:32 fib(; signed:32 a, signed:32 b) {
  signed:32 result = a + b;
  new a = result;
  new b = a;
  return result;
}

int main() {
  logic host static_init fib(0, 1);
  printf("host:\n%d\n", logic host call fib());
  printf("%d\n", logic host invoke fib());
  printf("%d\n", logic host invoke fib());
  printf("%d\n", logic host invoke fib());
  printf("%d\n", logic host invoke fib());
  printf("%d\n", logic host invoke fib());
  
  int32_t result1 = logic host invoke fib();
  
  logic trans static_init fib(0, 1);
  printf("trans:\n%d\n", logic trans call fib());
  printf("%d\n", logic trans invoke fib());
  printf("%d\n", logic trans invoke fib());
  printf("%d\n", logic trans invoke fib());
  printf("%d\n", logic trans invoke fib());
  printf("%d\n", logic trans invoke fib());

  int32_t result2 = logic trans invoke fib();
  
  return result1 != result2;
}
