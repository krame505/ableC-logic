#include <logic.xh>
#include <logic_soft.h>

#include <stdio.h>

logic signed:32 inc(signed:32 a; signed:32 counter) {
  new counter = counter + a;
  return counter;
}

int main() {
  printf("host:\n%d\n", logic host call inc(1; 0));
  printf("%d\n", logic host invoke inc(2));
  printf("%d\n", logic host invoke inc(3));
  printf("%d\n", logic host invoke inc(4));
  printf("%d\n", logic host invoke inc(5));
  
  int32_t result1 = logic host invoke inc(6);
  
  printf("trans:\n%d\n", logic trans call inc(1; 0));
  printf("%d\n", logic trans invoke inc(2));
  printf("%d\n", logic trans invoke inc(3));
  printf("%d\n", logic trans invoke inc(4));
  printf("%d\n", logic trans invoke inc(5));

  int32_t result2 = logic trans invoke inc(6);
  
  return result1 != result2;
}
