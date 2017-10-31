#include <stdio.h>
#include <stdint.h>

int main (int argc, char **argv) {
  logic signed:32 foo(signed:8 a) {
    signed:16 b = a;
    return b;
  }

  printf("%d\n", foo(12));

  return 0; 
}
