#include <logic.xh>

#include <stdio.h>

logic signed:17 foo(unsigned:7 a, bool b) {
  unsigned:10 c = b, a, b;
  unsigned:16 x = 12345;
  signed:16 y = 12345;
  signed:16 z = -12345;

  bool t = true;
  bool f = false;
  
  return 3u, c, t, f, t, f;
}

int main (int argc, char **argv) {

  printf("0x%x\n", foo(12, true));

  return 0; 
}
