#include <logic.xh>

#include <stdio.h>

logic signed:17 foo(unsigned:7 a, bool b) {
  unsigned:10 c = b, a, b;
  unsigned:16 x = 12345;
  signed:16 y = 12345;
  signed:16 z = -12345;

  bool t = true;
  bool f = false;

  unsigned:3 w = (3u, a)[3];
  
  return 3u, c, t, f, t, f;
}

logic unsigned:16 lsh(unsigned:16 x) {
  return x[1..15], false;
}

logic unsigned:8 bitNot(unsigned:8 x) {
  return !x[0], !x[1], !x[2], !x[3], !x[4], !x[5], !x[6], !x[7];
}

/*
logic signed:16 arsh(unsigned:16 x) {
  return 
}
*/
int main (int argc, char **argv) {

  printf("0x%x\n", foo(12, true));
  uint16_t x = 1;
  printf("0x%x\n", x);
  for (int i = 0; i < 17; i++) {
    x = lsh(x);
    printf("0x%x\n", x);
  }

  printf("0x%x\n", bitNot(0x55));
  printf("0x%x\n", bitNot(bitNot(0x55)));
  
  return 0; 
}
