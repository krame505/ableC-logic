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

logic bool bar(unsigned:8 x) {
  unsigned:4 y = x[0..3] | x[4..7];
  unsigned:2 z = y[0..1] | y[2..3];
  return z[0] | z[1];
}

logic unsigned:16 lsh(unsigned:16 x) {
  return x[1..15], false;
}

logic unsigned:16 rsh(unsigned:16 x) {
  return false, x[0..14];
}

logic unsigned:16 lsh3x(unsigned:16 x) {
  return lsh(lsh(lsh(x)));
}

logic unsigned:16 lsh6x(unsigned:16 x) {
  return lsh3x(lsh3x(x));
}

logic unsigned:8 bitNot8(unsigned:8 x) {
  return !x[0], !x[1], !x[2], !x[3], !x[4], !x[5], !x[6], !x[7];
}

logic unsigned:16 bitNot16(unsigned:16 x) {
  return bitNot8(x[0..7]), bitNot8(x[8..15]);
}

logic unsigned:16 baz(unsigned:8 x) {
  return lsh(bitNot8(x));
}

logic signed:16 arsh(signed:16 x) {
  return x[0], x[0..14];
}

logic unsigned:2 halfAdd(bool x, bool y) {
  return x && y, x ^ y;
}

logic signed:16 foo1(signed:16 x) {
  return x[0..14], !x[15];
}

logic signed:16 bar1(signed:8 x) {
  return foo1(x);
}

logic unsigned:16 opTest(unsigned:8 x, unsigned:16 y) {
  return x & y;
}

logic unsigned:16 opTest2(unsigned:16 x) {
  return ~x;
}

logic signed:16 opTest3(signed:8 x, signed:16 y) {
  return x ^ y;
}

int main (int argc, char **argv) {

  printf("0x%x\n", foo(12, true));
  uint16_t x = 1;
  printf("0x%x\n", x);
  for (int i = 0; i < 17; i++) {
    x = lsh(x);
    printf("0x%x\n", x);
  }
  x = 0x8000;
  printf("0x%x\n", x);
  for (int i = 0; i < 17; i++) {
    x = rsh(x);
    printf("0x%x\n", x);
  }
  x = 0x8000;
  printf("0x%x\n", x);
  for (int i = 0; i < 17; i++) {
    x = arsh(x);
    printf("0x%x\n", x);
  }
  printf("0x%x\n", lsh6x(0xAAAA));

  printf("0x%x\n", bitNot16(0x5555));
  printf("0x%x\n", bitNot16(bitNot16(0x5555)));

  printf("%x\n", halfAdd(false, false));
  printf("%x\n", halfAdd(false, true));
  printf("%x\n", halfAdd(true, false));
  printf("%x\n", halfAdd(true, true));
  
  printf("%d\n", bar1(5));
  printf("%d\n", bar1(-5));

  printf("0x%hx\n", opTest(0xFA, 0xAF23));
  printf("0x%hx\n", opTest2(0xF0F0));
  
  return 0; 
}
