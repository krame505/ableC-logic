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
  unsigned:4 y = x[7..4] | x[3..0];
  unsigned:2 z = y[3..2] | y[1..0];
  return z[0] | z[1];
}

logic unsigned:16 lsh1x(unsigned:16 x) {
  return x[14..0], false;
}

logic unsigned:16 rsh1x(unsigned:16 x) {
  return false, x[15..1];
}

logic unsigned:16 lsh3x(unsigned:16 x) {
  return lsh1x(lsh1x(lsh1x(x)));
}

logic unsigned:16 lsh6x(unsigned:16 x) {
  return lsh3x(lsh3x(x));
}

logic unsigned:8 bitNot8(unsigned:8 x) {
  return !x[7], !x[6], !x[5], !x[4], !x[3], !x[2], !x[1], !x[0];
}

logic unsigned:16 bitNot16(unsigned:16 x) {
  return bitNot8(x[15..8]), bitNot8(x[7..0]);
}

logic unsigned:16 baz(unsigned:8 x) {
  return lsh1x(bitNot8(x));
}

logic signed:16 arsh1x(signed:16 x) {
  return x[15], x[..1];
}

logic signed:16 foo1(signed:16 x) {
  return x[..1], !x[0];
}

logic signed:16 bar1(signed:8 x) {
  return foo1(x);
}

logic unsigned:16 opTest(unsigned:8 x, unsigned:16 y) {
  return x & y;
}

logic unsigned:16 opTest2(unsigned:16 x) {
  return !x;
}

logic signed:16 opTest3(signed:8 x, signed:16 y) {
  return x ^ y;
}

logic bool opTest4(bool x, bool y) {
  return x ^ y;
}

logic bool foo3(unsigned:3 a) {
  bool b = a[0] | a[1];
  bool c = b | a[2];
  return b & c | !b ^ !c;
}

logic bool foo4(unsigned:2 a) {
  bool b = a[0] | a[1];
  bool c = !false && b;
  return b ^ c;
}

logic signed:4 addTest1(signed:4 a) {
  return a + 1;
}

logic signed:4 addTest2() {
  return 5 + 7;
}

logic unsigned:3 addTest(unsigned:3 a, unsigned:3 b) {
  return a + b;
}

logic signed:4 foo5() {
  return addTest1(addTest1(addTest1(5)));
}

logic signed:16 foo6() {
  unsigned:8 y = 6;
  return 1 + 2 + (-3 - 4) + 5 + -y + 7;
}

logic signed:8 condTest(unsigned:4 v) {
  return v[0]? 1 : v[1]? 2 : 3;
}

logic signed:32 fib(; signed:32 a, signed:32 b) {
  signed:32 result = a + b;
  new a = result;
  new b = a;
  return result;
}

int main (int argc, char **argv) {
  printf("0x%x\n", foo(12, true));
  uint16_t x = 1;
  printf("0x%x\n", x);
  for (int i = 0; i < 17; i++) {
    x = lsh1x(x);
    printf("0x%x\n", x);
  }
  x = 0x8000;
  printf("0x%x\n", x);
  for (int i = 0; i < 17; i++) {
    x = rsh1x(x);
    printf("0x%x\n", x);
  }
  x = 0x8000;
  printf("0x%x\n", x);
  for (int i = 0; i < 17; i++) {
    x = arsh1x(x);
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

  logic bool nested(signed:2 foo) {
    return foo[0] | foo[1];
  }
  printf("%d\n", nested(2));

  printf("%d\n", addTest(2, 3));

  printf("%d\n", condTest(1));
  printf("%d\n", condTest(2));
  printf("%d\n", condTest(4));

  logic host static_init fib(1, 0);
  printf("%d\n", fib());
  printf("%d\n", fib());
  printf("%d\n", fib());
  printf("%d\n", fib());
  printf("%d\n", fib());
  printf("%d\n", fib());
  printf("%d\n", fib());
  printf("%d\n", fib());
  logic host static_init fib(1, 0);
  printf("%d\n", fib());
  printf("%d\n", fib());
  printf("%d\n", fib());
  printf("%d\n", fib());
  printf("%d\n", fib());
  printf("%d\n", fib());
  printf("%d\n", fib());
  printf("%d\n", fib());
  printf("%d\n", fib());
  printf("%d\n", fib());
  
  return 0; 
}
