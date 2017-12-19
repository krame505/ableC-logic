#include <logic.xh>
#include <logic_soft.h>
#include <stdio.h>

logic signed:32 foo(signed:32 a) {
  return a + 1;
}

logic signed:32 bar(signed:32 a, signed:32 b) {
  signed:32 a1 = foo(a);
  signed:32 a2 = foo(a1);
  signed:32 a3 = foo(a2);
  signed:32 a4 = foo(a3);
  signed:32 a5 = foo(a4);
  signed:32 a6 = foo(a5);
  signed:32 a7 = foo(a6);
  signed:32 a8 = foo(a7);
  signed:32 a9 = foo(a8);
  signed:32 a10 = foo(a9);
  signed:32 a11 = foo(a10);
  signed:32 a12 = foo(a11);
  signed:32 a13 = foo(a12);
  signed:32 a14 = foo(a13);
  signed:32 a15 = foo(a14);
  signed:32 a16 = foo(a15);
  signed:32 a17 = foo(a16);
  signed:32 a18 = foo(a17);
  signed:32 a19 = foo(a18);
  signed:32 a20 = foo(a19);
  signed:32 a21 = foo(a20);
  signed:32 a22 = foo(a21);
  signed:32 a23 = foo(a22);
  signed:32 a24 = foo(a23);
  signed:32 a25 = foo(a24);
  signed:32 a26 = foo(a25);
  signed:32 a27 = foo(a26);
  signed:32 a28 = foo(a27);
  signed:32 a29 = foo(a28);
  signed:32 a30 = foo(a29);
  signed:32 a31 = foo(a30);
  signed:32 a32 = foo(a31);
  return a5;
}

int main() {
  int result = logic trans call bar(120, 6);
  printf("%d\n", result);
}
