#include <logic.xh>
#include <logic_soft.h>

#include <stdio.h>

logic signed:8 mul8(signed:8 a, signed:8 b) {
  /* Signed masks are sign-extended from the single bit element */
  signed:8 mask0 = a[0];
  signed:8 data0 = b;
  signed:8 mask1 = a[1];
  signed:8 data1 = b[6..0], 0;
  signed:8 mask2 = a[2];
  signed:8 data2 = b[5..0], 0, 0;
  signed:8 mask3 = a[3];
  signed:8 data3 = b[4..0], 0, 0, 0;
  signed:8 mask4 = a[4];
  signed:8 data4 = b[3..0], 0, 0, 0, 0;
  signed:8 mask5 = a[5];
  signed:8 data5 = b[2..0], 0, 0, 0, 0, 0;
  signed:8 mask6 = a[6];
  signed:8 data6 = b[1..0], 0, 0, 0, 0, 0, 0;
  signed:8 mask7 = a[7];
  signed:8 data7 = b[0], 0, 0, 0, 0, 0, 0, 0;
  return (mask0 & data0) + (mask1 & data1) + (mask2 & data2) + (mask3 & data3) + (mask4 & data4) + (mask5 & data5) + (mask6 & data6) + (mask7 & data7);
}

logic unsigned:32 mul(unsigned:32 a, unsigned:32 b) {
  return mul8(a[7..0], b[7..0]);
}

int main() {
  int8_t a = -5;
  int8_t b = -19;

  int8_t result1 = logic host call mul(a, b);
  printf("result1: %d\n", result1);
  
  int8_t result2 = logic trans call mul(a, b);
  printf("result2: %d\n", result2);

  return result1 != result2;
}

