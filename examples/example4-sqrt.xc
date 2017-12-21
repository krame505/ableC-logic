#include <logic.xh>
#include <logic_soft.h>
#include <stdio.h>

logic bool gt(unsigned:32 a, unsigned:32 b) {
  bool c1 = (a[31] && !b[31]);
  bool c2 = (a[30] && !b[30]) && !c1;
  bool c3 = (a[29] && !b[29]) && !c2;
  bool c4 = (a[28] && !b[28]) && !c3;
  bool c5 = (a[27] && !b[27]) && !c4;
  bool c6 = (a[26] && !b[26]) && !c5;
  bool c7 = (a[25] && !b[25]) && !c6;
  bool c8 = (a[24] && !b[24]) && !c7;
  bool c9 = (a[23] && !b[23]) && !c8;
  bool c10 = (a[22] && !b[22]) && !c9;
  bool c11 = (a[21] && !b[21]) && !c10;
  bool c12 = (a[20] && !b[20]) && !c11;
  bool c13 = (a[19] && !b[19]) && !c12;
  bool c14 = (a[18] && !b[18]) && !c13;
  bool c15 = (a[17] && !b[17]) && !c14;
  bool c16 = (a[16] && !b[16]) && !c15;
  bool c17 = (a[15] && !b[15]) && !c16;
  bool c18 = (a[14] && !b[14]) && !c17;
  bool c19 = (a[13] && !b[13]) && !c18;
  bool c20 = (a[12] && !b[12]) && !c19;
  bool c21 = (a[11] && !b[11]) && !c20;
  bool c22 = (a[10] && !b[10]) && !c21;
  bool c23 = (a[9] && !b[9]) && !c22;
  bool c24 = (a[8] && !b[8]) && !c23;
  bool c25 = (a[7] && !b[7]) && !c24;
  bool c26 = (a[6] && !b[6]) && !c25;
  bool c27 = (a[5] && !b[5]) && !c26;
  bool c28 = (a[4] && !b[4]) && !c27;
  bool c29 = (a[3] && !b[3]) && !c28;
  bool c30 = (a[2] && !b[2]) && !c29;
  bool c31 = (a[1] && !b[1]) && !c30;
  bool c32 = (a[0] && !b[0]) && !c31;
  return c1 || c2 || c3 || c4 || c5 || c6 || c7 || c8 || c9 || c10 || c11 || c12 || c13 || c14 || c15 || c16 || c17 || c18 || c19 || c20 || c21 || c22 || c23 || c24 || c25 || c26 || c27 || c28 || c29 || c30 || c31 || c32;
}

logic unsigned:32 isqrt_step(unsigned:32 res; unsigned:32 op, unsigned:32 mask, unsigned:32 mask_ready) {
  unsigned:32 newRes = !mask_ready? res : !gt(res + mask, op)? res[..1] + mask : res[..1];
  new op = mask_ready && !gt(res + mask, op)? op - (res + mask) : op;
  new mask = mask[..2];
  new mask_ready = mask_ready || !gt(mask[..2], op);
  return newRes;
}

uint32_t isqrt(uint32_t data, bool trans) {
  unsigned i;
  uint32_t res = 0;

  if (trans) {
    logic trans init isqrt_step;
    logic trans static_init isqrt_step(data, 0x40000000, data >= 0x40000000);
  } else {
    logic host init isqrt_step;
    logic host static_init isqrt_step(data, 0x40000000, data >= 0x40000000);
  }

  for (i = 0; i < 16; i++) {
    if (trans) {
      res = logic trans invoke isqrt_step(res);
    } else {
      res = logic host invoke isqrt_step(res);
    }
  }
  return res;
}

int main(size_t argc, char *argv[]) {
  printf("%d\n", isqrt(100, false));
  printf("%d\n", isqrt(100, true));
}
