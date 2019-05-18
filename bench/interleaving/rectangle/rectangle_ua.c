/* This code was generated by Usuba.
   See https://github.com/DadaIsCrazy/usuba.
   From the file "samples/usuba/rectangle_vector.ua" (included below). */

#include <stdint.h>

/* Do NOT change the order of those define/include */
#define NO_RUNTIME
#ifndef BITS_PER_REG
#define BITS_PER_REG 128
#endif
/* including the architecture specific .h */
#include "SSE.h"

/* auxiliary functions */
void SubColumn__V16 (/*inputs*/ DATATYPE a0,DATATYPE a1,DATATYPE a2,DATATYPE a3, /*outputs*/ DATATYPE* b0,DATATYPE* b1,DATATYPE* b2,DATATYPE* b3) {
  
  // Variables declaration
  DATATYPE t1;
  DATATYPE t11;
  DATATYPE t2;
  DATATYPE t3;
  DATATYPE t5;
  DATATYPE t6;
  DATATYPE t8;
  DATATYPE t9;

  // Instructions (body)
  t1 = NOT(a1);
  t2 = AND(a0,t1);
  t3 = XOR(a2,a3);
  *b0 = XOR(t2,t3);
  t5 = OR(a3,t1);
  t6 = XOR(a0,t5);
  *b1 = XOR(a2,t6);
  t8 = XOR(a1,a2);
  t9 = AND(t3,t6);
  *b3 = XOR(t8,t9);
  t11 = OR(*b0,t8);
  *b2 = XOR(t6,t11);

}

/* main function */
void Rectangle__ (/*inputs*/ DATATYPE plain__[4],uint16_t key__[26][4], /*outputs*/ DATATYPE cipher__[4]) {
  
  // Variables declaration
  DATATYPE _tmp10_0__;
  DATATYPE _tmp10_1__;
  DATATYPE _tmp10_2__;
  DATATYPE _tmp10_3__;
  DATATYPE _tmp11_0__;
  DATATYPE _tmp11_1__;
  DATATYPE _tmp11_2__;
  DATATYPE _tmp11_3__;
  DATATYPE _tmp12_0__;
  DATATYPE _tmp12_1__;
  DATATYPE _tmp12_2__;
  DATATYPE _tmp12_3__;
  DATATYPE _tmp13_0__;
  DATATYPE _tmp13_1__;
  DATATYPE _tmp13_2__;
  DATATYPE _tmp13_3__;
  DATATYPE _tmp14_0__;
  DATATYPE _tmp14_1__;
  DATATYPE _tmp14_2__;
  DATATYPE _tmp14_3__;
  DATATYPE _tmp15_0__;
  DATATYPE _tmp15_1__;
  DATATYPE _tmp15_2__;
  DATATYPE _tmp15_3__;
  DATATYPE _tmp16_0__;
  DATATYPE _tmp16_1__;
  DATATYPE _tmp16_2__;
  DATATYPE _tmp16_3__;
  DATATYPE _tmp17_0__;
  DATATYPE _tmp17_1__;
  DATATYPE _tmp17_2__;
  DATATYPE _tmp17_3__;
  DATATYPE _tmp18_0__;
  DATATYPE _tmp18_1__;
  DATATYPE _tmp18_2__;
  DATATYPE _tmp18_3__;
  DATATYPE _tmp19_0__;
  DATATYPE _tmp19_1__;
  DATATYPE _tmp19_2__;
  DATATYPE _tmp19_3__;
  DATATYPE _tmp1_0__;
  DATATYPE _tmp1_1__;
  DATATYPE _tmp1_2__;
  DATATYPE _tmp1_3__;
  DATATYPE _tmp20_0__;
  DATATYPE _tmp20_1__;
  DATATYPE _tmp20_2__;
  DATATYPE _tmp20_3__;
  DATATYPE _tmp21_0__;
  DATATYPE _tmp21_1__;
  DATATYPE _tmp21_2__;
  DATATYPE _tmp21_3__;
  DATATYPE _tmp22_0__;
  DATATYPE _tmp22_1__;
  DATATYPE _tmp22_2__;
  DATATYPE _tmp22_3__;
  DATATYPE _tmp23_0__;
  DATATYPE _tmp23_1__;
  DATATYPE _tmp23_2__;
  DATATYPE _tmp23_3__;
  DATATYPE _tmp24_0__;
  DATATYPE _tmp24_1__;
  DATATYPE _tmp24_2__;
  DATATYPE _tmp24_3__;
  DATATYPE _tmp25_0__;
  DATATYPE _tmp25_1__;
  DATATYPE _tmp25_2__;
  DATATYPE _tmp25_3__;
  DATATYPE _tmp26_0__;
  DATATYPE _tmp26_1__;
  DATATYPE _tmp26_2__;
  DATATYPE _tmp26_3__;
  DATATYPE _tmp27_0__;
  DATATYPE _tmp27_1__;
  DATATYPE _tmp27_2__;
  DATATYPE _tmp27_3__;
  DATATYPE _tmp28_0__;
  DATATYPE _tmp28_1__;
  DATATYPE _tmp28_2__;
  DATATYPE _tmp28_3__;
  DATATYPE _tmp29_0__;
  DATATYPE _tmp29_1__;
  DATATYPE _tmp29_2__;
  DATATYPE _tmp29_3__;
  DATATYPE _tmp2_0__;
  DATATYPE _tmp2_1__;
  DATATYPE _tmp2_2__;
  DATATYPE _tmp2_3__;
  DATATYPE _tmp30_0__;
  DATATYPE _tmp30_1__;
  DATATYPE _tmp30_2__;
  DATATYPE _tmp30_3__;
  DATATYPE _tmp31_0__;
  DATATYPE _tmp31_1__;
  DATATYPE _tmp31_2__;
  DATATYPE _tmp31_3__;
  DATATYPE _tmp32_0__;
  DATATYPE _tmp32_1__;
  DATATYPE _tmp32_2__;
  DATATYPE _tmp32_3__;
  DATATYPE _tmp33_0__;
  DATATYPE _tmp33_1__;
  DATATYPE _tmp33_2__;
  DATATYPE _tmp33_3__;
  DATATYPE _tmp34_0__;
  DATATYPE _tmp34_1__;
  DATATYPE _tmp34_2__;
  DATATYPE _tmp34_3__;
  DATATYPE _tmp35_0__;
  DATATYPE _tmp35_1__;
  DATATYPE _tmp35_2__;
  DATATYPE _tmp35_3__;
  DATATYPE _tmp36_0__;
  DATATYPE _tmp36_1__;
  DATATYPE _tmp36_2__;
  DATATYPE _tmp36_3__;
  DATATYPE _tmp37_0__;
  DATATYPE _tmp37_1__;
  DATATYPE _tmp37_2__;
  DATATYPE _tmp37_3__;
  DATATYPE _tmp38_0__;
  DATATYPE _tmp38_1__;
  DATATYPE _tmp38_2__;
  DATATYPE _tmp38_3__;
  DATATYPE _tmp39_0__;
  DATATYPE _tmp39_1__;
  DATATYPE _tmp39_2__;
  DATATYPE _tmp39_3__;
  DATATYPE _tmp3_0__;
  DATATYPE _tmp3_1__;
  DATATYPE _tmp3_2__;
  DATATYPE _tmp3_3__;
  DATATYPE _tmp40_0__;
  DATATYPE _tmp40_1__;
  DATATYPE _tmp40_2__;
  DATATYPE _tmp40_3__;
  DATATYPE _tmp41_0__;
  DATATYPE _tmp41_1__;
  DATATYPE _tmp41_2__;
  DATATYPE _tmp41_3__;
  DATATYPE _tmp42_0__;
  DATATYPE _tmp42_1__;
  DATATYPE _tmp42_2__;
  DATATYPE _tmp42_3__;
  DATATYPE _tmp43_0__;
  DATATYPE _tmp43_1__;
  DATATYPE _tmp43_2__;
  DATATYPE _tmp43_3__;
  DATATYPE _tmp44_0__;
  DATATYPE _tmp44_1__;
  DATATYPE _tmp44_2__;
  DATATYPE _tmp44_3__;
  DATATYPE _tmp45_0__;
  DATATYPE _tmp45_1__;
  DATATYPE _tmp45_2__;
  DATATYPE _tmp45_3__;
  DATATYPE _tmp46_0__;
  DATATYPE _tmp46_1__;
  DATATYPE _tmp46_2__;
  DATATYPE _tmp46_3__;
  DATATYPE _tmp47_0__;
  DATATYPE _tmp47_1__;
  DATATYPE _tmp47_2__;
  DATATYPE _tmp47_3__;
  DATATYPE _tmp48_0__;
  DATATYPE _tmp48_1__;
  DATATYPE _tmp48_2__;
  DATATYPE _tmp48_3__;
  DATATYPE _tmp49_0__;
  DATATYPE _tmp49_1__;
  DATATYPE _tmp49_2__;
  DATATYPE _tmp49_3__;
  DATATYPE _tmp4_0__;
  DATATYPE _tmp4_1__;
  DATATYPE _tmp4_2__;
  DATATYPE _tmp4_3__;
  DATATYPE _tmp50_0__;
  DATATYPE _tmp50_1__;
  DATATYPE _tmp50_2__;
  DATATYPE _tmp50_3__;
  DATATYPE _tmp5_0__;
  DATATYPE _tmp5_1__;
  DATATYPE _tmp5_2__;
  DATATYPE _tmp5_3__;
  DATATYPE _tmp6_0__;
  DATATYPE _tmp6_1__;
  DATATYPE _tmp6_2__;
  DATATYPE _tmp6_3__;
  DATATYPE _tmp7_0__;
  DATATYPE _tmp7_1__;
  DATATYPE _tmp7_2__;
  DATATYPE _tmp7_3__;
  DATATYPE _tmp8_0__;
  DATATYPE _tmp8_1__;
  DATATYPE _tmp8_2__;
  DATATYPE _tmp8_3__;
  DATATYPE _tmp9_0__;
  DATATYPE _tmp9_1__;
  DATATYPE _tmp9_2__;
  DATATYPE _tmp9_3__;
  DATATYPE tmp__1__1__;
  DATATYPE tmp__1__2__;
  DATATYPE tmp__1__3__;
  DATATYPE tmp__10__1__;
  DATATYPE tmp__10__2__;
  DATATYPE tmp__10__3__;
  DATATYPE tmp__11__1__;
  DATATYPE tmp__11__2__;
  DATATYPE tmp__11__3__;
  DATATYPE tmp__12__1__;
  DATATYPE tmp__12__2__;
  DATATYPE tmp__12__3__;
  DATATYPE tmp__13__1__;
  DATATYPE tmp__13__2__;
  DATATYPE tmp__13__3__;
  DATATYPE tmp__14__1__;
  DATATYPE tmp__14__2__;
  DATATYPE tmp__14__3__;
  DATATYPE tmp__15__1__;
  DATATYPE tmp__15__2__;
  DATATYPE tmp__15__3__;
  DATATYPE tmp__16__1__;
  DATATYPE tmp__16__2__;
  DATATYPE tmp__16__3__;
  DATATYPE tmp__17__1__;
  DATATYPE tmp__17__2__;
  DATATYPE tmp__17__3__;
  DATATYPE tmp__18__1__;
  DATATYPE tmp__18__2__;
  DATATYPE tmp__18__3__;
  DATATYPE tmp__19__1__;
  DATATYPE tmp__19__2__;
  DATATYPE tmp__19__3__;
  DATATYPE tmp__2__1__;
  DATATYPE tmp__2__2__;
  DATATYPE tmp__2__3__;
  DATATYPE tmp__20__1__;
  DATATYPE tmp__20__2__;
  DATATYPE tmp__20__3__;
  DATATYPE tmp__21__1__;
  DATATYPE tmp__21__2__;
  DATATYPE tmp__21__3__;
  DATATYPE tmp__22__1__;
  DATATYPE tmp__22__2__;
  DATATYPE tmp__22__3__;
  DATATYPE tmp__23__1__;
  DATATYPE tmp__23__2__;
  DATATYPE tmp__23__3__;
  DATATYPE tmp__24__1__;
  DATATYPE tmp__24__2__;
  DATATYPE tmp__24__3__;
  DATATYPE tmp__25__1__;
  DATATYPE tmp__25__2__;
  DATATYPE tmp__25__3__;
  DATATYPE tmp__3__1__;
  DATATYPE tmp__3__2__;
  DATATYPE tmp__3__3__;
  DATATYPE tmp__4__1__;
  DATATYPE tmp__4__2__;
  DATATYPE tmp__4__3__;
  DATATYPE tmp__5__1__;
  DATATYPE tmp__5__2__;
  DATATYPE tmp__5__3__;
  DATATYPE tmp__6__1__;
  DATATYPE tmp__6__2__;
  DATATYPE tmp__6__3__;
  DATATYPE tmp__7__1__;
  DATATYPE tmp__7__2__;
  DATATYPE tmp__7__3__;
  DATATYPE tmp__8__1__;
  DATATYPE tmp__8__2__;
  DATATYPE tmp__8__3__;
  DATATYPE tmp__9__1__;
  DATATYPE tmp__9__2__;
  DATATYPE tmp__9__3__;

  // Instructions (body)
  _tmp1_0__ = XOR(plain__[0],LIFT_16(key__[0][0]));
  _tmp1_1__ = XOR(plain__[1],LIFT_16(key__[0][1]));
  _tmp1_2__ = XOR(plain__[2],LIFT_16(key__[0][2]));
  _tmp1_3__ = XOR(plain__[3],LIFT_16(key__[0][3]));
  SubColumn__V16(_tmp1_0__,_tmp1_1__,_tmp1_2__,_tmp1_3__,&_tmp2_0__,&_tmp2_1__,&_tmp2_2__,&_tmp2_3__);
  tmp__1__1__ = L_ROTATE(_tmp2_1__,1,16);
  tmp__1__2__ = L_ROTATE(_tmp2_2__,12,16);
  tmp__1__3__ = L_ROTATE(_tmp2_3__,13,16);
  _tmp3_0__ = XOR(_tmp2_0__,LIFT_16(key__[1][0]));
  _tmp3_1__ = XOR(tmp__1__1__,LIFT_16(key__[1][1]));
  _tmp3_2__ = XOR(tmp__1__2__,LIFT_16(key__[1][2]));
  _tmp3_3__ = XOR(tmp__1__3__,LIFT_16(key__[1][3]));
  SubColumn__V16(_tmp3_0__,_tmp3_1__,_tmp3_2__,_tmp3_3__,&_tmp4_0__,&_tmp4_1__,&_tmp4_2__,&_tmp4_3__);
  tmp__2__1__ = L_ROTATE(_tmp4_1__,1,16);
  tmp__2__2__ = L_ROTATE(_tmp4_2__,12,16);
  tmp__2__3__ = L_ROTATE(_tmp4_3__,13,16);
  _tmp5_0__ = XOR(_tmp4_0__,LIFT_16(key__[2][0]));
  _tmp5_1__ = XOR(tmp__2__1__,LIFT_16(key__[2][1]));
  _tmp5_2__ = XOR(tmp__2__2__,LIFT_16(key__[2][2]));
  _tmp5_3__ = XOR(tmp__2__3__,LIFT_16(key__[2][3]));
  SubColumn__V16(_tmp5_0__,_tmp5_1__,_tmp5_2__,_tmp5_3__,&_tmp6_0__,&_tmp6_1__,&_tmp6_2__,&_tmp6_3__);
  tmp__3__1__ = L_ROTATE(_tmp6_1__,1,16);
  tmp__3__2__ = L_ROTATE(_tmp6_2__,12,16);
  tmp__3__3__ = L_ROTATE(_tmp6_3__,13,16);
  _tmp7_0__ = XOR(_tmp6_0__,LIFT_16(key__[3][0]));
  _tmp7_1__ = XOR(tmp__3__1__,LIFT_16(key__[3][1]));
  _tmp7_2__ = XOR(tmp__3__2__,LIFT_16(key__[3][2]));
  _tmp7_3__ = XOR(tmp__3__3__,LIFT_16(key__[3][3]));
  SubColumn__V16(_tmp7_0__,_tmp7_1__,_tmp7_2__,_tmp7_3__,&_tmp8_0__,&_tmp8_1__,&_tmp8_2__,&_tmp8_3__);
  tmp__4__1__ = L_ROTATE(_tmp8_1__,1,16);
  tmp__4__2__ = L_ROTATE(_tmp8_2__,12,16);
  tmp__4__3__ = L_ROTATE(_tmp8_3__,13,16);
  _tmp9_0__ = XOR(_tmp8_0__,LIFT_16(key__[4][0]));
  _tmp9_1__ = XOR(tmp__4__1__,LIFT_16(key__[4][1]));
  _tmp9_2__ = XOR(tmp__4__2__,LIFT_16(key__[4][2]));
  _tmp9_3__ = XOR(tmp__4__3__,LIFT_16(key__[4][3]));
  SubColumn__V16(_tmp9_0__,_tmp9_1__,_tmp9_2__,_tmp9_3__,&_tmp10_0__,&_tmp10_1__,&_tmp10_2__,&_tmp10_3__);
  tmp__5__1__ = L_ROTATE(_tmp10_1__,1,16);
  tmp__5__2__ = L_ROTATE(_tmp10_2__,12,16);
  tmp__5__3__ = L_ROTATE(_tmp10_3__,13,16);
  _tmp11_0__ = XOR(_tmp10_0__,LIFT_16(key__[5][0]));
  _tmp11_1__ = XOR(tmp__5__1__,LIFT_16(key__[5][1]));
  _tmp11_2__ = XOR(tmp__5__2__,LIFT_16(key__[5][2]));
  _tmp11_3__ = XOR(tmp__5__3__,LIFT_16(key__[5][3]));
  SubColumn__V16(_tmp11_0__,_tmp11_1__,_tmp11_2__,_tmp11_3__,&_tmp12_0__,&_tmp12_1__,&_tmp12_2__,&_tmp12_3__);
  tmp__6__1__ = L_ROTATE(_tmp12_1__,1,16);
  tmp__6__2__ = L_ROTATE(_tmp12_2__,12,16);
  tmp__6__3__ = L_ROTATE(_tmp12_3__,13,16);
  _tmp13_0__ = XOR(_tmp12_0__,LIFT_16(key__[6][0]));
  _tmp13_1__ = XOR(tmp__6__1__,LIFT_16(key__[6][1]));
  _tmp13_2__ = XOR(tmp__6__2__,LIFT_16(key__[6][2]));
  _tmp13_3__ = XOR(tmp__6__3__,LIFT_16(key__[6][3]));
  SubColumn__V16(_tmp13_0__,_tmp13_1__,_tmp13_2__,_tmp13_3__,&_tmp14_0__,&_tmp14_1__,&_tmp14_2__,&_tmp14_3__);
  tmp__7__1__ = L_ROTATE(_tmp14_1__,1,16);
  tmp__7__2__ = L_ROTATE(_tmp14_2__,12,16);
  tmp__7__3__ = L_ROTATE(_tmp14_3__,13,16);
  _tmp15_0__ = XOR(_tmp14_0__,LIFT_16(key__[7][0]));
  _tmp15_1__ = XOR(tmp__7__1__,LIFT_16(key__[7][1]));
  _tmp15_2__ = XOR(tmp__7__2__,LIFT_16(key__[7][2]));
  _tmp15_3__ = XOR(tmp__7__3__,LIFT_16(key__[7][3]));
  SubColumn__V16(_tmp15_0__,_tmp15_1__,_tmp15_2__,_tmp15_3__,&_tmp16_0__,&_tmp16_1__,&_tmp16_2__,&_tmp16_3__);
  tmp__8__1__ = L_ROTATE(_tmp16_1__,1,16);
  tmp__8__2__ = L_ROTATE(_tmp16_2__,12,16);
  tmp__8__3__ = L_ROTATE(_tmp16_3__,13,16);
  _tmp17_0__ = XOR(_tmp16_0__,LIFT_16(key__[8][0]));
  _tmp17_1__ = XOR(tmp__8__1__,LIFT_16(key__[8][1]));
  _tmp17_2__ = XOR(tmp__8__2__,LIFT_16(key__[8][2]));
  _tmp17_3__ = XOR(tmp__8__3__,LIFT_16(key__[8][3]));
  SubColumn__V16(_tmp17_0__,_tmp17_1__,_tmp17_2__,_tmp17_3__,&_tmp18_0__,&_tmp18_1__,&_tmp18_2__,&_tmp18_3__);
  tmp__9__1__ = L_ROTATE(_tmp18_1__,1,16);
  tmp__9__2__ = L_ROTATE(_tmp18_2__,12,16);
  tmp__9__3__ = L_ROTATE(_tmp18_3__,13,16);
  _tmp19_0__ = XOR(_tmp18_0__,LIFT_16(key__[9][0]));
  _tmp19_1__ = XOR(tmp__9__1__,LIFT_16(key__[9][1]));
  _tmp19_2__ = XOR(tmp__9__2__,LIFT_16(key__[9][2]));
  _tmp19_3__ = XOR(tmp__9__3__,LIFT_16(key__[9][3]));
  SubColumn__V16(_tmp19_0__,_tmp19_1__,_tmp19_2__,_tmp19_3__,&_tmp20_0__,&_tmp20_1__,&_tmp20_2__,&_tmp20_3__);
  tmp__10__1__ = L_ROTATE(_tmp20_1__,1,16);
  tmp__10__2__ = L_ROTATE(_tmp20_2__,12,16);
  tmp__10__3__ = L_ROTATE(_tmp20_3__,13,16);
  _tmp21_0__ = XOR(_tmp20_0__,LIFT_16(key__[10][0]));
  _tmp21_1__ = XOR(tmp__10__1__,LIFT_16(key__[10][1]));
  _tmp21_2__ = XOR(tmp__10__2__,LIFT_16(key__[10][2]));
  _tmp21_3__ = XOR(tmp__10__3__,LIFT_16(key__[10][3]));
  SubColumn__V16(_tmp21_0__,_tmp21_1__,_tmp21_2__,_tmp21_3__,&_tmp22_0__,&_tmp22_1__,&_tmp22_2__,&_tmp22_3__);
  tmp__11__1__ = L_ROTATE(_tmp22_1__,1,16);
  tmp__11__2__ = L_ROTATE(_tmp22_2__,12,16);
  tmp__11__3__ = L_ROTATE(_tmp22_3__,13,16);
  _tmp23_0__ = XOR(_tmp22_0__,LIFT_16(key__[11][0]));
  _tmp23_1__ = XOR(tmp__11__1__,LIFT_16(key__[11][1]));
  _tmp23_2__ = XOR(tmp__11__2__,LIFT_16(key__[11][2]));
  _tmp23_3__ = XOR(tmp__11__3__,LIFT_16(key__[11][3]));
  SubColumn__V16(_tmp23_0__,_tmp23_1__,_tmp23_2__,_tmp23_3__,&_tmp24_0__,&_tmp24_1__,&_tmp24_2__,&_tmp24_3__);
  tmp__12__1__ = L_ROTATE(_tmp24_1__,1,16);
  tmp__12__2__ = L_ROTATE(_tmp24_2__,12,16);
  tmp__12__3__ = L_ROTATE(_tmp24_3__,13,16);
  _tmp25_0__ = XOR(_tmp24_0__,LIFT_16(key__[12][0]));
  _tmp25_1__ = XOR(tmp__12__1__,LIFT_16(key__[12][1]));
  _tmp25_2__ = XOR(tmp__12__2__,LIFT_16(key__[12][2]));
  _tmp25_3__ = XOR(tmp__12__3__,LIFT_16(key__[12][3]));
  SubColumn__V16(_tmp25_0__,_tmp25_1__,_tmp25_2__,_tmp25_3__,&_tmp26_0__,&_tmp26_1__,&_tmp26_2__,&_tmp26_3__);
  tmp__13__1__ = L_ROTATE(_tmp26_1__,1,16);
  tmp__13__2__ = L_ROTATE(_tmp26_2__,12,16);
  tmp__13__3__ = L_ROTATE(_tmp26_3__,13,16);
  _tmp27_0__ = XOR(_tmp26_0__,LIFT_16(key__[13][0]));
  _tmp27_1__ = XOR(tmp__13__1__,LIFT_16(key__[13][1]));
  _tmp27_2__ = XOR(tmp__13__2__,LIFT_16(key__[13][2]));
  _tmp27_3__ = XOR(tmp__13__3__,LIFT_16(key__[13][3]));
  SubColumn__V16(_tmp27_0__,_tmp27_1__,_tmp27_2__,_tmp27_3__,&_tmp28_0__,&_tmp28_1__,&_tmp28_2__,&_tmp28_3__);
  tmp__14__1__ = L_ROTATE(_tmp28_1__,1,16);
  tmp__14__2__ = L_ROTATE(_tmp28_2__,12,16);
  tmp__14__3__ = L_ROTATE(_tmp28_3__,13,16);
  _tmp29_0__ = XOR(_tmp28_0__,LIFT_16(key__[14][0]));
  _tmp29_1__ = XOR(tmp__14__1__,LIFT_16(key__[14][1]));
  _tmp29_2__ = XOR(tmp__14__2__,LIFT_16(key__[14][2]));
  _tmp29_3__ = XOR(tmp__14__3__,LIFT_16(key__[14][3]));
  SubColumn__V16(_tmp29_0__,_tmp29_1__,_tmp29_2__,_tmp29_3__,&_tmp30_0__,&_tmp30_1__,&_tmp30_2__,&_tmp30_3__);
  tmp__15__1__ = L_ROTATE(_tmp30_1__,1,16);
  tmp__15__2__ = L_ROTATE(_tmp30_2__,12,16);
  tmp__15__3__ = L_ROTATE(_tmp30_3__,13,16);
  _tmp31_0__ = XOR(_tmp30_0__,LIFT_16(key__[15][0]));
  _tmp31_1__ = XOR(tmp__15__1__,LIFT_16(key__[15][1]));
  _tmp31_2__ = XOR(tmp__15__2__,LIFT_16(key__[15][2]));
  _tmp31_3__ = XOR(tmp__15__3__,LIFT_16(key__[15][3]));
  SubColumn__V16(_tmp31_0__,_tmp31_1__,_tmp31_2__,_tmp31_3__,&_tmp32_0__,&_tmp32_1__,&_tmp32_2__,&_tmp32_3__);
  tmp__16__1__ = L_ROTATE(_tmp32_1__,1,16);
  tmp__16__2__ = L_ROTATE(_tmp32_2__,12,16);
  tmp__16__3__ = L_ROTATE(_tmp32_3__,13,16);
  _tmp33_0__ = XOR(_tmp32_0__,LIFT_16(key__[16][0]));
  _tmp33_1__ = XOR(tmp__16__1__,LIFT_16(key__[16][1]));
  _tmp33_2__ = XOR(tmp__16__2__,LIFT_16(key__[16][2]));
  _tmp33_3__ = XOR(tmp__16__3__,LIFT_16(key__[16][3]));
  SubColumn__V16(_tmp33_0__,_tmp33_1__,_tmp33_2__,_tmp33_3__,&_tmp34_0__,&_tmp34_1__,&_tmp34_2__,&_tmp34_3__);
  tmp__17__1__ = L_ROTATE(_tmp34_1__,1,16);
  tmp__17__2__ = L_ROTATE(_tmp34_2__,12,16);
  tmp__17__3__ = L_ROTATE(_tmp34_3__,13,16);
  _tmp35_0__ = XOR(_tmp34_0__,LIFT_16(key__[17][0]));
  _tmp35_1__ = XOR(tmp__17__1__,LIFT_16(key__[17][1]));
  _tmp35_2__ = XOR(tmp__17__2__,LIFT_16(key__[17][2]));
  _tmp35_3__ = XOR(tmp__17__3__,LIFT_16(key__[17][3]));
  SubColumn__V16(_tmp35_0__,_tmp35_1__,_tmp35_2__,_tmp35_3__,&_tmp36_0__,&_tmp36_1__,&_tmp36_2__,&_tmp36_3__);
  tmp__18__1__ = L_ROTATE(_tmp36_1__,1,16);
  tmp__18__2__ = L_ROTATE(_tmp36_2__,12,16);
  tmp__18__3__ = L_ROTATE(_tmp36_3__,13,16);
  _tmp37_0__ = XOR(_tmp36_0__,LIFT_16(key__[18][0]));
  _tmp37_1__ = XOR(tmp__18__1__,LIFT_16(key__[18][1]));
  _tmp37_2__ = XOR(tmp__18__2__,LIFT_16(key__[18][2]));
  _tmp37_3__ = XOR(tmp__18__3__,LIFT_16(key__[18][3]));
  SubColumn__V16(_tmp37_0__,_tmp37_1__,_tmp37_2__,_tmp37_3__,&_tmp38_0__,&_tmp38_1__,&_tmp38_2__,&_tmp38_3__);
  tmp__19__1__ = L_ROTATE(_tmp38_1__,1,16);
  tmp__19__2__ = L_ROTATE(_tmp38_2__,12,16);
  tmp__19__3__ = L_ROTATE(_tmp38_3__,13,16);
  _tmp39_0__ = XOR(_tmp38_0__,LIFT_16(key__[19][0]));
  _tmp39_1__ = XOR(tmp__19__1__,LIFT_16(key__[19][1]));
  _tmp39_2__ = XOR(tmp__19__2__,LIFT_16(key__[19][2]));
  _tmp39_3__ = XOR(tmp__19__3__,LIFT_16(key__[19][3]));
  SubColumn__V16(_tmp39_0__,_tmp39_1__,_tmp39_2__,_tmp39_3__,&_tmp40_0__,&_tmp40_1__,&_tmp40_2__,&_tmp40_3__);
  tmp__20__1__ = L_ROTATE(_tmp40_1__,1,16);
  tmp__20__2__ = L_ROTATE(_tmp40_2__,12,16);
  tmp__20__3__ = L_ROTATE(_tmp40_3__,13,16);
  _tmp41_0__ = XOR(_tmp40_0__,LIFT_16(key__[20][0]));
  _tmp41_1__ = XOR(tmp__20__1__,LIFT_16(key__[20][1]));
  _tmp41_2__ = XOR(tmp__20__2__,LIFT_16(key__[20][2]));
  _tmp41_3__ = XOR(tmp__20__3__,LIFT_16(key__[20][3]));
  SubColumn__V16(_tmp41_0__,_tmp41_1__,_tmp41_2__,_tmp41_3__,&_tmp42_0__,&_tmp42_1__,&_tmp42_2__,&_tmp42_3__);
  tmp__21__1__ = L_ROTATE(_tmp42_1__,1,16);
  tmp__21__2__ = L_ROTATE(_tmp42_2__,12,16);
  tmp__21__3__ = L_ROTATE(_tmp42_3__,13,16);
  _tmp43_0__ = XOR(_tmp42_0__,LIFT_16(key__[21][0]));
  _tmp43_1__ = XOR(tmp__21__1__,LIFT_16(key__[21][1]));
  _tmp43_2__ = XOR(tmp__21__2__,LIFT_16(key__[21][2]));
  _tmp43_3__ = XOR(tmp__21__3__,LIFT_16(key__[21][3]));
  SubColumn__V16(_tmp43_0__,_tmp43_1__,_tmp43_2__,_tmp43_3__,&_tmp44_0__,&_tmp44_1__,&_tmp44_2__,&_tmp44_3__);
  tmp__22__1__ = L_ROTATE(_tmp44_1__,1,16);
  tmp__22__2__ = L_ROTATE(_tmp44_2__,12,16);
  tmp__22__3__ = L_ROTATE(_tmp44_3__,13,16);
  _tmp45_0__ = XOR(_tmp44_0__,LIFT_16(key__[22][0]));
  _tmp45_1__ = XOR(tmp__22__1__,LIFT_16(key__[22][1]));
  _tmp45_2__ = XOR(tmp__22__2__,LIFT_16(key__[22][2]));
  _tmp45_3__ = XOR(tmp__22__3__,LIFT_16(key__[22][3]));
  SubColumn__V16(_tmp45_0__,_tmp45_1__,_tmp45_2__,_tmp45_3__,&_tmp46_0__,&_tmp46_1__,&_tmp46_2__,&_tmp46_3__);
  tmp__23__1__ = L_ROTATE(_tmp46_1__,1,16);
  tmp__23__2__ = L_ROTATE(_tmp46_2__,12,16);
  tmp__23__3__ = L_ROTATE(_tmp46_3__,13,16);
  _tmp47_0__ = XOR(_tmp46_0__,LIFT_16(key__[23][0]));
  _tmp47_1__ = XOR(tmp__23__1__,LIFT_16(key__[23][1]));
  _tmp47_2__ = XOR(tmp__23__2__,LIFT_16(key__[23][2]));
  _tmp47_3__ = XOR(tmp__23__3__,LIFT_16(key__[23][3]));
  SubColumn__V16(_tmp47_0__,_tmp47_1__,_tmp47_2__,_tmp47_3__,&_tmp48_0__,&_tmp48_1__,&_tmp48_2__,&_tmp48_3__);
  tmp__24__1__ = L_ROTATE(_tmp48_1__,1,16);
  tmp__24__2__ = L_ROTATE(_tmp48_2__,12,16);
  tmp__24__3__ = L_ROTATE(_tmp48_3__,13,16);
  _tmp49_0__ = XOR(_tmp48_0__,LIFT_16(key__[24][0]));
  _tmp49_1__ = XOR(tmp__24__1__,LIFT_16(key__[24][1]));
  _tmp49_2__ = XOR(tmp__24__2__,LIFT_16(key__[24][2]));
  _tmp49_3__ = XOR(tmp__24__3__,LIFT_16(key__[24][3]));
  SubColumn__V16(_tmp49_0__,_tmp49_1__,_tmp49_2__,_tmp49_3__,&_tmp50_0__,&_tmp50_1__,&_tmp50_2__,&_tmp50_3__);
  tmp__25__1__ = L_ROTATE(_tmp50_1__,1,16);
  tmp__25__2__ = L_ROTATE(_tmp50_2__,12,16);
  tmp__25__3__ = L_ROTATE(_tmp50_3__,13,16);
  cipher__[0] = XOR(_tmp50_0__,LIFT_16(key__[25][0]));
  cipher__[1] = XOR(tmp__25__1__,LIFT_16(key__[25][1]));
  cipher__[2] = XOR(tmp__25__2__,LIFT_16(key__[25][2]));
  cipher__[3] = XOR(tmp__25__3__,LIFT_16(key__[25][3]));

}


/* **************************************************************** */
/*                            Usuba source                          */
/*                                                                  */
/*

 _no_inline table SubColumn(input :  v4 :: base)
  returns out :  v4 :: base
{
  6, 5, 12, 10, 1, 14, 7, 9, 11, 0, 3, 13, 8, 15, 4, 2
}


 node ShiftRows(input :  u16x4 :: base)
  returns out :  u16x4 :: base
vars

let
  (out[0]) = input[0];
  (out[1]) = (input[1] <<< 1);
  (out[2]) = (input[2] <<< 12);
  (out[3]) = (input[3] <<< 13)
tel

 node Rectangle(plain :  u16x4 :: base,key : const u16x4[26] :: base)
  returns cipher :  u16x4 :: base
vars
  tmp :  u16x4[26] :: base
let
  (tmp[0]) = plain;
  _no_unroll forall i in [0,24] {
    (tmp[(i + 1)]) = ShiftRows(SubColumn((tmp[i] ^ key[i])))
  };
  (cipher) = (tmp[25] ^ key[25])
tel

*/
 