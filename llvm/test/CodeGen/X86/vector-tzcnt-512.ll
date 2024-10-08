; NOTE: Assertions have been autogenerated by utils/update_llc_test_checks.py
; RUN: llc < %s -mtriple=x86_64-unknown-unknown -mattr=+avx512f,+avx512cd | FileCheck %s --check-prefix=AVX512CD
; RUN: llc < %s -mtriple=x86_64-unknown-unknown -mattr=+avx512f,+avx512cd,+avx512bw | FileCheck %s --check-prefix=AVX512CDBW
; RUN: llc < %s -mtriple=x86_64-unknown-unknown -mattr=+avx512f,+avx512bw | FileCheck %s --check-prefix=AVX512BW
; RUN: llc < %s -mtriple=x86_64-unknown-unknown -mattr=+avx512vpopcntdq | FileCheck %s --check-prefix=AVX512VPOPCNTDQ
; RUN: llc < %s -mtriple=x86_64-unknown-unknown -mattr=+avx512bitalg | FileCheck %s --check-prefix=BITALG

define <8 x i64> @testv8i64(<8 x i64> %in) nounwind {
; AVX512CD-LABEL: testv8i64:
; AVX512CD:       # %bb.0:
; AVX512CD-NEXT:    vpternlogd {{.*#+}} zmm1 = -1
; AVX512CD-NEXT:    vpaddq %zmm1, %zmm0, %zmm1
; AVX512CD-NEXT:    vpandnq %zmm1, %zmm0, %zmm0
; AVX512CD-NEXT:    vplzcntq %zmm0, %zmm0
; AVX512CD-NEXT:    vpbroadcastq {{.*#+}} zmm1 = [64,64,64,64,64,64,64,64]
; AVX512CD-NEXT:    vpsubq %zmm0, %zmm1, %zmm0
; AVX512CD-NEXT:    retq
;
; AVX512CDBW-LABEL: testv8i64:
; AVX512CDBW:       # %bb.0:
; AVX512CDBW-NEXT:    vpternlogd {{.*#+}} zmm1 = -1
; AVX512CDBW-NEXT:    vpaddq %zmm1, %zmm0, %zmm1
; AVX512CDBW-NEXT:    vpandnq %zmm1, %zmm0, %zmm0
; AVX512CDBW-NEXT:    vplzcntq %zmm0, %zmm0
; AVX512CDBW-NEXT:    vpbroadcastq {{.*#+}} zmm1 = [64,64,64,64,64,64,64,64]
; AVX512CDBW-NEXT:    vpsubq %zmm0, %zmm1, %zmm0
; AVX512CDBW-NEXT:    retq
;
; AVX512BW-LABEL: testv8i64:
; AVX512BW:       # %bb.0:
; AVX512BW-NEXT:    vpternlogd {{.*#+}} zmm1 = -1
; AVX512BW-NEXT:    vpaddq %zmm1, %zmm0, %zmm1
; AVX512BW-NEXT:    vpandnq %zmm1, %zmm0, %zmm0
; AVX512BW-NEXT:    vpbroadcastb {{.*#+}} zmm1 = [15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15]
; AVX512BW-NEXT:    vpandq %zmm1, %zmm0, %zmm2
; AVX512BW-NEXT:    vbroadcasti32x4 {{.*#+}} zmm3 = [0,1,1,2,1,2,2,3,1,2,2,3,2,3,3,4,0,1,1,2,1,2,2,3,1,2,2,3,2,3,3,4,0,1,1,2,1,2,2,3,1,2,2,3,2,3,3,4,0,1,1,2,1,2,2,3,1,2,2,3,2,3,3,4]
; AVX512BW-NEXT:    # zmm3 = mem[0,1,2,3,0,1,2,3,0,1,2,3,0,1,2,3]
; AVX512BW-NEXT:    vpshufb %zmm2, %zmm3, %zmm2
; AVX512BW-NEXT:    vpsrlw $4, %zmm0, %zmm0
; AVX512BW-NEXT:    vpandq %zmm1, %zmm0, %zmm0
; AVX512BW-NEXT:    vpshufb %zmm0, %zmm3, %zmm0
; AVX512BW-NEXT:    vpaddb %zmm2, %zmm0, %zmm0
; AVX512BW-NEXT:    vpxor %xmm1, %xmm1, %xmm1
; AVX512BW-NEXT:    vpsadbw %zmm1, %zmm0, %zmm0
; AVX512BW-NEXT:    retq
;
; AVX512VPOPCNTDQ-LABEL: testv8i64:
; AVX512VPOPCNTDQ:       # %bb.0:
; AVX512VPOPCNTDQ-NEXT:    vpternlogd {{.*#+}} zmm1 = -1
; AVX512VPOPCNTDQ-NEXT:    vpaddq %zmm1, %zmm0, %zmm1
; AVX512VPOPCNTDQ-NEXT:    vpandnq %zmm1, %zmm0, %zmm0
; AVX512VPOPCNTDQ-NEXT:    vpopcntq %zmm0, %zmm0
; AVX512VPOPCNTDQ-NEXT:    retq
;
; BITALG-LABEL: testv8i64:
; BITALG:       # %bb.0:
; BITALG-NEXT:    vpternlogd {{.*#+}} zmm1 = -1
; BITALG-NEXT:    vpaddq %zmm1, %zmm0, %zmm1
; BITALG-NEXT:    vpandnq %zmm1, %zmm0, %zmm0
; BITALG-NEXT:    vpopcntb %zmm0, %zmm0
; BITALG-NEXT:    vpxor %xmm1, %xmm1, %xmm1
; BITALG-NEXT:    vpsadbw %zmm1, %zmm0, %zmm0
; BITALG-NEXT:    retq
  %out = call <8 x i64> @llvm.cttz.v8i64(<8 x i64> %in, i1 0)
  ret <8 x i64> %out
}

define <8 x i64> @testv8i64u(<8 x i64> %in) nounwind {
; AVX512CD-LABEL: testv8i64u:
; AVX512CD:       # %bb.0:
; AVX512CD-NEXT:    vpternlogd {{.*#+}} zmm1 = -1
; AVX512CD-NEXT:    vpaddq %zmm1, %zmm0, %zmm1
; AVX512CD-NEXT:    vpandnq %zmm1, %zmm0, %zmm0
; AVX512CD-NEXT:    vplzcntq %zmm0, %zmm0
; AVX512CD-NEXT:    vpbroadcastq {{.*#+}} zmm1 = [64,64,64,64,64,64,64,64]
; AVX512CD-NEXT:    vpsubq %zmm0, %zmm1, %zmm0
; AVX512CD-NEXT:    retq
;
; AVX512CDBW-LABEL: testv8i64u:
; AVX512CDBW:       # %bb.0:
; AVX512CDBW-NEXT:    vpternlogd {{.*#+}} zmm1 = -1
; AVX512CDBW-NEXT:    vpaddq %zmm1, %zmm0, %zmm1
; AVX512CDBW-NEXT:    vpandnq %zmm1, %zmm0, %zmm0
; AVX512CDBW-NEXT:    vplzcntq %zmm0, %zmm0
; AVX512CDBW-NEXT:    vpbroadcastq {{.*#+}} zmm1 = [64,64,64,64,64,64,64,64]
; AVX512CDBW-NEXT:    vpsubq %zmm0, %zmm1, %zmm0
; AVX512CDBW-NEXT:    retq
;
; AVX512BW-LABEL: testv8i64u:
; AVX512BW:       # %bb.0:
; AVX512BW-NEXT:    vpternlogd {{.*#+}} zmm1 = -1
; AVX512BW-NEXT:    vpaddq %zmm1, %zmm0, %zmm1
; AVX512BW-NEXT:    vpandnq %zmm1, %zmm0, %zmm0
; AVX512BW-NEXT:    vpbroadcastb {{.*#+}} zmm1 = [15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15]
; AVX512BW-NEXT:    vpandq %zmm1, %zmm0, %zmm2
; AVX512BW-NEXT:    vbroadcasti32x4 {{.*#+}} zmm3 = [0,1,1,2,1,2,2,3,1,2,2,3,2,3,3,4,0,1,1,2,1,2,2,3,1,2,2,3,2,3,3,4,0,1,1,2,1,2,2,3,1,2,2,3,2,3,3,4,0,1,1,2,1,2,2,3,1,2,2,3,2,3,3,4]
; AVX512BW-NEXT:    # zmm3 = mem[0,1,2,3,0,1,2,3,0,1,2,3,0,1,2,3]
; AVX512BW-NEXT:    vpshufb %zmm2, %zmm3, %zmm2
; AVX512BW-NEXT:    vpsrlw $4, %zmm0, %zmm0
; AVX512BW-NEXT:    vpandq %zmm1, %zmm0, %zmm0
; AVX512BW-NEXT:    vpshufb %zmm0, %zmm3, %zmm0
; AVX512BW-NEXT:    vpaddb %zmm2, %zmm0, %zmm0
; AVX512BW-NEXT:    vpxor %xmm1, %xmm1, %xmm1
; AVX512BW-NEXT:    vpsadbw %zmm1, %zmm0, %zmm0
; AVX512BW-NEXT:    retq
;
; AVX512VPOPCNTDQ-LABEL: testv8i64u:
; AVX512VPOPCNTDQ:       # %bb.0:
; AVX512VPOPCNTDQ-NEXT:    vpternlogd {{.*#+}} zmm1 = -1
; AVX512VPOPCNTDQ-NEXT:    vpaddq %zmm1, %zmm0, %zmm1
; AVX512VPOPCNTDQ-NEXT:    vpandnq %zmm1, %zmm0, %zmm0
; AVX512VPOPCNTDQ-NEXT:    vpopcntq %zmm0, %zmm0
; AVX512VPOPCNTDQ-NEXT:    retq
;
; BITALG-LABEL: testv8i64u:
; BITALG:       # %bb.0:
; BITALG-NEXT:    vpternlogd {{.*#+}} zmm1 = -1
; BITALG-NEXT:    vpaddq %zmm1, %zmm0, %zmm1
; BITALG-NEXT:    vpandnq %zmm1, %zmm0, %zmm0
; BITALG-NEXT:    vpopcntb %zmm0, %zmm0
; BITALG-NEXT:    vpxor %xmm1, %xmm1, %xmm1
; BITALG-NEXT:    vpsadbw %zmm1, %zmm0, %zmm0
; BITALG-NEXT:    retq
  %out = call <8 x i64> @llvm.cttz.v8i64(<8 x i64> %in, i1 -1)
  ret <8 x i64> %out
}

define <16 x i32> @testv16i32(<16 x i32> %in) nounwind {
; AVX512CD-LABEL: testv16i32:
; AVX512CD:       # %bb.0:
; AVX512CD-NEXT:    vpternlogd {{.*#+}} zmm1 = -1
; AVX512CD-NEXT:    vpaddd %zmm1, %zmm0, %zmm1
; AVX512CD-NEXT:    vpandnd %zmm1, %zmm0, %zmm0
; AVX512CD-NEXT:    vplzcntd %zmm0, %zmm0
; AVX512CD-NEXT:    vpbroadcastd {{.*#+}} zmm1 = [32,32,32,32,32,32,32,32,32,32,32,32,32,32,32,32]
; AVX512CD-NEXT:    vpsubd %zmm0, %zmm1, %zmm0
; AVX512CD-NEXT:    retq
;
; AVX512CDBW-LABEL: testv16i32:
; AVX512CDBW:       # %bb.0:
; AVX512CDBW-NEXT:    vpternlogd {{.*#+}} zmm1 = -1
; AVX512CDBW-NEXT:    vpaddd %zmm1, %zmm0, %zmm1
; AVX512CDBW-NEXT:    vpandnd %zmm1, %zmm0, %zmm0
; AVX512CDBW-NEXT:    vplzcntd %zmm0, %zmm0
; AVX512CDBW-NEXT:    vpbroadcastd {{.*#+}} zmm1 = [32,32,32,32,32,32,32,32,32,32,32,32,32,32,32,32]
; AVX512CDBW-NEXT:    vpsubd %zmm0, %zmm1, %zmm0
; AVX512CDBW-NEXT:    retq
;
; AVX512BW-LABEL: testv16i32:
; AVX512BW:       # %bb.0:
; AVX512BW-NEXT:    vpternlogd {{.*#+}} zmm1 = -1
; AVX512BW-NEXT:    vpaddd %zmm1, %zmm0, %zmm1
; AVX512BW-NEXT:    vpandnd %zmm1, %zmm0, %zmm0
; AVX512BW-NEXT:    vpbroadcastb {{.*#+}} zmm1 = [15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15]
; AVX512BW-NEXT:    vpandq %zmm1, %zmm0, %zmm2
; AVX512BW-NEXT:    vbroadcasti32x4 {{.*#+}} zmm3 = [0,1,1,2,1,2,2,3,1,2,2,3,2,3,3,4,0,1,1,2,1,2,2,3,1,2,2,3,2,3,3,4,0,1,1,2,1,2,2,3,1,2,2,3,2,3,3,4,0,1,1,2,1,2,2,3,1,2,2,3,2,3,3,4]
; AVX512BW-NEXT:    # zmm3 = mem[0,1,2,3,0,1,2,3,0,1,2,3,0,1,2,3]
; AVX512BW-NEXT:    vpshufb %zmm2, %zmm3, %zmm2
; AVX512BW-NEXT:    vpsrlw $4, %zmm0, %zmm0
; AVX512BW-NEXT:    vpandq %zmm1, %zmm0, %zmm0
; AVX512BW-NEXT:    vpshufb %zmm0, %zmm3, %zmm0
; AVX512BW-NEXT:    vpaddb %zmm2, %zmm0, %zmm0
; AVX512BW-NEXT:    vpxor %xmm1, %xmm1, %xmm1
; AVX512BW-NEXT:    vpunpckhdq {{.*#+}} zmm2 = zmm0[2],zmm1[2],zmm0[3],zmm1[3],zmm0[6],zmm1[6],zmm0[7],zmm1[7],zmm0[10],zmm1[10],zmm0[11],zmm1[11],zmm0[14],zmm1[14],zmm0[15],zmm1[15]
; AVX512BW-NEXT:    vpsadbw %zmm1, %zmm2, %zmm2
; AVX512BW-NEXT:    vpunpckldq {{.*#+}} zmm0 = zmm0[0],zmm1[0],zmm0[1],zmm1[1],zmm0[4],zmm1[4],zmm0[5],zmm1[5],zmm0[8],zmm1[8],zmm0[9],zmm1[9],zmm0[12],zmm1[12],zmm0[13],zmm1[13]
; AVX512BW-NEXT:    vpsadbw %zmm1, %zmm0, %zmm0
; AVX512BW-NEXT:    vpackuswb %zmm2, %zmm0, %zmm0
; AVX512BW-NEXT:    retq
;
; AVX512VPOPCNTDQ-LABEL: testv16i32:
; AVX512VPOPCNTDQ:       # %bb.0:
; AVX512VPOPCNTDQ-NEXT:    vpternlogd {{.*#+}} zmm1 = -1
; AVX512VPOPCNTDQ-NEXT:    vpaddd %zmm1, %zmm0, %zmm1
; AVX512VPOPCNTDQ-NEXT:    vpandnd %zmm1, %zmm0, %zmm0
; AVX512VPOPCNTDQ-NEXT:    vpopcntd %zmm0, %zmm0
; AVX512VPOPCNTDQ-NEXT:    retq
;
; BITALG-LABEL: testv16i32:
; BITALG:       # %bb.0:
; BITALG-NEXT:    vpternlogd {{.*#+}} zmm1 = -1
; BITALG-NEXT:    vpaddd %zmm1, %zmm0, %zmm1
; BITALG-NEXT:    vpandnd %zmm1, %zmm0, %zmm0
; BITALG-NEXT:    vpopcntb %zmm0, %zmm0
; BITALG-NEXT:    vpxor %xmm1, %xmm1, %xmm1
; BITALG-NEXT:    vpunpckhdq {{.*#+}} zmm2 = zmm0[2],zmm1[2],zmm0[3],zmm1[3],zmm0[6],zmm1[6],zmm0[7],zmm1[7],zmm0[10],zmm1[10],zmm0[11],zmm1[11],zmm0[14],zmm1[14],zmm0[15],zmm1[15]
; BITALG-NEXT:    vpsadbw %zmm1, %zmm2, %zmm2
; BITALG-NEXT:    vpunpckldq {{.*#+}} zmm0 = zmm0[0],zmm1[0],zmm0[1],zmm1[1],zmm0[4],zmm1[4],zmm0[5],zmm1[5],zmm0[8],zmm1[8],zmm0[9],zmm1[9],zmm0[12],zmm1[12],zmm0[13],zmm1[13]
; BITALG-NEXT:    vpsadbw %zmm1, %zmm0, %zmm0
; BITALG-NEXT:    vpackuswb %zmm2, %zmm0, %zmm0
; BITALG-NEXT:    retq
  %out = call <16 x i32> @llvm.cttz.v16i32(<16 x i32> %in, i1 0)
  ret <16 x i32> %out
}

define <16 x i32> @testv16i32u(<16 x i32> %in) nounwind {
; AVX512CD-LABEL: testv16i32u:
; AVX512CD:       # %bb.0:
; AVX512CD-NEXT:    vpternlogd {{.*#+}} zmm1 = -1
; AVX512CD-NEXT:    vpaddd %zmm1, %zmm0, %zmm1
; AVX512CD-NEXT:    vpandnd %zmm1, %zmm0, %zmm0
; AVX512CD-NEXT:    vplzcntd %zmm0, %zmm0
; AVX512CD-NEXT:    vpbroadcastd {{.*#+}} zmm1 = [32,32,32,32,32,32,32,32,32,32,32,32,32,32,32,32]
; AVX512CD-NEXT:    vpsubd %zmm0, %zmm1, %zmm0
; AVX512CD-NEXT:    retq
;
; AVX512CDBW-LABEL: testv16i32u:
; AVX512CDBW:       # %bb.0:
; AVX512CDBW-NEXT:    vpternlogd {{.*#+}} zmm1 = -1
; AVX512CDBW-NEXT:    vpaddd %zmm1, %zmm0, %zmm1
; AVX512CDBW-NEXT:    vpandnd %zmm1, %zmm0, %zmm0
; AVX512CDBW-NEXT:    vplzcntd %zmm0, %zmm0
; AVX512CDBW-NEXT:    vpbroadcastd {{.*#+}} zmm1 = [32,32,32,32,32,32,32,32,32,32,32,32,32,32,32,32]
; AVX512CDBW-NEXT:    vpsubd %zmm0, %zmm1, %zmm0
; AVX512CDBW-NEXT:    retq
;
; AVX512BW-LABEL: testv16i32u:
; AVX512BW:       # %bb.0:
; AVX512BW-NEXT:    vpternlogd {{.*#+}} zmm1 = -1
; AVX512BW-NEXT:    vpaddd %zmm1, %zmm0, %zmm1
; AVX512BW-NEXT:    vpandnd %zmm1, %zmm0, %zmm0
; AVX512BW-NEXT:    vpbroadcastb {{.*#+}} zmm1 = [15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15]
; AVX512BW-NEXT:    vpandq %zmm1, %zmm0, %zmm2
; AVX512BW-NEXT:    vbroadcasti32x4 {{.*#+}} zmm3 = [0,1,1,2,1,2,2,3,1,2,2,3,2,3,3,4,0,1,1,2,1,2,2,3,1,2,2,3,2,3,3,4,0,1,1,2,1,2,2,3,1,2,2,3,2,3,3,4,0,1,1,2,1,2,2,3,1,2,2,3,2,3,3,4]
; AVX512BW-NEXT:    # zmm3 = mem[0,1,2,3,0,1,2,3,0,1,2,3,0,1,2,3]
; AVX512BW-NEXT:    vpshufb %zmm2, %zmm3, %zmm2
; AVX512BW-NEXT:    vpsrlw $4, %zmm0, %zmm0
; AVX512BW-NEXT:    vpandq %zmm1, %zmm0, %zmm0
; AVX512BW-NEXT:    vpshufb %zmm0, %zmm3, %zmm0
; AVX512BW-NEXT:    vpaddb %zmm2, %zmm0, %zmm0
; AVX512BW-NEXT:    vpxor %xmm1, %xmm1, %xmm1
; AVX512BW-NEXT:    vpunpckhdq {{.*#+}} zmm2 = zmm0[2],zmm1[2],zmm0[3],zmm1[3],zmm0[6],zmm1[6],zmm0[7],zmm1[7],zmm0[10],zmm1[10],zmm0[11],zmm1[11],zmm0[14],zmm1[14],zmm0[15],zmm1[15]
; AVX512BW-NEXT:    vpsadbw %zmm1, %zmm2, %zmm2
; AVX512BW-NEXT:    vpunpckldq {{.*#+}} zmm0 = zmm0[0],zmm1[0],zmm0[1],zmm1[1],zmm0[4],zmm1[4],zmm0[5],zmm1[5],zmm0[8],zmm1[8],zmm0[9],zmm1[9],zmm0[12],zmm1[12],zmm0[13],zmm1[13]
; AVX512BW-NEXT:    vpsadbw %zmm1, %zmm0, %zmm0
; AVX512BW-NEXT:    vpackuswb %zmm2, %zmm0, %zmm0
; AVX512BW-NEXT:    retq
;
; AVX512VPOPCNTDQ-LABEL: testv16i32u:
; AVX512VPOPCNTDQ:       # %bb.0:
; AVX512VPOPCNTDQ-NEXT:    vpternlogd {{.*#+}} zmm1 = -1
; AVX512VPOPCNTDQ-NEXT:    vpaddd %zmm1, %zmm0, %zmm1
; AVX512VPOPCNTDQ-NEXT:    vpandnd %zmm1, %zmm0, %zmm0
; AVX512VPOPCNTDQ-NEXT:    vpopcntd %zmm0, %zmm0
; AVX512VPOPCNTDQ-NEXT:    retq
;
; BITALG-LABEL: testv16i32u:
; BITALG:       # %bb.0:
; BITALG-NEXT:    vpternlogd {{.*#+}} zmm1 = -1
; BITALG-NEXT:    vpaddd %zmm1, %zmm0, %zmm1
; BITALG-NEXT:    vpandnd %zmm1, %zmm0, %zmm0
; BITALG-NEXT:    vpopcntb %zmm0, %zmm0
; BITALG-NEXT:    vpxor %xmm1, %xmm1, %xmm1
; BITALG-NEXT:    vpunpckhdq {{.*#+}} zmm2 = zmm0[2],zmm1[2],zmm0[3],zmm1[3],zmm0[6],zmm1[6],zmm0[7],zmm1[7],zmm0[10],zmm1[10],zmm0[11],zmm1[11],zmm0[14],zmm1[14],zmm0[15],zmm1[15]
; BITALG-NEXT:    vpsadbw %zmm1, %zmm2, %zmm2
; BITALG-NEXT:    vpunpckldq {{.*#+}} zmm0 = zmm0[0],zmm1[0],zmm0[1],zmm1[1],zmm0[4],zmm1[4],zmm0[5],zmm1[5],zmm0[8],zmm1[8],zmm0[9],zmm1[9],zmm0[12],zmm1[12],zmm0[13],zmm1[13]
; BITALG-NEXT:    vpsadbw %zmm1, %zmm0, %zmm0
; BITALG-NEXT:    vpackuswb %zmm2, %zmm0, %zmm0
; BITALG-NEXT:    retq
  %out = call <16 x i32> @llvm.cttz.v16i32(<16 x i32> %in, i1 -1)
  ret <16 x i32> %out
}

define <32 x i16> @testv32i16(<32 x i16> %in) nounwind {
; AVX512CD-LABEL: testv32i16:
; AVX512CD:       # %bb.0:
; AVX512CD-NEXT:    vpcmpeqd %ymm1, %ymm1, %ymm1
; AVX512CD-NEXT:    vpaddw %ymm1, %ymm0, %ymm2
; AVX512CD-NEXT:    vpandn %ymm2, %ymm0, %ymm2
; AVX512CD-NEXT:    vpbroadcastb {{.*#+}} ymm3 = [15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15]
; AVX512CD-NEXT:    vpand %ymm3, %ymm2, %ymm4
; AVX512CD-NEXT:    vbroadcasti128 {{.*#+}} ymm5 = [0,1,1,2,1,2,2,3,1,2,2,3,2,3,3,4,0,1,1,2,1,2,2,3,1,2,2,3,2,3,3,4]
; AVX512CD-NEXT:    # ymm5 = mem[0,1,0,1]
; AVX512CD-NEXT:    vpshufb %ymm4, %ymm5, %ymm4
; AVX512CD-NEXT:    vpsrlw $4, %ymm2, %ymm2
; AVX512CD-NEXT:    vpand %ymm3, %ymm2, %ymm2
; AVX512CD-NEXT:    vpshufb %ymm2, %ymm5, %ymm2
; AVX512CD-NEXT:    vpaddb %ymm4, %ymm2, %ymm2
; AVX512CD-NEXT:    vpsllw $8, %ymm2, %ymm4
; AVX512CD-NEXT:    vpaddb %ymm2, %ymm4, %ymm2
; AVX512CD-NEXT:    vpsrlw $8, %ymm2, %ymm2
; AVX512CD-NEXT:    vextracti64x4 $1, %zmm0, %ymm0
; AVX512CD-NEXT:    vpaddw %ymm1, %ymm0, %ymm1
; AVX512CD-NEXT:    vpandn %ymm1, %ymm0, %ymm0
; AVX512CD-NEXT:    vpand %ymm3, %ymm0, %ymm1
; AVX512CD-NEXT:    vpshufb %ymm1, %ymm5, %ymm1
; AVX512CD-NEXT:    vpsrlw $4, %ymm0, %ymm0
; AVX512CD-NEXT:    vpand %ymm3, %ymm0, %ymm0
; AVX512CD-NEXT:    vpshufb %ymm0, %ymm5, %ymm0
; AVX512CD-NEXT:    vpaddb %ymm1, %ymm0, %ymm0
; AVX512CD-NEXT:    vpsllw $8, %ymm0, %ymm1
; AVX512CD-NEXT:    vpaddb %ymm0, %ymm1, %ymm0
; AVX512CD-NEXT:    vpsrlw $8, %ymm0, %ymm0
; AVX512CD-NEXT:    vinserti64x4 $1, %ymm0, %zmm2, %zmm0
; AVX512CD-NEXT:    retq
;
; AVX512CDBW-LABEL: testv32i16:
; AVX512CDBW:       # %bb.0:
; AVX512CDBW-NEXT:    vpternlogd {{.*#+}} zmm1 = -1
; AVX512CDBW-NEXT:    vpaddw %zmm1, %zmm0, %zmm1
; AVX512CDBW-NEXT:    vpandnq %zmm1, %zmm0, %zmm0
; AVX512CDBW-NEXT:    vpbroadcastb {{.*#+}} zmm1 = [15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15]
; AVX512CDBW-NEXT:    vpandq %zmm1, %zmm0, %zmm2
; AVX512CDBW-NEXT:    vbroadcasti32x4 {{.*#+}} zmm3 = [0,1,1,2,1,2,2,3,1,2,2,3,2,3,3,4,0,1,1,2,1,2,2,3,1,2,2,3,2,3,3,4,0,1,1,2,1,2,2,3,1,2,2,3,2,3,3,4,0,1,1,2,1,2,2,3,1,2,2,3,2,3,3,4]
; AVX512CDBW-NEXT:    # zmm3 = mem[0,1,2,3,0,1,2,3,0,1,2,3,0,1,2,3]
; AVX512CDBW-NEXT:    vpshufb %zmm2, %zmm3, %zmm2
; AVX512CDBW-NEXT:    vpsrlw $4, %zmm0, %zmm0
; AVX512CDBW-NEXT:    vpandq %zmm1, %zmm0, %zmm0
; AVX512CDBW-NEXT:    vpshufb %zmm0, %zmm3, %zmm0
; AVX512CDBW-NEXT:    vpaddb %zmm2, %zmm0, %zmm0
; AVX512CDBW-NEXT:    vpsllw $8, %zmm0, %zmm1
; AVX512CDBW-NEXT:    vpaddb %zmm0, %zmm1, %zmm0
; AVX512CDBW-NEXT:    vpsrlw $8, %zmm0, %zmm0
; AVX512CDBW-NEXT:    retq
;
; AVX512BW-LABEL: testv32i16:
; AVX512BW:       # %bb.0:
; AVX512BW-NEXT:    vpternlogd {{.*#+}} zmm1 = -1
; AVX512BW-NEXT:    vpaddw %zmm1, %zmm0, %zmm1
; AVX512BW-NEXT:    vpandnq %zmm1, %zmm0, %zmm0
; AVX512BW-NEXT:    vpbroadcastb {{.*#+}} zmm1 = [15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15]
; AVX512BW-NEXT:    vpandq %zmm1, %zmm0, %zmm2
; AVX512BW-NEXT:    vbroadcasti32x4 {{.*#+}} zmm3 = [0,1,1,2,1,2,2,3,1,2,2,3,2,3,3,4,0,1,1,2,1,2,2,3,1,2,2,3,2,3,3,4,0,1,1,2,1,2,2,3,1,2,2,3,2,3,3,4,0,1,1,2,1,2,2,3,1,2,2,3,2,3,3,4]
; AVX512BW-NEXT:    # zmm3 = mem[0,1,2,3,0,1,2,3,0,1,2,3,0,1,2,3]
; AVX512BW-NEXT:    vpshufb %zmm2, %zmm3, %zmm2
; AVX512BW-NEXT:    vpsrlw $4, %zmm0, %zmm0
; AVX512BW-NEXT:    vpandq %zmm1, %zmm0, %zmm0
; AVX512BW-NEXT:    vpshufb %zmm0, %zmm3, %zmm0
; AVX512BW-NEXT:    vpaddb %zmm2, %zmm0, %zmm0
; AVX512BW-NEXT:    vpsllw $8, %zmm0, %zmm1
; AVX512BW-NEXT:    vpaddb %zmm0, %zmm1, %zmm0
; AVX512BW-NEXT:    vpsrlw $8, %zmm0, %zmm0
; AVX512BW-NEXT:    retq
;
; AVX512VPOPCNTDQ-LABEL: testv32i16:
; AVX512VPOPCNTDQ:       # %bb.0:
; AVX512VPOPCNTDQ-NEXT:    vpcmpeqd %ymm1, %ymm1, %ymm1
; AVX512VPOPCNTDQ-NEXT:    vpaddw %ymm1, %ymm0, %ymm2
; AVX512VPOPCNTDQ-NEXT:    vpandn %ymm2, %ymm0, %ymm2
; AVX512VPOPCNTDQ-NEXT:    vpmovzxwd {{.*#+}} zmm2 = ymm2[0],zero,ymm2[1],zero,ymm2[2],zero,ymm2[3],zero,ymm2[4],zero,ymm2[5],zero,ymm2[6],zero,ymm2[7],zero,ymm2[8],zero,ymm2[9],zero,ymm2[10],zero,ymm2[11],zero,ymm2[12],zero,ymm2[13],zero,ymm2[14],zero,ymm2[15],zero
; AVX512VPOPCNTDQ-NEXT:    vpopcntd %zmm2, %zmm2
; AVX512VPOPCNTDQ-NEXT:    vpmovdw %zmm2, %ymm2
; AVX512VPOPCNTDQ-NEXT:    vextracti64x4 $1, %zmm0, %ymm0
; AVX512VPOPCNTDQ-NEXT:    vpaddw %ymm1, %ymm0, %ymm1
; AVX512VPOPCNTDQ-NEXT:    vpandn %ymm1, %ymm0, %ymm0
; AVX512VPOPCNTDQ-NEXT:    vpmovzxwd {{.*#+}} zmm0 = ymm0[0],zero,ymm0[1],zero,ymm0[2],zero,ymm0[3],zero,ymm0[4],zero,ymm0[5],zero,ymm0[6],zero,ymm0[7],zero,ymm0[8],zero,ymm0[9],zero,ymm0[10],zero,ymm0[11],zero,ymm0[12],zero,ymm0[13],zero,ymm0[14],zero,ymm0[15],zero
; AVX512VPOPCNTDQ-NEXT:    vpopcntd %zmm0, %zmm0
; AVX512VPOPCNTDQ-NEXT:    vpmovdw %zmm0, %ymm0
; AVX512VPOPCNTDQ-NEXT:    vinserti64x4 $1, %ymm0, %zmm2, %zmm0
; AVX512VPOPCNTDQ-NEXT:    retq
;
; BITALG-LABEL: testv32i16:
; BITALG:       # %bb.0:
; BITALG-NEXT:    vpternlogd {{.*#+}} zmm1 = -1
; BITALG-NEXT:    vpaddw %zmm1, %zmm0, %zmm1
; BITALG-NEXT:    vpandnq %zmm1, %zmm0, %zmm0
; BITALG-NEXT:    vpopcntw %zmm0, %zmm0
; BITALG-NEXT:    retq
  %out = call <32 x i16> @llvm.cttz.v32i16(<32 x i16> %in, i1 0)
  ret <32 x i16> %out
}

define <32 x i16> @testv32i16u(<32 x i16> %in) nounwind {
; AVX512CD-LABEL: testv32i16u:
; AVX512CD:       # %bb.0:
; AVX512CD-NEXT:    vpcmpeqd %ymm1, %ymm1, %ymm1
; AVX512CD-NEXT:    vpaddw %ymm1, %ymm0, %ymm2
; AVX512CD-NEXT:    vpandn %ymm2, %ymm0, %ymm2
; AVX512CD-NEXT:    vpbroadcastb {{.*#+}} ymm3 = [15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15]
; AVX512CD-NEXT:    vpand %ymm3, %ymm2, %ymm4
; AVX512CD-NEXT:    vbroadcasti128 {{.*#+}} ymm5 = [0,1,1,2,1,2,2,3,1,2,2,3,2,3,3,4,0,1,1,2,1,2,2,3,1,2,2,3,2,3,3,4]
; AVX512CD-NEXT:    # ymm5 = mem[0,1,0,1]
; AVX512CD-NEXT:    vpshufb %ymm4, %ymm5, %ymm4
; AVX512CD-NEXT:    vpsrlw $4, %ymm2, %ymm2
; AVX512CD-NEXT:    vpand %ymm3, %ymm2, %ymm2
; AVX512CD-NEXT:    vpshufb %ymm2, %ymm5, %ymm2
; AVX512CD-NEXT:    vpaddb %ymm4, %ymm2, %ymm2
; AVX512CD-NEXT:    vpsllw $8, %ymm2, %ymm4
; AVX512CD-NEXT:    vpaddb %ymm2, %ymm4, %ymm2
; AVX512CD-NEXT:    vpsrlw $8, %ymm2, %ymm2
; AVX512CD-NEXT:    vextracti64x4 $1, %zmm0, %ymm0
; AVX512CD-NEXT:    vpaddw %ymm1, %ymm0, %ymm1
; AVX512CD-NEXT:    vpandn %ymm1, %ymm0, %ymm0
; AVX512CD-NEXT:    vpand %ymm3, %ymm0, %ymm1
; AVX512CD-NEXT:    vpshufb %ymm1, %ymm5, %ymm1
; AVX512CD-NEXT:    vpsrlw $4, %ymm0, %ymm0
; AVX512CD-NEXT:    vpand %ymm3, %ymm0, %ymm0
; AVX512CD-NEXT:    vpshufb %ymm0, %ymm5, %ymm0
; AVX512CD-NEXT:    vpaddb %ymm1, %ymm0, %ymm0
; AVX512CD-NEXT:    vpsllw $8, %ymm0, %ymm1
; AVX512CD-NEXT:    vpaddb %ymm0, %ymm1, %ymm0
; AVX512CD-NEXT:    vpsrlw $8, %ymm0, %ymm0
; AVX512CD-NEXT:    vinserti64x4 $1, %ymm0, %zmm2, %zmm0
; AVX512CD-NEXT:    retq
;
; AVX512CDBW-LABEL: testv32i16u:
; AVX512CDBW:       # %bb.0:
; AVX512CDBW-NEXT:    vpternlogd {{.*#+}} zmm1 = -1
; AVX512CDBW-NEXT:    vpaddw %zmm1, %zmm0, %zmm1
; AVX512CDBW-NEXT:    vpandnq %zmm1, %zmm0, %zmm0
; AVX512CDBW-NEXT:    vpbroadcastb {{.*#+}} zmm1 = [15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15]
; AVX512CDBW-NEXT:    vpandq %zmm1, %zmm0, %zmm2
; AVX512CDBW-NEXT:    vbroadcasti32x4 {{.*#+}} zmm3 = [0,1,1,2,1,2,2,3,1,2,2,3,2,3,3,4,0,1,1,2,1,2,2,3,1,2,2,3,2,3,3,4,0,1,1,2,1,2,2,3,1,2,2,3,2,3,3,4,0,1,1,2,1,2,2,3,1,2,2,3,2,3,3,4]
; AVX512CDBW-NEXT:    # zmm3 = mem[0,1,2,3,0,1,2,3,0,1,2,3,0,1,2,3]
; AVX512CDBW-NEXT:    vpshufb %zmm2, %zmm3, %zmm2
; AVX512CDBW-NEXT:    vpsrlw $4, %zmm0, %zmm0
; AVX512CDBW-NEXT:    vpandq %zmm1, %zmm0, %zmm0
; AVX512CDBW-NEXT:    vpshufb %zmm0, %zmm3, %zmm0
; AVX512CDBW-NEXT:    vpaddb %zmm2, %zmm0, %zmm0
; AVX512CDBW-NEXT:    vpsllw $8, %zmm0, %zmm1
; AVX512CDBW-NEXT:    vpaddb %zmm0, %zmm1, %zmm0
; AVX512CDBW-NEXT:    vpsrlw $8, %zmm0, %zmm0
; AVX512CDBW-NEXT:    retq
;
; AVX512BW-LABEL: testv32i16u:
; AVX512BW:       # %bb.0:
; AVX512BW-NEXT:    vpternlogd {{.*#+}} zmm1 = -1
; AVX512BW-NEXT:    vpaddw %zmm1, %zmm0, %zmm1
; AVX512BW-NEXT:    vpandnq %zmm1, %zmm0, %zmm0
; AVX512BW-NEXT:    vpbroadcastb {{.*#+}} zmm1 = [15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15]
; AVX512BW-NEXT:    vpandq %zmm1, %zmm0, %zmm2
; AVX512BW-NEXT:    vbroadcasti32x4 {{.*#+}} zmm3 = [0,1,1,2,1,2,2,3,1,2,2,3,2,3,3,4,0,1,1,2,1,2,2,3,1,2,2,3,2,3,3,4,0,1,1,2,1,2,2,3,1,2,2,3,2,3,3,4,0,1,1,2,1,2,2,3,1,2,2,3,2,3,3,4]
; AVX512BW-NEXT:    # zmm3 = mem[0,1,2,3,0,1,2,3,0,1,2,3,0,1,2,3]
; AVX512BW-NEXT:    vpshufb %zmm2, %zmm3, %zmm2
; AVX512BW-NEXT:    vpsrlw $4, %zmm0, %zmm0
; AVX512BW-NEXT:    vpandq %zmm1, %zmm0, %zmm0
; AVX512BW-NEXT:    vpshufb %zmm0, %zmm3, %zmm0
; AVX512BW-NEXT:    vpaddb %zmm2, %zmm0, %zmm0
; AVX512BW-NEXT:    vpsllw $8, %zmm0, %zmm1
; AVX512BW-NEXT:    vpaddb %zmm0, %zmm1, %zmm0
; AVX512BW-NEXT:    vpsrlw $8, %zmm0, %zmm0
; AVX512BW-NEXT:    retq
;
; AVX512VPOPCNTDQ-LABEL: testv32i16u:
; AVX512VPOPCNTDQ:       # %bb.0:
; AVX512VPOPCNTDQ-NEXT:    vpcmpeqd %ymm1, %ymm1, %ymm1
; AVX512VPOPCNTDQ-NEXT:    vpaddw %ymm1, %ymm0, %ymm2
; AVX512VPOPCNTDQ-NEXT:    vpandn %ymm2, %ymm0, %ymm2
; AVX512VPOPCNTDQ-NEXT:    vpmovzxwd {{.*#+}} zmm2 = ymm2[0],zero,ymm2[1],zero,ymm2[2],zero,ymm2[3],zero,ymm2[4],zero,ymm2[5],zero,ymm2[6],zero,ymm2[7],zero,ymm2[8],zero,ymm2[9],zero,ymm2[10],zero,ymm2[11],zero,ymm2[12],zero,ymm2[13],zero,ymm2[14],zero,ymm2[15],zero
; AVX512VPOPCNTDQ-NEXT:    vpopcntd %zmm2, %zmm2
; AVX512VPOPCNTDQ-NEXT:    vpmovdw %zmm2, %ymm2
; AVX512VPOPCNTDQ-NEXT:    vextracti64x4 $1, %zmm0, %ymm0
; AVX512VPOPCNTDQ-NEXT:    vpaddw %ymm1, %ymm0, %ymm1
; AVX512VPOPCNTDQ-NEXT:    vpandn %ymm1, %ymm0, %ymm0
; AVX512VPOPCNTDQ-NEXT:    vpmovzxwd {{.*#+}} zmm0 = ymm0[0],zero,ymm0[1],zero,ymm0[2],zero,ymm0[3],zero,ymm0[4],zero,ymm0[5],zero,ymm0[6],zero,ymm0[7],zero,ymm0[8],zero,ymm0[9],zero,ymm0[10],zero,ymm0[11],zero,ymm0[12],zero,ymm0[13],zero,ymm0[14],zero,ymm0[15],zero
; AVX512VPOPCNTDQ-NEXT:    vpopcntd %zmm0, %zmm0
; AVX512VPOPCNTDQ-NEXT:    vpmovdw %zmm0, %ymm0
; AVX512VPOPCNTDQ-NEXT:    vinserti64x4 $1, %ymm0, %zmm2, %zmm0
; AVX512VPOPCNTDQ-NEXT:    retq
;
; BITALG-LABEL: testv32i16u:
; BITALG:       # %bb.0:
; BITALG-NEXT:    vpternlogd {{.*#+}} zmm1 = -1
; BITALG-NEXT:    vpaddw %zmm1, %zmm0, %zmm1
; BITALG-NEXT:    vpandnq %zmm1, %zmm0, %zmm0
; BITALG-NEXT:    vpopcntw %zmm0, %zmm0
; BITALG-NEXT:    retq
  %out = call <32 x i16> @llvm.cttz.v32i16(<32 x i16> %in, i1 -1)
  ret <32 x i16> %out
}

define <64 x i8> @testv64i8(<64 x i8> %in) nounwind {
; AVX512CD-LABEL: testv64i8:
; AVX512CD:       # %bb.0:
; AVX512CD-NEXT:    vextracti64x4 $1, %zmm0, %ymm1
; AVX512CD-NEXT:    vpcmpeqd %ymm2, %ymm2, %ymm2
; AVX512CD-NEXT:    vpaddb %ymm2, %ymm1, %ymm3
; AVX512CD-NEXT:    vpandn %ymm3, %ymm1, %ymm1
; AVX512CD-NEXT:    vpbroadcastb {{.*#+}} ymm3 = [15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15]
; AVX512CD-NEXT:    vpand %ymm3, %ymm1, %ymm4
; AVX512CD-NEXT:    vbroadcasti128 {{.*#+}} ymm5 = [0,1,1,2,1,2,2,3,1,2,2,3,2,3,3,4,0,1,1,2,1,2,2,3,1,2,2,3,2,3,3,4]
; AVX512CD-NEXT:    # ymm5 = mem[0,1,0,1]
; AVX512CD-NEXT:    vpshufb %ymm4, %ymm5, %ymm4
; AVX512CD-NEXT:    vpsrlw $4, %ymm1, %ymm1
; AVX512CD-NEXT:    vpand %ymm3, %ymm1, %ymm1
; AVX512CD-NEXT:    vpshufb %ymm1, %ymm5, %ymm1
; AVX512CD-NEXT:    vpaddb %ymm4, %ymm1, %ymm1
; AVX512CD-NEXT:    vpaddb %ymm2, %ymm0, %ymm2
; AVX512CD-NEXT:    vpandn %ymm2, %ymm0, %ymm0
; AVX512CD-NEXT:    vpand %ymm3, %ymm0, %ymm2
; AVX512CD-NEXT:    vpshufb %ymm2, %ymm5, %ymm2
; AVX512CD-NEXT:    vpsrlw $4, %ymm0, %ymm0
; AVX512CD-NEXT:    vpand %ymm3, %ymm0, %ymm0
; AVX512CD-NEXT:    vpshufb %ymm0, %ymm5, %ymm0
; AVX512CD-NEXT:    vpaddb %ymm2, %ymm0, %ymm0
; AVX512CD-NEXT:    vinserti64x4 $1, %ymm1, %zmm0, %zmm0
; AVX512CD-NEXT:    retq
;
; AVX512CDBW-LABEL: testv64i8:
; AVX512CDBW:       # %bb.0:
; AVX512CDBW-NEXT:    vpternlogd {{.*#+}} zmm1 = -1
; AVX512CDBW-NEXT:    vpaddb %zmm1, %zmm0, %zmm1
; AVX512CDBW-NEXT:    vpandnq %zmm1, %zmm0, %zmm0
; AVX512CDBW-NEXT:    vpbroadcastb {{.*#+}} zmm1 = [15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15]
; AVX512CDBW-NEXT:    vpandq %zmm1, %zmm0, %zmm2
; AVX512CDBW-NEXT:    vbroadcasti32x4 {{.*#+}} zmm3 = [0,1,1,2,1,2,2,3,1,2,2,3,2,3,3,4,0,1,1,2,1,2,2,3,1,2,2,3,2,3,3,4,0,1,1,2,1,2,2,3,1,2,2,3,2,3,3,4,0,1,1,2,1,2,2,3,1,2,2,3,2,3,3,4]
; AVX512CDBW-NEXT:    # zmm3 = mem[0,1,2,3,0,1,2,3,0,1,2,3,0,1,2,3]
; AVX512CDBW-NEXT:    vpshufb %zmm2, %zmm3, %zmm2
; AVX512CDBW-NEXT:    vpsrlw $4, %zmm0, %zmm0
; AVX512CDBW-NEXT:    vpandq %zmm1, %zmm0, %zmm0
; AVX512CDBW-NEXT:    vpshufb %zmm0, %zmm3, %zmm0
; AVX512CDBW-NEXT:    vpaddb %zmm2, %zmm0, %zmm0
; AVX512CDBW-NEXT:    retq
;
; AVX512BW-LABEL: testv64i8:
; AVX512BW:       # %bb.0:
; AVX512BW-NEXT:    vpternlogd {{.*#+}} zmm1 = -1
; AVX512BW-NEXT:    vpaddb %zmm1, %zmm0, %zmm1
; AVX512BW-NEXT:    vpandnq %zmm1, %zmm0, %zmm0
; AVX512BW-NEXT:    vpbroadcastb {{.*#+}} zmm1 = [15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15]
; AVX512BW-NEXT:    vpandq %zmm1, %zmm0, %zmm2
; AVX512BW-NEXT:    vbroadcasti32x4 {{.*#+}} zmm3 = [0,1,1,2,1,2,2,3,1,2,2,3,2,3,3,4,0,1,1,2,1,2,2,3,1,2,2,3,2,3,3,4,0,1,1,2,1,2,2,3,1,2,2,3,2,3,3,4,0,1,1,2,1,2,2,3,1,2,2,3,2,3,3,4]
; AVX512BW-NEXT:    # zmm3 = mem[0,1,2,3,0,1,2,3,0,1,2,3,0,1,2,3]
; AVX512BW-NEXT:    vpshufb %zmm2, %zmm3, %zmm2
; AVX512BW-NEXT:    vpsrlw $4, %zmm0, %zmm0
; AVX512BW-NEXT:    vpandq %zmm1, %zmm0, %zmm0
; AVX512BW-NEXT:    vpshufb %zmm0, %zmm3, %zmm0
; AVX512BW-NEXT:    vpaddb %zmm2, %zmm0, %zmm0
; AVX512BW-NEXT:    retq
;
; AVX512VPOPCNTDQ-LABEL: testv64i8:
; AVX512VPOPCNTDQ:       # %bb.0:
; AVX512VPOPCNTDQ-NEXT:    vextracti64x4 $1, %zmm0, %ymm1
; AVX512VPOPCNTDQ-NEXT:    vpcmpeqd %ymm2, %ymm2, %ymm2
; AVX512VPOPCNTDQ-NEXT:    vpaddb %ymm2, %ymm1, %ymm3
; AVX512VPOPCNTDQ-NEXT:    vpandn %ymm3, %ymm1, %ymm1
; AVX512VPOPCNTDQ-NEXT:    vpbroadcastb {{.*#+}} ymm3 = [15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15]
; AVX512VPOPCNTDQ-NEXT:    vpand %ymm3, %ymm1, %ymm4
; AVX512VPOPCNTDQ-NEXT:    vbroadcasti128 {{.*#+}} ymm5 = [0,1,1,2,1,2,2,3,1,2,2,3,2,3,3,4,0,1,1,2,1,2,2,3,1,2,2,3,2,3,3,4]
; AVX512VPOPCNTDQ-NEXT:    # ymm5 = mem[0,1,0,1]
; AVX512VPOPCNTDQ-NEXT:    vpshufb %ymm4, %ymm5, %ymm4
; AVX512VPOPCNTDQ-NEXT:    vpsrlw $4, %ymm1, %ymm1
; AVX512VPOPCNTDQ-NEXT:    vpand %ymm3, %ymm1, %ymm1
; AVX512VPOPCNTDQ-NEXT:    vpshufb %ymm1, %ymm5, %ymm1
; AVX512VPOPCNTDQ-NEXT:    vpaddb %ymm4, %ymm1, %ymm1
; AVX512VPOPCNTDQ-NEXT:    vpaddb %ymm2, %ymm0, %ymm2
; AVX512VPOPCNTDQ-NEXT:    vpandn %ymm2, %ymm0, %ymm0
; AVX512VPOPCNTDQ-NEXT:    vpand %ymm3, %ymm0, %ymm2
; AVX512VPOPCNTDQ-NEXT:    vpshufb %ymm2, %ymm5, %ymm2
; AVX512VPOPCNTDQ-NEXT:    vpsrlw $4, %ymm0, %ymm0
; AVX512VPOPCNTDQ-NEXT:    vpand %ymm3, %ymm0, %ymm0
; AVX512VPOPCNTDQ-NEXT:    vpshufb %ymm0, %ymm5, %ymm0
; AVX512VPOPCNTDQ-NEXT:    vpaddb %ymm2, %ymm0, %ymm0
; AVX512VPOPCNTDQ-NEXT:    vinserti64x4 $1, %ymm1, %zmm0, %zmm0
; AVX512VPOPCNTDQ-NEXT:    retq
;
; BITALG-LABEL: testv64i8:
; BITALG:       # %bb.0:
; BITALG-NEXT:    vpternlogd {{.*#+}} zmm1 = -1
; BITALG-NEXT:    vpaddb %zmm1, %zmm0, %zmm1
; BITALG-NEXT:    vpandnq %zmm1, %zmm0, %zmm0
; BITALG-NEXT:    vpopcntb %zmm0, %zmm0
; BITALG-NEXT:    retq
  %out = call <64 x i8> @llvm.cttz.v64i8(<64 x i8> %in, i1 0)
  ret <64 x i8> %out
}

define <64 x i8> @testv64i8u(<64 x i8> %in) nounwind {
; AVX512CD-LABEL: testv64i8u:
; AVX512CD:       # %bb.0:
; AVX512CD-NEXT:    vextracti64x4 $1, %zmm0, %ymm1
; AVX512CD-NEXT:    vpcmpeqd %ymm2, %ymm2, %ymm2
; AVX512CD-NEXT:    vpaddb %ymm2, %ymm1, %ymm3
; AVX512CD-NEXT:    vpandn %ymm3, %ymm1, %ymm1
; AVX512CD-NEXT:    vpbroadcastb {{.*#+}} ymm3 = [15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15]
; AVX512CD-NEXT:    vpand %ymm3, %ymm1, %ymm4
; AVX512CD-NEXT:    vbroadcasti128 {{.*#+}} ymm5 = [0,1,1,2,1,2,2,3,1,2,2,3,2,3,3,4,0,1,1,2,1,2,2,3,1,2,2,3,2,3,3,4]
; AVX512CD-NEXT:    # ymm5 = mem[0,1,0,1]
; AVX512CD-NEXT:    vpshufb %ymm4, %ymm5, %ymm4
; AVX512CD-NEXT:    vpsrlw $4, %ymm1, %ymm1
; AVX512CD-NEXT:    vpand %ymm3, %ymm1, %ymm1
; AVX512CD-NEXT:    vpshufb %ymm1, %ymm5, %ymm1
; AVX512CD-NEXT:    vpaddb %ymm4, %ymm1, %ymm1
; AVX512CD-NEXT:    vpaddb %ymm2, %ymm0, %ymm2
; AVX512CD-NEXT:    vpandn %ymm2, %ymm0, %ymm0
; AVX512CD-NEXT:    vpand %ymm3, %ymm0, %ymm2
; AVX512CD-NEXT:    vpshufb %ymm2, %ymm5, %ymm2
; AVX512CD-NEXT:    vpsrlw $4, %ymm0, %ymm0
; AVX512CD-NEXT:    vpand %ymm3, %ymm0, %ymm0
; AVX512CD-NEXT:    vpshufb %ymm0, %ymm5, %ymm0
; AVX512CD-NEXT:    vpaddb %ymm2, %ymm0, %ymm0
; AVX512CD-NEXT:    vinserti64x4 $1, %ymm1, %zmm0, %zmm0
; AVX512CD-NEXT:    retq
;
; AVX512CDBW-LABEL: testv64i8u:
; AVX512CDBW:       # %bb.0:
; AVX512CDBW-NEXT:    vpternlogd {{.*#+}} zmm1 = -1
; AVX512CDBW-NEXT:    vpaddb %zmm1, %zmm0, %zmm1
; AVX512CDBW-NEXT:    vpandnq %zmm1, %zmm0, %zmm0
; AVX512CDBW-NEXT:    vpbroadcastb {{.*#+}} zmm1 = [15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15]
; AVX512CDBW-NEXT:    vpandq %zmm1, %zmm0, %zmm2
; AVX512CDBW-NEXT:    vbroadcasti32x4 {{.*#+}} zmm3 = [0,1,1,2,1,2,2,3,1,2,2,3,2,3,3,4,0,1,1,2,1,2,2,3,1,2,2,3,2,3,3,4,0,1,1,2,1,2,2,3,1,2,2,3,2,3,3,4,0,1,1,2,1,2,2,3,1,2,2,3,2,3,3,4]
; AVX512CDBW-NEXT:    # zmm3 = mem[0,1,2,3,0,1,2,3,0,1,2,3,0,1,2,3]
; AVX512CDBW-NEXT:    vpshufb %zmm2, %zmm3, %zmm2
; AVX512CDBW-NEXT:    vpsrlw $4, %zmm0, %zmm0
; AVX512CDBW-NEXT:    vpandq %zmm1, %zmm0, %zmm0
; AVX512CDBW-NEXT:    vpshufb %zmm0, %zmm3, %zmm0
; AVX512CDBW-NEXT:    vpaddb %zmm2, %zmm0, %zmm0
; AVX512CDBW-NEXT:    retq
;
; AVX512BW-LABEL: testv64i8u:
; AVX512BW:       # %bb.0:
; AVX512BW-NEXT:    vpternlogd {{.*#+}} zmm1 = -1
; AVX512BW-NEXT:    vpaddb %zmm1, %zmm0, %zmm1
; AVX512BW-NEXT:    vpandnq %zmm1, %zmm0, %zmm0
; AVX512BW-NEXT:    vpbroadcastb {{.*#+}} zmm1 = [15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15]
; AVX512BW-NEXT:    vpandq %zmm1, %zmm0, %zmm2
; AVX512BW-NEXT:    vbroadcasti32x4 {{.*#+}} zmm3 = [0,1,1,2,1,2,2,3,1,2,2,3,2,3,3,4,0,1,1,2,1,2,2,3,1,2,2,3,2,3,3,4,0,1,1,2,1,2,2,3,1,2,2,3,2,3,3,4,0,1,1,2,1,2,2,3,1,2,2,3,2,3,3,4]
; AVX512BW-NEXT:    # zmm3 = mem[0,1,2,3,0,1,2,3,0,1,2,3,0,1,2,3]
; AVX512BW-NEXT:    vpshufb %zmm2, %zmm3, %zmm2
; AVX512BW-NEXT:    vpsrlw $4, %zmm0, %zmm0
; AVX512BW-NEXT:    vpandq %zmm1, %zmm0, %zmm0
; AVX512BW-NEXT:    vpshufb %zmm0, %zmm3, %zmm0
; AVX512BW-NEXT:    vpaddb %zmm2, %zmm0, %zmm0
; AVX512BW-NEXT:    retq
;
; AVX512VPOPCNTDQ-LABEL: testv64i8u:
; AVX512VPOPCNTDQ:       # %bb.0:
; AVX512VPOPCNTDQ-NEXT:    vextracti64x4 $1, %zmm0, %ymm1
; AVX512VPOPCNTDQ-NEXT:    vpcmpeqd %ymm2, %ymm2, %ymm2
; AVX512VPOPCNTDQ-NEXT:    vpaddb %ymm2, %ymm1, %ymm3
; AVX512VPOPCNTDQ-NEXT:    vpandn %ymm3, %ymm1, %ymm1
; AVX512VPOPCNTDQ-NEXT:    vpbroadcastb {{.*#+}} ymm3 = [15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15]
; AVX512VPOPCNTDQ-NEXT:    vpand %ymm3, %ymm1, %ymm4
; AVX512VPOPCNTDQ-NEXT:    vbroadcasti128 {{.*#+}} ymm5 = [0,1,1,2,1,2,2,3,1,2,2,3,2,3,3,4,0,1,1,2,1,2,2,3,1,2,2,3,2,3,3,4]
; AVX512VPOPCNTDQ-NEXT:    # ymm5 = mem[0,1,0,1]
; AVX512VPOPCNTDQ-NEXT:    vpshufb %ymm4, %ymm5, %ymm4
; AVX512VPOPCNTDQ-NEXT:    vpsrlw $4, %ymm1, %ymm1
; AVX512VPOPCNTDQ-NEXT:    vpand %ymm3, %ymm1, %ymm1
; AVX512VPOPCNTDQ-NEXT:    vpshufb %ymm1, %ymm5, %ymm1
; AVX512VPOPCNTDQ-NEXT:    vpaddb %ymm4, %ymm1, %ymm1
; AVX512VPOPCNTDQ-NEXT:    vpaddb %ymm2, %ymm0, %ymm2
; AVX512VPOPCNTDQ-NEXT:    vpandn %ymm2, %ymm0, %ymm0
; AVX512VPOPCNTDQ-NEXT:    vpand %ymm3, %ymm0, %ymm2
; AVX512VPOPCNTDQ-NEXT:    vpshufb %ymm2, %ymm5, %ymm2
; AVX512VPOPCNTDQ-NEXT:    vpsrlw $4, %ymm0, %ymm0
; AVX512VPOPCNTDQ-NEXT:    vpand %ymm3, %ymm0, %ymm0
; AVX512VPOPCNTDQ-NEXT:    vpshufb %ymm0, %ymm5, %ymm0
; AVX512VPOPCNTDQ-NEXT:    vpaddb %ymm2, %ymm0, %ymm0
; AVX512VPOPCNTDQ-NEXT:    vinserti64x4 $1, %ymm1, %zmm0, %zmm0
; AVX512VPOPCNTDQ-NEXT:    retq
;
; BITALG-LABEL: testv64i8u:
; BITALG:       # %bb.0:
; BITALG-NEXT:    vpternlogd {{.*#+}} zmm1 = -1
; BITALG-NEXT:    vpaddb %zmm1, %zmm0, %zmm1
; BITALG-NEXT:    vpandnq %zmm1, %zmm0, %zmm0
; BITALG-NEXT:    vpopcntb %zmm0, %zmm0
; BITALG-NEXT:    retq
  %out = call <64 x i8> @llvm.cttz.v64i8(<64 x i8> %in, i1 -1)
  ret <64 x i8> %out
}

declare <8 x i64> @llvm.cttz.v8i64(<8 x i64>, i1)
declare <16 x i32> @llvm.cttz.v16i32(<16 x i32>, i1)
declare <32 x i16> @llvm.cttz.v32i16(<32 x i16>, i1)
declare <64 x i8> @llvm.cttz.v64i8(<64 x i8>, i1)
