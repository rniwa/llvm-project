; NOTE: Assertions have been autogenerated by utils/update_llc_test_checks.py UTC_ARGS: --version 5
; RUN: llc -mtriple=riscv32-unknown-elf -mattr=+zba %s -o - | FileCheck %s

declare i32 @callee1(i32 noundef)
declare i32 @callee2(i32 noundef, i32 noundef)
declare i32 @callee(i32 noundef, i32 noundef, i32 noundef, i32 noundef)

define void @t1(i32 noundef %a, i32 noundef %b, i32 noundef %c, i32 noundef %d) #0 {
; CHECK-LABEL: t1:
; CHECK:       # %bb.0: # %entry
; CHECK-NEXT:    slli a4, a0, 2
; CHECK-NEXT:    addi a4, a4, 45
; CHECK-NEXT:    add a1, a4, a1
; CHECK-NEXT:    add a2, a4, a2
; CHECK-NEXT:    sh2add a3, a0, a3
; CHECK-NEXT:    mv a0, a1
; CHECK-NEXT:    tail callee
entry:
  %shl = shl i32 %a, 2
  %add = add nsw i32 %shl, 45
  %add1 = add nsw i32 %add, %b
  %add3 = add nsw i32 %add, %c
  %add5 = add nsw i32 %shl, %d
  %call = tail call i32 @callee(i32 noundef %add1, i32 noundef %add1, i32 noundef %add3, i32 noundef %add5)
  ret void
}

define void @t2(i32 noundef %a, i32 noundef %b, i32 noundef %c) #0 {
; CHECK-LABEL: t2:
; CHECK:       # %bb.0: # %entry
; CHECK-NEXT:    slli a0, a0, 2
; CHECK-NEXT:    addi a5, a0, 42
; CHECK-NEXT:    add a4, a5, a1
; CHECK-NEXT:    add a3, a5, a2
; CHECK-NEXT:    mv a1, a5
; CHECK-NEXT:    mv a2, a4
; CHECK-NEXT:    tail callee
entry:
  %shl = shl i32 %a, 2
  %add = add nsw i32 %shl, 42
  %add4 = add nsw i32 %add, %b
  %add7 = add nsw i32 %add, %c
  %call = tail call i32 @callee(i32 noundef %shl, i32 noundef %add, i32 noundef %add4, i32 noundef %add7)
  ret void
}

define void @t3(i32 noundef %a, i32 noundef %b, i32 noundef %c, i32 noundef %d, i32 noundef %e) #0 {
; CHECK-LABEL: t3:
; CHECK:       # %bb.0: # %entry
; CHECK-NEXT:    slli a0, a0, 2
; CHECK-NEXT:    addi a5, a0, 42
; CHECK-NEXT:    add a0, a5, a1
; CHECK-NEXT:    add a1, a5, a2
; CHECK-NEXT:    add a2, a5, a3
; CHECK-NEXT:    add a3, a5, a4
; CHECK-NEXT:    tail callee
entry:
  %shl = shl i32 %a, 2
  %add = add nsw i32 %shl, 42
  %add1 = add nsw i32 %add, %b
  %add2 = add nsw i32 %add, %c
  %add3 = add nsw i32 %add, %d
  %add4 = add nsw i32 %add, %e
  %call = tail call i32 @callee(i32 noundef %add1, i32 noundef %add2, i32 noundef %add3, i32 noundef %add4)
  ret void
}

define void @t4(i32 noundef %a, i32 noundef %b) #0 {
; CHECK-LABEL: t4:
; CHECK:       # %bb.0: # %entry
; CHECK-NEXT:    sh2add a0, a0, a1
; CHECK-NEXT:    addi a0, a0, 42
; CHECK-NEXT:    tail callee1
entry:
  %shl = shl i32 %a, 2
  %add = add nsw i32 %shl, 42
  %add1 = add nsw i32 %add, %b
  %call = tail call i32 @callee1(i32 noundef %add1)
  ret void
}

define void @t5(i32 noundef %a, i32 noundef %b, i32 noundef %c) #0 {
; CHECK-LABEL: t5:
; CHECK:       # %bb.0: # %entry
; CHECK-NEXT:    sh2add a2, a0, a2
; CHECK-NEXT:    sh2add a0, a0, a1
; CHECK-NEXT:    addi a0, a0, 42
; CHECK-NEXT:    addi a1, a2, 42
; CHECK-NEXT:    tail callee2
entry:
  %shl = shl i32 %a, 2
  %add = add nsw i32 %shl, 42
  %add1 = add nsw i32 %add, %b
  %add2 = add nsw i32 %add, %c
  %call = tail call i32 @callee2(i32 noundef %add1, i32 noundef %add2)
  ret void
}

define void @t6(i32 noundef %a, i32 noundef %b) #0 {
; CHECK-LABEL: t6:
; CHECK:       # %bb.0: # %entry
; CHECK-NEXT:    slli a2, a0, 2
; CHECK-NEXT:    sh2add a0, a0, a1
; CHECK-NEXT:    addi a0, a0, 42
; CHECK-NEXT:    mv a1, a2
; CHECK-NEXT:    mv a3, a2
; CHECK-NEXT:    tail callee
entry:
  %shl = shl i32 %a, 2
  %add = add nsw i32 %shl, 42
  %add1 = add nsw i32 %add, %b
  %call = tail call i32 @callee(i32 noundef %add1, i32 noundef %shl, i32 noundef %shl, i32 noundef %shl)
  ret void
}

define void @t7(i32 noundef %a, i32 noundef %b) #0 {
; CHECK-LABEL: t7:
; CHECK:       # %bb.0: # %entry
; CHECK-NEXT:    slli a0, a0, 2
; CHECK-NEXT:    addi a2, a0, 42
; CHECK-NEXT:    add a0, a2, a1
; CHECK-NEXT:    mv a1, a2
; CHECK-NEXT:    mv a3, a2
; CHECK-NEXT:    tail callee
entry:
  %shl = shl i32 %a, 2
  %add = add nsw i32 %shl, 42
  %add1 = add nsw i32 %add, %b
  %call = tail call i32 @callee(i32 noundef %add1, i32 noundef %add, i32 noundef %add, i32 noundef %add)
  ret void
}

define void @t8(i32 noundef %a, i32 noundef %b, i32 noundef %c, i32 noundef %d) #0 {
; CHECK-LABEL: t8:
; CHECK:       # %bb.0: # %entry
; CHECK-NEXT:    lui a4, 1
; CHECK-NEXT:    addi a4, a4, 1307
; CHECK-NEXT:    sh3add a4, a0, a4
; CHECK-NEXT:    add a1, a4, a1
; CHECK-NEXT:    add a2, a4, a2
; CHECK-NEXT:    sh3add a3, a0, a3
; CHECK-NEXT:    mv a0, a1
; CHECK-NEXT:    tail callee
entry:
  %shl = shl i32 %a, 3
  %add = add nsw i32 %shl, 5403
  %add1 = add nsw i32 %add, %b
  %add3 = add nsw i32 %add, %c
  %add5 = add nsw i32 %shl, %d
  %call = tail call i32 @callee(i32 noundef %add1, i32 noundef %add1, i32 noundef %add3, i32 noundef %add5)
  ret void
}

define void @t9(i32 noundef %a, i32 noundef %b, i32 noundef %c, i32 noundef %d) #0 {
; CHECK-LABEL: t9:
; CHECK:       # %bb.0: # %entry
; CHECK-NEXT:    slli a4, a0, 2
; CHECK-NEXT:    addi a4, a4, -42
; CHECK-NEXT:    add a1, a4, a1
; CHECK-NEXT:    add a2, a4, a2
; CHECK-NEXT:    sh2add a3, a0, a3
; CHECK-NEXT:    mv a0, a1
; CHECK-NEXT:    tail callee
entry:
  %shl = shl i32 %a, 2
  %add = add nsw i32 %shl, -42
  %add1 = add nsw i32 %add, %b
  %add3 = add nsw i32 %add, %c
  %add5 = add nsw i32 %shl, %d
  %call = tail call i32 @callee(i32 noundef %add1, i32 noundef %add1, i32 noundef %add3, i32 noundef %add5)
  ret void
}

define void @t10(i32 noundef %a, i32 noundef %b, i32 noundef %c, i32 noundef %d) #0 {
; CHECK-LABEL: t10:
; CHECK:       # %bb.0: # %entry
; CHECK-NEXT:    tail callee
entry:
  %shl = shl i32 %a, -2
  %add = add nsw i32 %shl, 42
  %add1 = add nsw i32 %add, %b
  %add3 = add nsw i32 %add, %c
  %add5 = add nsw i32 %shl, %d
  %call = tail call i32 @callee(i32 noundef %add1, i32 noundef %add1, i32 noundef %add3, i32 noundef %add5)
  ret void
}

attributes #0 = { nounwind optsize }
