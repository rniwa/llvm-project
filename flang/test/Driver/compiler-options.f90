! RUN: %flang -S -emit-llvm -flang-deprecated-no-hlfir -o - %s | FileCheck %s
! Test communication of COMPILER_OPTIONS from flang to flang -fc1.
! CHECK: [[OPTSVAR:@_QQclX[0-9a-f]+]] = {{[a-z]+}} constant [[[OPTSLEN:[0-9]+]] x i8] c"{{.*}}flang{{(\.exe)?}} {{.*}}-S -emit-llvm -flang-deprecated-no-hlfir -o - {{.*}}compiler-options.f90"
program main
    use ISO_FORTRAN_ENV, only: compiler_options
    implicit none
    character (len = :), allocatable :: v
! CHECK: call void @llvm.memmove.p0.p0.i64(ptr %{{[0-9]+}}, ptr [[OPTSVAR]], i64 [[OPTSLEN]], i1 false)
    v = compiler_options()
    print *, v
    deallocate(v)
    close(1)
end program main
