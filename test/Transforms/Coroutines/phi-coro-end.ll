; Verify that we correctly handle suspend when the coro.end block contains phi
; RUN: opt < %s -O2 -enable-coroutines -S | FileCheck %s

define i8* @f(i32 %n) {
entry:
  %id = call token @llvm.coro.id(i32 0, i8* null, i8* null, i8* null)
  %hdl = call i8* @llvm.coro.begin(token %id, i8* null)
  %0 = call i8 @llvm.coro.suspend(token none, i1 false)
  switch i8 %0, label %suspend [i8 0, label %cleanup i8 1, label %cleanup]

cleanup:
  %mem = call i8* @llvm.coro.free(i8* %hdl)
  call void @free(i8* %mem)
  br label %suspend

suspend:
  %r = phi i32 [%n, %entry], [1, %cleanup]
  call void @llvm.coro.end(i8* %hdl, i1 false)  
  call void @print(i32 %r)
  ret i8* %hdl
}

; CHECK-LABEL: @main
define i32 @main() {
entry:
  %hdl = call i8* @f(i32 4)
  call void @llvm.coro.resume(i8* %hdl)
  ret i32 0
;CHECK: call void @print(i32 4)
;CHECK: ret i32 0
}

declare i8* @llvm.coro.alloc()
declare i8* @llvm.coro.free(i8*)
declare i8  @llvm.coro.suspend(token, i1)
declare void @llvm.coro.resume(i8*)
declare void @llvm.coro.destroy(i8*)
  
declare token @llvm.coro.id(i32, i8*, i8*, i8*)
declare i8* @llvm.coro.begin(token, i8*)
declare void @llvm.coro.end(i8*, i1) 

declare noalias i8* @malloc(i32)
declare void @print(i32)
declare void @free(i8*)
