; Third example from Doc/Coroutines.rst (two suspend points)
; RUN: opt < %s -O3 -S | FileCheck %s

define i8* @f(i32 %n) {
entry:
  %id = call token @llvm.coro.id()
  %size = call i32 @llvm.coro.size.i32()
  %alloc = call i8* @malloc(i32 %size)
  %hdl = call noalias i8* @llvm.coro.begin(token %id, i8* %alloc, i32 0, i8* null, i8* null)
  br label %loop
loop:
  %n.val = phi i32 [ %n, %entry ], [ %inc, %loop.resume ]
  call void @print(i32 %n.val) #4
  %0 = call i8 @llvm.coro.suspend(token none, i1 false)
  switch i8 %0, label %suspend [i8 0, label %loop.resume
                                i8 1, label %cleanup]
loop.resume:
  %inc = add nsw i32 %n.val, 1
  %sub = xor i32 %n.val, -1
  call void @print(i32 %sub)
  %1 = call i8 @llvm.coro.suspend(token none, i1 false)
  switch i8 %1, label %suspend [i8 0, label %loop
                                i8 1, label %cleanup]
cleanup:
  %mem = call i8* @llvm.coro.free(i8* %hdl)
  call void @free(i8* %mem)
  br label %suspend
suspend:
  call void @llvm.coro.end(i8* %hdl, i1 false)
  ret i8* %hdl
}

; CHECK: %f.Frame = type { void (%f.Frame*)*, void (%f.Frame*)*, i8, i32 }

; CHECK-LABEL: @main
define i32 @main() {
entry:
  %hdl = call i8* @f(i32 4)
  call void @llvm.coro.resume(i8* %hdl)
  call void @llvm.coro.resume(i8* %hdl)
  call void @llvm.coro.destroy(i8* %hdl)
  ret i32 0
; CHECK:      call void @print(i32 4)
; CHECK-NEXT: call void @print(i32 -5)
; CHECK-NEXT: call void @print(i32 5)
; CHECK:      ret i32 0
}

declare i8* @malloc(i32)
declare void @free(i8*)
declare void @print(i32)

declare token @llvm.coro.id()
declare i1 @llvm.coro.alloc(token)
declare i32 @llvm.coro.size.i32()
declare i8* @llvm.coro.begin(token, i8*, i32, i8*, i8*)
declare i8 @llvm.coro.suspend(token, i1)
declare i8* @llvm.coro.free(i8*)
declare void @llvm.coro.end(i8*, i1)

declare void @llvm.coro.resume(i8*)
declare void @llvm.coro.destroy(i8*)
