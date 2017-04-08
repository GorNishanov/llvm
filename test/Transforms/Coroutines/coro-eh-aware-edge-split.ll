; Check that we can handle edge splits leading into a landingpad
; RUN: opt < %s -coro-split -S | FileCheck %s

target datalayout = "e-m:e-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

%"struct.coro::promise_type" = type { i8 }

; Function Attrs: uwtable
define void @f(i1 %cond) "coroutine.presplit"="1" personality i32 0 {
entry:
  %id = call token @llvm.coro.id(i32 16, i8* null, i8* null, i8* null)
  %size = tail call i64 @llvm.coro.size.i64()
  %alloc = call i8* @malloc(i64 %size)
  %hdl = call i8* @llvm.coro.begin(token %id, i8* %alloc)
  %sp = call i8 @llvm.coro.suspend(token none, i1 false)
  switch i8 %sp, label %coro.ret [
    i8 0, label %resume
    i8 1, label %cleanup
  ]

resume:
  br i1 %cond, label %invoke1, label %invoke2

invoke1:
  invoke void @may_throw1()
          to label %unreach unwind label %pad.with.phi
invoke2:
  invoke void @may_throw2()
          to label %unreach unwind label %pad.with.phi

pad.with.phi:
  %val = phi i32 [ 0, %invoke1 ], [ 1, %invoke2 ]
  %lp = landingpad { i8*, i32 }
          catch i8* null
  %exn = extractvalue { i8*, i32 } %lp, 0
  call i8* @__cxa_begin_catch(i8* %exn)
  call void @use_val(i32 %val)
  call void @__cxa_end_catch()
  br label %cleanup

cleanup:                                        ; preds = %invoke.cont15, %if.else, %if.then, %ehcleanup21, %init.suspend
  %mem = call i8* @llvm.coro.free(token %id, i8* %hdl)
  call void @free(i8* %mem)
  br label %coro.ret

coro.ret:
  call i1 @llvm.coro.end(i8* null, i1 false)
  ret void

unreach:
  unreachable
}

; See if we extracted resume part and dealt with phi in landing pad

; CHECK-LABEL: define internal fastcc void @f.resume(
; CHECK: pad.with.phi.from.invoke2:
; CHECK:   %0 = landingpad { i8*, i32 }
; CHECK:           catch i8* null
; CHECK:   br label %pad.with.phi

; CHECK: pad.with.phi.from.invoke1:
; CHECK:   %1 = landingpad { i8*, i32 }
; CHECK:           catch i8* null
; CHECK:   br label %pad.with.phi

; CHECK: pad.with.phi:
; CHECK:   %val = phi i32 [ 0, %pad.with.phi.from.invoke1 ], [ 1, %pad.with.phi.from.invoke2 ]
; CHECK:   %lp = phi { i8*, i32 } [ %0, %pad.with.phi.from.invoke2 ], [ %1, %pad.with.phi.from.invoke1 ]
; CHECK:   %exn = extractvalue { i8*, i32 } %lp, 0
; CHECK:   call i8* @__cxa_begin_catch(i8* %exn)
; CHECK:   call void @use_val(i32 %val)
; CHECK:   call void @__cxa_end_catch()
; CHECK:   call void @free(i8* %vFrame)
; CHECK:   ret void

; Function Attrs: uwtable
define void @g(i1 %cond) "coroutine.presplit"="1" personality i32 0 {
entry:
  %id = call token @llvm.coro.id(i32 16, i8* null, i8* null, i8* null)
  %size = tail call i64 @llvm.coro.size.i64()
  %alloc = call i8* @malloc(i64 %size)
  %hdl = call i8* @llvm.coro.begin(token %id, i8* %alloc)
  %sp = call i8 @llvm.coro.suspend(token none, i1 false)
  switch i8 %sp, label %coro.ret [
    i8 0, label %resume
    i8 1, label %cleanup
  ]

resume:
  br i1 %cond, label %invoke1, label %invoke2

invoke1:
  invoke void @may_throw1()
          to label %unreach unwind label %pad.with.phi
invoke2:
  invoke void @may_throw2()
          to label %unreach unwind label %pad.with.phi

pad.with.phi:
  %val = phi i32 [ 0, %invoke1 ], [ 1, %invoke2 ]
  %tok = cleanuppad within none []
  call void @use_val(i32 %val)
  cleanupret from %tok unwind to caller

cleanup:                                        ; preds = %invoke.cont15, %if.else, %if.then, %ehcleanup21, %init.suspend
  %mem = call i8* @llvm.coro.free(token %id, i8* %hdl)
  call void @free(i8* %mem)
  br label %coro.ret

coro.ret:
  call i1 @llvm.coro.end(i8* null, i1 false)
  ret void

unreach:
  unreachable
}


; Function Attrs: argmemonly nounwind readonly
declare token @llvm.coro.id(i32, i8* readnone, i8* nocapture readonly, i8*)
declare noalias i8* @malloc(i64)
declare i64 @llvm.coro.size.i64()
declare i8* @llvm.coro.begin(token, i8* writeonly)

; Function Attrs: nounwind
declare token @llvm.coro.save(i8*)
declare i8 @llvm.coro.suspend(token, i1)

; Function Attrs: argmemonly nounwind
declare void @may_throw1()
declare void @may_throw2()

declare i8* @__cxa_begin_catch(i8*)

declare void @use_val(i32)
declare void @__cxa_end_catch()

; Function Attrs: nounwind
declare i1 @llvm.coro.end(i8*, i1)
declare void @free(i8*)
declare i8* @llvm.coro.free(token, i8* nocapture readonly)
