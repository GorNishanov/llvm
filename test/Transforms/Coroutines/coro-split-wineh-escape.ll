; Tests that coro-split removes cleanup code after coro.end in resume functions
; and retains it in the start function.
; RUN: opt < %s -coro-split -S | FileCheck %s

%struct.coro = type { i8 }
%struct.Param = type { i8 }
%"struct.coro::promise_type" = type { i8 }
%eh.ThrowInfo = type { i32, i32, i32, i32 }

declare dso_local void @do_something()
;declare void @"?may_throw@@YAXXZ"()
declare void @may_throw(%struct.Param* dereferenceable(1))
declare dllimport void @_CxxThrowException(i8*, %eh.ThrowInfo*)
declare i32 @__CxxFrameHandler3(...)
declare i8* @alloc_mem(i64)
declare void @param_dtor(%struct.Param*)
declare void @coro_dtor(%struct.coro* %agg.result)
declare i8* @free_mem(i8*)
declare void @llvm.coro.eh.suspend(token %eh_save)
declare token @llvm.coro.save(i8* %beg)
declare i64 @llvm.coro.size.i64()
declare i8* @llvm.coro.free(token, i8*)
declare i32 @llvm.coro.size.i32()
declare i8  @llvm.coro.suspend(token, i1)
declare void @llvm.coro.resume(i8*)
declare void @llvm.coro.destroy(i8*)

declare token @llvm.coro.id(i32, i8*, i8*, i8*)
declare i1 @llvm.coro.alloc(token)
declare i8* @llvm.coro.begin(token, i8*)
declare i1 @llvm.coro.end(i8*, i1) 

declare noalias i8* @malloc(i32)
declare void @print(i32)
declare void @free(i8*)

define void @f(%struct.coro* noalias sret %agg.result, i8 %x.coerce) "coroutine.presplit"="1" personality i8* bitcast (i32 (...)* @__CxxFrameHandler3 to i8*) {
entry:
  %x = alloca %struct.Param, align 1
  %x1 = alloca %struct.Param, align 1
  %__promise = alloca %"struct.coro::promise_type", align 1
  %coerce.dive = getelementptr inbounds %struct.Param, %struct.Param* %x, i64 0, i32 0
  store i8 %x.coerce, i8* %coerce.dive, align 1
  %0 = getelementptr inbounds %"struct.coro::promise_type", %"struct.coro::promise_type"* %__promise, i64 0, i32 0
  %id = call token @llvm.coro.id(i32 16, i8* nonnull %0, i8* bitcast (void (%struct.coro*, i8)* @f to i8*), i8* null)
  %mem = call i1 @llvm.coro.alloc(token %id)
  br i1 %mem, label %coro.alloc, label %init.suspend

coro.alloc:                                       ; preds = %entry
  %sz = tail call i64 @llvm.coro.size.i64()
  %call.i = call i8* @alloc_mem(i64 %sz) #7
  br label %init.suspend

init.suspend:                                     ; preds = %entry, %coro.alloc
  %mem_phi = phi i8* [ null, %entry ], [ %call.i, %coro.alloc ]
  %beg = call noalias nonnull i8* @llvm.coro.begin(token %id, i8* %mem_phi)
  %init_save = call token @llvm.coro.save(i8* %beg)
  %init_susp = call i8 @llvm.coro.suspend(token %init_save, i1 false)
  switch i8 %init_susp, label %coro.ret [
    i8 0, label %init.ready
    i8 1, label %init_cleanup
  ]

init.ready:                                       ; preds = %init.suspend
  invoke void @may_throw(%struct.Param* nonnull dereferenceable(1) %x1)
          to label %init_cleanup unwind label %ehcleanup

ehcleanup:                                        ; preds = %init.ready
  %cpad_eh = cleanuppad within none []
  %eh_save = call token @llvm.coro.save(i8* %beg) [ "funclet"(token %cpad_eh) ]
  cleanupret from %cpad_eh unwind label %catch.dispatch

catch.dispatch:                                   ; preds = %ehcleanup
  %catch_sw = catchswitch within none [label %catch] unwind label %eh_susp_cleanup

catch:                                            ; preds = %catch.dispatch
  %catch_pad = catchpad within %catch_sw [i8* null, i32 64, i8* null]
  call void @do_something() #7 [ "funclet"(token %catch_pad) ]
  invoke void @_CxxThrowException(i8* null, %eh.ThrowInfo* null) #13 [ "funclet"(token %catch_pad) ]
          to label %.noexc unwind label %eh_susp_cleanup

.noexc:                                           ; preds = %catch
  unreachable

eh_susp_cleanup:                                       ; preds = %catch, %catch.dispatch
  %eh_cpad = cleanuppad within none []
  call void @llvm.coro.eh.suspend(token %eh_save) [ "funclet"(token %eh_cpad) ]
  call void @param_dtor(%struct.Param* nonnull %x1) #7 [ "funclet"(token %eh_cpad) ]
  %eh_coro_free = call i8* @llvm.coro.free(token %id, i8* %beg)
  %eh_free_cond = icmp eq i8* %eh_coro_free, null
  br i1 %eh_free_cond, label %after.coro.free34, label %coro.free33

init_cleanup:                                        ; preds = %init.ready, %init.suspend
  call void @param_dtor(%struct.Param* nonnull %x1) #7
  %init_coro_free = call i8* @llvm.coro.free(token %id, i8* %beg)
  %init_free_cond = icmp eq i8* %init_coro_free, null
  br i1 %init_free_cond, label %coro.ret, label %coro.free

coro.free:                                        ; preds = %init_cleanup
  %call.i49 = call i8* @free_mem(i8* nonnull %init_coro_free) #7
  br label %coro.ret

coro.ret:                                         ; preds = %init_cleanup, %coro.free, %init.suspend
  call i1 @llvm.coro.end(i8* null, i1 false) #14
  call void @param_dtor(%struct.Param* nonnull %x) #7
  ret void

coro.free33:                                      ; preds = %eh_susp_cleanup
  %call.i47 = call i8* @free_mem(i8* nonnull %eh_coro_free) #7 [ "funclet"(token %eh_cpad) ]
  br label %after.coro.free34

after.coro.free34:                                ; preds = %eh_susp_cleanup, %coro.free33
  call i1 @llvm.coro.end(i8* null, i1 true) [ "funclet"(token %eh_cpad) ]
  call void @coro_dtor(%struct.coro* %agg.result) #7 [ "funclet"(token %eh_cpad) ]
  call void @param_dtor(%struct.Param* nonnull %x) #7 [ "funclet"(token %eh_cpad) ]
  cleanupret from %eh_cpad unwind to caller
}

; TODO: add more checks
; CHECK: define void @f(
