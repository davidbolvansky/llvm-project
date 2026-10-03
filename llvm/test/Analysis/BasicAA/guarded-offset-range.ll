; RUN: opt < %s -aa-pipeline=basic-aa -passes=aa-eval -print-all-alias-modref-info -disable-output 2>&1 | FileCheck %s

; A loop guard bounds an array access below a later field of the same object.

; CHECK-LABEL: Function: true_edge
; CHECK: NoAlias: i32* %element, i32* %field
define void @true_edge(ptr %base) {
entry:
  br label %header
header:
  %i = phi i32 [ 0, %entry ], [ %next, %body ]
  %cmp = icmp ult i32 %i, 4
  br i1 %cmp, label %body, label %exit
body:
  %idx = zext i32 %i to i64
  %element = getelementptr inbounds i32, ptr %base, i64 %idx
  %field = getelementptr inbounds i32, ptr %base, i64 4
  load i32, ptr %element
  store i32 0, ptr %field
  %next = add nuw i32 %i, 1
  br label %header
exit:
  ret void
}

; CHECK-LABEL: Function: false_edge
; CHECK: NoAlias: i32* %element, i32* %field
define void @false_edge(ptr %base) {
entry:
  br label %header
header:
  %i = phi i32 [ 0, %entry ], [ %next, %body ]
  %cmp = icmp uge i32 %i, 4
  br i1 %cmp, label %exit, label %body
body:
  %idx = zext i32 %i to i64
  %element = getelementptr inbounds i32, ptr %base, i64 %idx
  %field = getelementptr inbounds i32, ptr %base, i64 4
  load i32, ptr %element
  store i32 0, ptr %field
  %next = add nuw i32 %i, 1
  br label %header
exit:
  ret void
}

; CHECK-LABEL: Function: same_successor
; CHECK: MayAlias: i32* %element, i32* %field
define void @same_successor(ptr %base) {
entry:
  br label %header
header:
  %i = phi i32 [ 0, %entry ], [ %next, %body ]
  %cmp = icmp ult i32 %i, 4
  br i1 %cmp, label %body, label %body
body:
  %idx = zext i32 %i to i64
  %element = getelementptr inbounds i32, ptr %base, i64 %idx
  %field = getelementptr inbounds i32, ptr %base, i64 4
  load i32, ptr %element
  store i32 0, ptr %field
  %next = add nuw i32 %i, 1
  br label %header
exit:
  ret void
}

; CHECK-LABEL: Function: nonadjacent_guard
; CHECK: NoAlias: i32* %element, i32* %field
define void @nonadjacent_guard(ptr %base, i32 %index, i1 %choice) {
entry:
  %cmp = icmp ult i32 %index, 4
  br i1 %cmp, label %split, label %exit
split:
  br i1 %choice, label %left, label %right
left:
  br label %body
right:
  br label %body
body:
  %idx = zext i32 %index to i64
  %element = getelementptr i32, ptr %base, i64 %idx
  %field = getelementptr i32, ptr %base, i64 4
  load i32, ptr %element
  store i32 0, ptr %field
  br label %exit
exit:
  ret void
}

; The unconstrained path prevents the comparison from bounding the access.
; CHECK-LABEL: Function: nondominating_guard
; CHECK: MayAlias: i32* %element, i32* %field
define void @nondominating_guard(ptr %base, i32 %index, i1 %choice) {
entry:
  br i1 %choice, label %check, label %body
check:
  %cmp = icmp ult i32 %index, 4
  br i1 %cmp, label %body, label %exit
body:
  %idx = zext i32 %index to i64
  %element = getelementptr i32, ptr %base, i64 %idx
  %field = getelementptr i32, ptr %base, i64 4
  load i32, ptr %element
  store i32 0, ptr %field
  br label %exit
exit:
  ret void
}
