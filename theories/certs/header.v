From mathcomp Require Import ssreflect ssrbool ssrfun seq choice.
From Coq Require Import (* Znat BinIntDef *) Uint63.
Local Open Scope uint63_scope.

Set Implicit Arguments.
Unset Strict Implicit. 
Unset Printing Implicit Defensive.

Require Import int_seq present rewcert fastcert criteria batchchecker wfsizelexi.
