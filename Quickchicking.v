From Coq Require Import String List.
Import ListNotations.
From mathcomp.ssreflect
  Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq path.
From mathcomp.algebra
  Require Import ssralg ssrnum ssrint.
Set Implicit Arguments.
(* Import GRing.Theory Num.Theory. *)
(* Local Open Scope ring_scope. *)
From Tezos
  Require Import language blockchain semantics factorial.
From QuickChick Require Import QuickChick.
Import QcDefaultNotation. Import QcNotation. Open Scope qc_scope.
Require Export ExtLib.Structures.Monads.
(* Export MonadNotation. *)

(* Open Scope monad_scope. *)
Conjecture factorial_correct_eval : forall h m1 (n : nat), evaluates h (Some(factorial_program, [::Int (n%:Z)],m1)) (Some(Done,[::Int ((factorial n)%:Z)],m1)).

Inductive stupid : nat -> Prop :=
  stupidC : stupid 42.

Instance stupidDec n : Dec (stupid n).
Proof.
  constructor. unfold decidable.
  destruct (Nat.eqb n 42) eqn:H.
  - apply PeanoNat.Nat.eqb_eq in H.
    left. rewrite H; constructor.
  - right.
    unfold not.
    intros.
    inversion H0.
    subst.
    simpl in H. discriminate.
Defined.

Conjecture bla: forall n, stupid n.

Fixpoint eqdt (eqit : instr_type -> instr_type -> bool) t t' : bool :=
  match t, t' with
  | t_bool, t_bool => true
  | t_int, t_int => true
  | t_pair t3 t4,t_pair t5 t6 => (eqdt eqit t3 t5) && (eqdt eqit t4 t6)
  | t_option t1, t_option t2 => eqdt eqit t1 t2
  | t_list t1, t_list t2 => eqdt eqit t1 t2
  | t_string, t_string => true
  | t_map t1 t2, t_map t3 t4 => eqdt eqit t1 t3 && eqdt eqit t2 t4
  | t_signature, t_signature => true
  | t_key, t_key => true
  | t_tez,t_tez => true
  | t_contract t1 t2, t_contract t3 t4 => eqdt eqit t1 t3 && eqdt eqit t2 t4
  | t_unit, t_unit => true
  | t_timestamp, t_timestamp => true
  | t_quotation i1, t_quotation i2 => eqit i1 i2
  | _, _ => false (* FIXME *)
  end.
Lemma eqdt_refl : forall (eqit : instr_type -> instr_type -> bool) (H : reflexive eqit) x, eqdt eqit x x.
Proof.
  move => eqit H x.
  elim Hx : x => // [t1 H1 t2 H2|t1 H1 t2 H2|t1 H1 t2 H2] .
  - by rewrite /= H1 H2.
  - by rewrite /= H1 H2.
  - by rewrite /= H1 H2.
Qed.
Definition seq_forall {A : Type} (f : A -> bool) (l : seq A) :=
  foldr (fun x y => f x && y) true l.

Definition evaluates_max (N : nat) h s z := evaluate h N s = z.

Instance stackEq : forall (x y : stack), Dec (x = y).
Proof.
  constructor; unfold decidable.
  intros.
  apply Dec_eq_list.  intros.
  induction x0; induction y0.
    match goal with
      [ |- Dec (?c ?x = ?c ?y) ] => idtac "yay!"
    end.

Instance instrEq : forall (i1 i2 : instr), Dec (i1 = i2).
Proof. Admitted.

Instance memoryEq : forall (m1 m2 : memory), Dec (m1 = m2).
Proof. Admitted.

Instance stackEq : forall (x y : stack), Dec (x = y).
Proof. Admitted.

Hint Resolve stackEq memoryEq instrEq.

Instance evaluates_dec N h s s' : Dec (evaluates_max N h s s').
Proof.
  constructor.
  unfold evaluates_max. unfold decidable.
  set result := evaluate h N s.
  apply Dec_eq_opt. intros.
  apply Dec_eq_prod; intros.
  apply Dec_eq_prod; intros.
  all: auto.
Qed.

Instance handleMemory : Gen memory.
Proof.
Admitted.

Instance handleStack : Gen stack.
Proof.
Admitted.

Instance handleInstr : Gen instr.
Proof.
Admitted.

Check @testDec (forall x y z, evaluates x y z) _.

Conjecture foo : evaluates_max 500 42 None None.

Check step_fun.

QuickChick foo.