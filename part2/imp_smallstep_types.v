Require Import Coq.Arith.Arith.
Require Import Coq.Arith.EqNat.
Require Import Coq.omega.Omega.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Bool.Bool.
Require Import Coq.Logic.FunctionalExtensionality.

(** * SfLib: Software Foundations Library *)

(* $Date: 2013-01-16 22:29:57 -0500 (Wed, 16 Jan 2013) $ *)

(** Here we collect together several useful definitions and theorems
    from Basics.v, List.v, Poly.v, Ind.v, and Logic.v that are not
    already in the Coq standard library.  From now on we can [Import]
    or [Export] this file, instead of cluttering our environment with
    all the examples and false starts in those files. *)

(** * From the Coq Standard Library *)

Require Omega.   (* needed for using the [omega] tactic *)
Require Export Bool.
Require Export List.
Require Export Arith.
Require Export Arith.EqNat.  (* Contains [beq_nat], among other things *)

(** * From Basics.v *)

Definition admit {T: Type} : T.  Admitted.

Require String. Open Scope string_scope.

Ltac move_to_top x :=
  match reverse goal with
  | H : _ |- _ => try move x after H
  end.

Tactic Notation "assert_eq" ident(x) constr(v) :=
  let H := fresh in
  assert (x = v) as H by reflexivity;
  clear H.

Tactic Notation "Case_aux" ident(x) constr(name) :=
  first [
    set (x := name); move_to_top x
  | assert_eq x name; move_to_top x
  | fail 1 "because we are working on a different case" ].

Tactic Notation "Case" constr(name) := Case_aux Case name.
Tactic Notation "SCase" constr(name) := Case_aux SCase name.
Tactic Notation "SSCase" constr(name) := Case_aux SSCase name.
Tactic Notation "SSSCase" constr(name) := Case_aux SSSCase name.
Tactic Notation "SSSSCase" constr(name) := Case_aux SSSSCase name.
Tactic Notation "SSSSSCase" constr(name) := Case_aux SSSSSCase name.
Tactic Notation "SSSSSSCase" constr(name) := Case_aux SSSSSSCase name.
Tactic Notation "SSSSSSSCase" constr(name) := Case_aux SSSSSSSCase name.

Fixpoint ble_nat (n m : nat) : bool :=
  match n with
  | O => true
  | S n' =>
      match m with
      | O => false
      | S m' => ble_nat n' m'
      end
  end.

Theorem andb_true_elim1 : forall b c,
  andb b c = true -> b = true.
Proof.
  intros b c H.
  destruct b.
  Case "b = true".
    reflexivity.
  Case "b = false".
    rewrite <- H. reflexivity.  Qed.

Theorem andb_true_elim2 : forall b c,
  andb b c = true -> c = true.
Proof.
(* An exercise in Basics.v *)
Admitted.

Theorem beq_nat_sym : forall (n m : nat),
  beq_nat n m = beq_nat m n.
(* An exercise in Lists.v *)
Admitted.

(* From Poly.v *)

Notation "[ ]" := nil.
Notation "[ x , .. , y ]" := (cons x .. (cons y []) ..).
Notation "x ++ y" := (app x y) 
                     (at level 60, right associativity).

(** * From Props.v *)

Inductive ev : nat -> Prop :=
  | ev_0 : ev O
  | ev_SS : forall n:nat, ev n -> ev (S (S n)).

(** * From Logic.v *)

Theorem andb_true : forall b c,
  andb b c = true -> b = true /\ c = true.
Proof.
  intros b c H.
  destruct b.
    destruct c.
      apply conj. reflexivity. reflexivity.
      inversion H.
    inversion H.  Qed.

Theorem not_eq_beq_false : forall n n' : nat,
     n <> n' ->
     beq_nat n n' = false.
Proof. 
(* An exercise in Logic.v *)
Admitted.

Theorem ex_falso_quodlibet : forall (P:Prop),
  False -> P.
Proof.
  intros P contra.
  inversion contra.  Qed.

Theorem ev_not_ev_S : forall n,
  ev n -> ~ ev (S n).
Proof. 
(* An exercise in Logic.v *)
Admitted.

Theorem ble_nat_true : forall n m,
  ble_nat n m = true -> n <= m.
(* An exercise in Logic.v *)
Admitted.

Theorem ble_nat_false : forall n m,
  ble_nat n m = false -> ~(n <= m).
(* An exercise in Logic.v *)
Admitted.

Inductive appears_in (n : nat) : list nat -> Prop :=
| ai_here : forall l, appears_in n (n::l)
| ai_later : forall m l, appears_in n l -> appears_in n (m::l).

Inductive next_nat (n:nat) : nat -> Prop :=
  | nn : next_nat n (S n).

Inductive total_relation : nat -> nat -> Prop :=
  tot : forall n m : nat, total_relation n m.

Inductive empty_relation : nat -> nat -> Prop := .

(** * From Later Files *)

Definition relation (X:Type) := X -> X -> Prop.

Definition deterministic {X: Type} (R: relation X) :=
  forall x y1 y2 : X, R x y1 -> R x y2 -> y1 = y2. 

Inductive multi (X:Type) (R: relation X) 
                            : X -> X -> Prop :=
  | multi_refl  : forall (x : X),
                 multi X R x x
  | multi_step : forall (x y z : X),
                    R x y ->
                    multi X R y z ->
                    multi X R x z.
Implicit Arguments multi [[X]]. 

Tactic Notation "multi_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "multi_refl" | Case_aux c "multi_step" ].

Theorem multi_R : forall (X:Type) (R:relation X) (x y : X),
       R x y -> multi R x y.
Proof.
  intros X R x y r.
  apply multi_step with y. apply r. apply multi_refl.   Qed.

Theorem multi_trans :
  forall (X:Type) (R: relation X) (x y z : X),
      multi R x y  ->
      multi R y z ->
      multi R x z.
Proof.
  (* FILL IN HERE *) Admitted.

(* Identifiers and polymorphic partial maps. *)

Inductive id : Type := 
  Id : nat -> id.

Definition beq_id id1 id2 :=
  match (id1, id2) with
    (Id n1, Id n2) => beq_nat n1 n2
  end.

Theorem beq_id_refl : forall i,
  true = beq_id i i.
Proof.
  intros. destruct i.
  apply beq_nat_refl.  Qed.

Theorem beq_id_eq : forall i1 i2,
  true = beq_id i1 i2 -> i1 = i2.
Proof.
  intros i1 i2 H.
  destruct i1. destruct i2.
  apply beq_nat_eq in H. subst.
  reflexivity.  Qed.

Theorem beq_id_false_not_eq : forall i1 i2,
  beq_id i1 i2 = false -> i1 <> i2.
Proof.
  intros i1 i2 H.
  destruct i1. destruct i2.
  apply beq_nat_false in H.
  intros C. apply H. inversion C. reflexivity.  Qed.

Theorem not_eq_beq_id_false : forall i1 i2,
  i1 <> i2 -> beq_id i1 i2 = false.
Proof.
  intros i1 i2 H.
  destruct i1. destruct i2.
  assert (n <> n0).
    intros C. subst. apply H. reflexivity.
  apply not_eq_beq_false. assumption.  Qed.

Theorem beq_id_sym: forall i1 i2,
  beq_id i1 i2 = beq_id i2 i1.
Proof.
  intros i1 i2. destruct i1. destruct i2. apply beq_nat_sym. Qed.


Definition partial_map (A:Type) := id -> option A.

Definition empty {A:Type} : partial_map A := (fun _ => None). 

Definition extend {A:Type} (Gamma : partial_map A) (x:id) (T : A) :=
  fun x' => if beq_id x x' then Some T else Gamma x'.

Lemma extend_eq : forall A (ctxt: partial_map A) x T,
  (extend ctxt x T) x = Some T.
Proof.
  intros. unfold extend. rewrite <- beq_id_refl. auto.
Qed.

Lemma extend_neq : forall A (ctxt: partial_map A) x1 T x2,
  beq_id x2 x1 = false ->
  (extend ctxt x2 T) x1 = ctxt x1.
Proof.
  intros. unfold extend. rewrite H. auto.
Qed.

Lemma extend_shadow : forall A (ctxt: partial_map A) t1 t2 x1 x2,
  extend (extend ctxt x2 t1) x2 t2 x1 = extend ctxt x2 t2 x1.
Proof with auto.
  intros. unfold extend. destruct (beq_id x2 x1)...
Qed.

(** * Some useful tactics *)

Tactic Notation "solve_by_inversion_step" tactic(t) :=  
  match goal with  
  | H : _ |- _ => solve [ inversion H; subst; t ] 
  end
  || fail "because the goal is not solvable by inversion.".

Tactic Notation "solve" "by" "inversion" "1" :=
  solve_by_inversion_step idtac.
Tactic Notation "solve" "by" "inversion" "2" :=
  solve_by_inversion_step (solve by inversion 1).
Tactic Notation "solve" "by" "inversion" "3" :=
  solve_by_inversion_step (solve by inversion 2).
Tactic Notation "solve" "by" "inversion" :=
  solve by inversion 1.

(*------------------------EXAMPLE 1-----------------------*)

Inductive aexp : Type :=
  | ANum : nat -> aexp
  | APlus : aexp -> aexp -> aexp
  | AMinus : aexp -> aexp -> aexp
  | AMult : aexp -> aexp -> aexp.

Tactic Notation "aexp_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "ANum" | Case_aux c "APlus"
  | Case_aux c "AMinus" | Case_aux c "AMult" ].


Fixpoint aeval (a : aexp) : nat :=
  match a with
  | ANum n => n
  | APlus a1 a2 => (aeval a1) + (aeval a2)
  | AMinus a1 a2 => (aeval a1) - (aeval a2)
  | AMult a1 a2 => (aeval a1) * (aeval a2)
  end.

Inductive bexp : Type :=
  | BTrue : bexp
  | BFalse : bexp
  | BEq : aexp -> aexp -> bexp
  | BLe : aexp -> aexp -> bexp
  | BNot : bexp -> bexp
  | BAnd : bexp -> bexp -> bexp.

Fixpoint beval (b : bexp) : bool :=
  match b with
  | BTrue => true
  | BFalse => false
  | BEq a1 a2 => beq_nat (aeval a1) (aeval a2)
  | BLe a1 a2 => ble_nat (aeval a1) (aeval a2)
  | BNot b1 => negb (beval b1)
  | BAnd b1 b2 => andb (beval b1) (beval b2)
  end.

Example test_aeval1:
  aeval (APlus (ANum 2) (ANum 2)) = 4.
Proof. reflexivity. Qed.

Fixpoint optimize_0plus (a:aexp) : aexp :=
  match a with
  | ANum n =>
      ANum n
  | APlus (ANum 0) e2 =>
      optimize_0plus e2
  | APlus e1 e2 =>
      APlus (optimize_0plus e1) (optimize_0plus e2)
  | AMinus e1 e2 =>
      AMinus (optimize_0plus e1) (optimize_0plus e2)
  | AMult e1 e2 =>
      AMult (optimize_0plus e1) (optimize_0plus e2)
  end.

Example test_optimize_0plus:
  optimize_0plus (APlus (ANum 2)
                        (APlus (ANum 0)
                               (APlus (ANum 0) (ANum 1))))
  = APlus (ANum 2) (ANum 1).
Proof. reflexivity. Qed.

Theorem optimize_0plus_sound: forall a:aexp,
  aeval (optimize_0plus a) = aeval a.
Proof.
  intros a. induction a.
  Case "ANum". simpl. reflexivity.
  Case "APlus". destruct a1.
    SCase "a1 = ANum n". destruct n.
      SSCase "n = 0". simpl. apply IHa2.
      SSCase "n ≠ 0". simpl. rewrite IHa2. reflexivity.
    SCase "a1 = APlus a1_1 a1_2".
      simpl. simpl in IHa1. rewrite IHa1.
      rewrite IHa2. reflexivity.
    SCase "a1 = AMinus a1_1 a1_2".
      simpl. simpl in IHa1. rewrite IHa1.
      rewrite IHa2. reflexivity.
    SCase "a1 = AMult a1_1 a1_2".
      simpl. simpl in IHa1. rewrite IHa1.
      rewrite IHa2. reflexivity.
  Case "AMinus".
    simpl. rewrite IHa1. rewrite IHa2. reflexivity.
  Case "AMult".
    simpl. rewrite IHa1. rewrite IHa2. reflexivity. 
    Qed.


(* -----------------------------EXAMPLE 2 -----------------------------*)

Definition state := id -> nat.

Definition empty_state : state :=
  fun _ => 0.

Theorem eq_id_dec : forall id1 id2 : id, {id1 = id2} + {id1 <> id2}.
Proof.
   intros id1 id2.
   destruct id1 as [n1]. destruct id2 as [n2].
   destruct (eq_nat_dec n1 n2) as [Heq | Hneq].
   Case "n1 = n2".
     left. rewrite Heq. reflexivity.
   Case "n1 ≠ n2".
     right. intros contra. inversion contra. apply Hneq. apply H0.
Defined.


Definition update (st : state) (x : id) (n : nat) : state :=
  fun x' => if eq_id_dec x x' then n else st x'.

Inductive aexp2 : Type :=
  | ANum2 : nat -> aexp2
  | AId2 : id -> aexp2 (* <----- NEW *)
  | APlus2 : aexp2 -> aexp2 -> aexp2
  | AMinus2 : aexp2 -> aexp2 -> aexp2
  | AMult2 : aexp2 -> aexp2 -> aexp2.

Tactic Notation "aexp_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "ANum" | Case_aux c "AId" | Case_aux c "APlus"
  | Case_aux c "AMinus" | Case_aux c "AMult" ].

Fixpoint aeval2 (st: state)(a : aexp2) : nat :=
  match a with
  | ANum2 n => n
  | AId2 x => st x (* <----- NEW *)
  | APlus2 a1 a2 => (aeval2 st a1) + (aeval2 st a2)
  | AMinus2 a1 a2 => (aeval2 st a1) - (aeval2 st a2)
  | AMult2 a1 a2 => (aeval2 st a1) * (aeval2 st a2)
  end.

Inductive bexp2 : Type :=
  | BTrue2 : bexp2
  | BFalse2 : bexp2
  | BEq2 : aexp2 -> aexp2 -> bexp2
  | BLe2 : aexp2 -> aexp2 -> bexp2
  | BNot2 : bexp2 -> bexp2
  | BAnd2 : bexp2 -> bexp2 -> bexp2.

Fixpoint beval2 (st : state) (b : bexp2) : bool :=
  match b with
  | BTrue2 => true
  | BFalse2 => false
  | BEq2 a1 a2 => beq_nat (aeval2 st a1) (aeval2 st a2)
  | BLe2 a1 a2 => ble_nat (aeval2 st a1) (aeval2 st a2)
  | BNot2 b1 => negb (beval2 st b1)
  | BAnd2 b1 b2 => andb (beval2 st b1) (beval2 st b2)
  end.


Inductive com : Type :=
  | CSkip : com
  | CAss : id -> aexp2 -> com
  | CSeq : com -> com -> com
  | CIf : bexp2 -> com -> com -> com
  | CWhile : bexp2 -> com -> com.


Tactic Notation "com_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "SKIP" | Case_aux c "::=" | Case_aux c ";;"
  | Case_aux c "IFB" | Case_aux c "WHILE" ].

Notation "'SKIP'" :=
  CSkip.
Notation "x '::=' a" :=
  (CAss x a) (at level 60).
Notation "c1 ;; c2" :=
  (CSeq c1 c2) (at level 80, right associativity).
Notation "'WHILE' b 'DO' c 'END'" :=
  (CWhile b c) (at level 80, right associativity).
Notation "'IFB' c1 'THEN' c2 'ELSE' c3 'FI'" :=
  (CIf c1 c2 c3) (at level 80, right associativity).

Reserved Notation "c1 '/' st '||' st'" (at level 40, st at level 39).

Inductive ceval : com -> state -> state -> Prop :=
  | E_Skip : forall st: state,
      SKIP / st || st
  | E_Ass : forall (st:state) (x:id) (a1: aexp2) (n:nat),
      aeval2 st a1 = n ->
      (x ::= a1) / st || (update st x n)
  | E_Seq : forall (c1 c2:com) (st st' st'':state),
      c1 / st || st' ->
      c2 / st' || st'' ->
      (c1 ;; c2) / st || st''
  | E_IfTrue : forall (st st':state) (b:bexp2) (c1 c2:com),
      beval2 st b = true ->
      c1 / st || st' ->
      (IFB b THEN c1 ELSE c2 FI) / st || st'
  | E_IfFalse : forall (st st':state) (b:bexp2) (c1 c2:com),
      beval2 st b = false ->
      c2 / st || st' ->
      (IFB b THEN c1 ELSE c2 FI) / st || st'
  | E_WhileEnd : forall (b:bexp2) (st:state) (c:com),
      beval2 st b = false ->
      (WHILE b DO c END) / st || st
  | E_WhileLoop : forall (st st' st'':state) (b:bexp2) (c:com),
      beval2 st b = true ->
      c / st || st' ->
      (WHILE b DO c END) / st' || st'' ->
      (WHILE b DO c END) / st || st''

  where "c1 '/' st '||' st'" := (ceval c1 st st').


Tactic Notation "ceval_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "E_Skip" | Case_aux c "E_Ass" | Case_aux c "E_Seq"
  | Case_aux c "E_IfTrue" | Case_aux c "E_IfFalse"
  | Case_aux c "E_WhileEnd" | Case_aux c "E_WhileLoop" ].


Theorem ceval_deterministic: forall (c:com) (st st1 st2: state),
     c / st || st1 ->
     c / st || st2 ->
     st1 = st2.
Proof.
  intros c st st1 st2 E1 E2.
  generalize dependent st2.
  ceval_cases (induction E1) Case;
           intros st2 E2; inversion E2; subst.
  Case "E_Skip". reflexivity.
  Case "E_Ass". reflexivity.
  Case "E_Seq".
    assert (st' = st'0) as EQ1.
      SCase "Proof of assertion". apply IHE1_1; assumption.
    subst st'0.
    apply IHE1_2. assumption.
  Case "E_IfTrue".
    SCase "b1 evaluates to true".
      apply IHE1. assumption.
    SCase "b1 evaluates to false (contradiction)".
      rewrite H in H5. inversion H5.
  Case "E_IfFalse".
    SCase "b1 evaluates to true (contradiction)".
      rewrite H in H5. inversion H5.
    SCase "b1 evaluates to false".
      apply IHE1. assumption.
  Case "E_WhileEnd".
    SCase "b1 evaluates to false".
      reflexivity.
    SCase "b1 evaluates to true (contradiction)".
      rewrite H in H2. inversion H2.
  Case "E_WhileLoop".
    SCase "b1 evaluates to false (contradiction)".
      rewrite H in H4. inversion H4.
    SCase "b1 evaluates to true".
      assert (st' = st'0) as EQ1.
        SSCase "Proof of assertion". apply IHE1_1; assumption.
      subst st'0.
      apply IHE1_2. assumption. Qed.



(********************************************SMALL - STEP********************************************)


(*******************************************DETERMINISTIC STEP - EXAMPLE - 1******************************************)


Inductive tm : Type :=
  | C : nat -> tm (* Constant *)
  | P : tm -> tm -> tm. (* Plus *)

Fixpoint evalF (t : tm) : nat :=
  match t with
  | C n => n
  | P a1 a2 => evalF a1 + evalF a2
  end.

Reserved Notation " t '||' n " (at level 50, left associativity).

Inductive eval : tm -> nat -> Prop :=
  | E_Const : forall n:nat,
      C n || n
  | E_Plus : forall (t1 t2:tm) (n1 n2:nat),
      t1 || n1 ->
      t2 || n2 ->
      P t1 t2 || (n1 + n2)

  where " t '||' n " := (eval t n).

Reserved Notation " t '=>' t' " (at level 50, left associativity).

Module SimpleArith1.

Inductive step : tm -> tm -> Prop :=
  | ST_PlusConstConst : forall n1 n2:nat,
      P (C n1) (C n2) => C (n1 + n2)
  | ST_Plus1 : forall t1 t1' t2: tm,
      t1 => t1' ->
      P t1 t2 => P t1' t2
  | ST_Plus2 : forall (n1:nat) (t2 t2':tm),
      t2 => t2' ->
      P (C n1) t2 => P (C n1) t2'

  where " t '=>' t' " := (step t t').


Definition deterministic2 {X: Type} (R: relation X) :=
  forall x y1 y2 : X, R x y1 -> R x y2 -> y1 = y2.

End SimpleArith1.


Module SimpleArith2.
Import SimpleArith1.

Theorem step_deterministic:
  deterministic2 step.
Proof.
  unfold deterministic2. intros x y1 y2 Hy1 Hy2.
  generalize dependent y2.
  induction Hy1; intros y2 Hy2.
    - (* ST_PlusConstConst *) inversion Hy2.
      + (* ST_PlusConstConst *) reflexivity.
      + (* ST_Plus1 *) inversion H2.
      + (* ST_Plus2 *) inversion H2.

    - (* ST_Plus1 *) inversion Hy2.
      + (* ST_PlusConstConst *) rewrite <- H0 in Hy1. inversion Hy1.
      + (* ST_Plus1 *)
        rewrite <- (IHHy1 t1'0).
        reflexivity. assumption.
      + (* ST_Plus2 *) rewrite <- H in Hy1. inversion Hy1.

    - (* ST_Plus2 *) inversion Hy2.
      + (* ST_PlusConstConst *) rewrite <- H1 in Hy1. inversion Hy1.
      + (* ST_Plus1 *) inversion H2.
      + (* ST_Plus2 *)
        rewrite <- (IHHy1 t2'0).
        reflexivity. assumption.
Qed.


Theorem step_deterministic_alt: deterministic step.
Proof.
  intros x y1 y2 Hy1 Hy2.
  generalize dependent y2.
  induction Hy1; intros y2 Hy2;
    inversion Hy2; subst; try (solve by inversion).
  - (* ST_PlusConstConst *) reflexivity.
  - (* ST_Plus1 *)
    apply IHHy1 in H2. rewrite H2. reflexivity.
  - (* ST_Plus2 *)
    apply IHHy1 in H2. rewrite H2. reflexivity.
Qed.

End SimpleArith2.


Inductive value : tm -> Prop :=
  v_const : forall n:nat, value (C n).


(***********************EXPLICIT Value******************)


Inductive step : tm -> tm -> Prop :=
  | ST_PlusConstConst : forall n1 n2:nat,
          P (C n1) (C n2)
      => C (n1 + n2)
  | ST_Plus1 : forall t1 t1' t2:tm,
        t1 => t1' ->
        P t1 t2 => P t1' t2
  | ST_Plus2 : forall (v1 t2 t2':tm),
        value v1 -> (* <----- n.b. *)
        t2 => t2' ->
        P v1 t2 => P v1 t2'

  where " t '=>' t' " := (step t t').

(****************************PROOF FOR PROGRESS***********************)

Theorem strong_progress : forall t,
  value t \/ (exists t', t => t').
Proof.
  induction t.
    - (* C *) left. apply v_const.
    - (* P *) right. inversion IHt1.
      + (* l *) inversion IHt2.
        * (* l *) inversion H. inversion H0.
          exists(C (n + n0)).
          apply ST_PlusConstConst.
        * (* r *) inversion H0 as [t' H1].
          exists(P t1 t').
          apply ST_Plus2. apply H. apply H1.
      + (* r *) inversion H as [t' H0].
          exists(P t' t2).
          apply ST_Plus1. apply H0. Qed.


(***********************NORMAL FORMS***************************)

Definition normal_form {X:Type} (R:relation X) (t:X) : Prop :=
  ~ exists t', R t t'.

Lemma value_is_nf : forall v,
  value v -> normal_form step v.
Proof.
  unfold normal_form. intros v H. inversion H.
  intros contra. inversion contra. inversion H1.
Qed.

Lemma nf_is_value : forall t,
  normal_form step t -> value t.
Proof. (* a corollary of strong_progress... *)
  unfold normal_form. intros t H.
  assert (G : value t \/ exists t', t => t').
  { (* Proof of assertion *) apply strong_progress. }
  inversion G.
    + (* l *) apply H0.
    + (* r *) exfalso. apply H. assumption. Qed.

Corollary nf_same_as_value : forall t,
  normal_form step t <-> value t.
Proof.
  split. apply nf_is_value. apply value_is_nf. Qed.

(************************MULTI-STEP REDUCTION*****************)

Inductive multi2 {X:Type} (R: relation X) : relation X :=
  | multi_refl2 : forall (x : X), multi2 R x x
  | multi_step2 : forall (x y z : X),
                    R x y ->
                    multi2 R y z ->
                    multi2 R x z.

Notation " t '=>*' t' " := (multi2 step t t') (at level 40).

Theorem multi_R2 : forall (X:Type) (R:relation X) (x y : X),
       R x y -> (multi2 R) x y.
Proof.
  intros X R x y H.
  apply multi_step2 with y. apply H. apply multi_refl2. Qed.

Theorem multi_trans2 :
  forall (X:Type) (R: relation X) (x y z : X),
      multi2 R x y ->
      multi2 R y z ->
      multi2 R x z.
Proof.
  intros X R x y z G H.
  induction G.
    - (* multi_refl *) assumption.
    - (* multi_step *)
      apply multi_step2 with y. assumption.
      apply IHG. assumption. Qed.

Definition step_normal_form := normal_form step.

Definition normal_form_of (t t' : tm) :=
  (t =>* t' /\ step_normal_form t').

(***********************************************SMALL STEP - IMP - EXAMPLE 2************************************)


Inductive aval : aexp2 -> Prop :=
  av_num : forall n, aval (ANum2 n).

Reserved Notation " t '/' st '=a>' t' " (at level 40, st at level 39).

Inductive astep : state -> aexp2 -> aexp2 -> Prop :=
  | AS_Id : forall st i,
      AId2 i / st =a> ANum2 (st i)
  | AS_Plus2 : forall st n1 n2,
      APlus2 (ANum2 n1) (ANum2 n2) / st =a> ANum2 (n1 + n2)
  | AS_Plus_1 : forall st a1 a1' a2,
      a1 / st =a> a1' ->
      (APlus2 a1 a2) / st =a> (APlus2 a1' a2)
  | AS_Plus_2 : forall st v1 a2 a2',
      aval v1 ->
      a2 / st =a> a2' ->
      (APlus2 v1 a2) / st =a> (APlus2 v1 a2')
  | AS_Minus2 : forall st n1 n2,
      (AMinus2 (ANum2 n1) (ANum2 n2)) / st =a> (ANum2 (minus n1 n2))
  | AS_Minus_1 : forall st a1 a1' a2,
      a1 / st =a> a1' ->
      (AMinus2 a1 a2) / st =a> (AMinus2 a1' a2)
  | AS_Minus_2 : forall st v1 a2 a2',
      aval v1 ->
      a2 / st =a> a2' ->
      (AMinus2 v1 a2) / st =a> (AMinus2 v1 a2')
  | AS_Mult2 : forall st n1 n2,
      (AMult2 (ANum2 n1) (ANum2 n2)) / st =a> (ANum2 (mult n1 n2))
  | AS_Mult_1 : forall st a1 a1' a2,
      a1 / st =a> a1' ->
      (AMult2 (a1) (a2)) / st =a> (AMult2 (a1') (a2))
  | AS_Mult_2 : forall st v1 a2 a2',
      aval v1 ->
      a2 / st =a> a2' ->
      (AMult2 v1 a2) / st =a> (AMult2 v1 a2')

    where " t '/' st '=a>' t' " := (astep st t t').

(********bstep***********)

Require Import Le Lt Gt Decidable PeanoNat.
Notation leb := Nat.leb (compat "8.4").

Reserved Notation " t '/' st '=b>' t' " (at level 40, st at level 39).

  Inductive bstep : state -> bexp2 -> bexp2 -> Prop :=
  | BS_Eq : forall st n1 n2,
      (BEq2 (ANum2 n1) (ANum2 n2)) / st =b>
      (if (beq_nat n1 n2) then BTrue2 else BFalse2)
  | BS_Eq1 : forall st a1 a1' a2,
      a1 / st =a> a1' ->
      (BEq2 a1 a2) / st =b> (BEq2 a1' a2)
  | BS_Eq2 : forall st v1 a2 a2',
      aval v1 ->
      a2 / st =a> a2' ->
      (BEq2 v1 a2) / st =b> (BEq2 v1 a2')
  | BS_LtEq : forall st n1 n2,
      (BLe2 (ANum2 n1) (ANum2 n2)) / st =b>
               (if (leb n1 n2) then BTrue2 else BFalse2)
  | BS_LtEq1 : forall st a1 a1' a2,
      a1 / st =a> a1' ->
      (BLe2 a1 a2) / st =b> (BLe2 a1' a2)
  | BS_LtEq2 : forall st v1 a2 a2',
      aval v1 ->
      a2 / st =a> a2' ->
      (BLe2 v1 a2) / st =b> (BLe2 v1 (a2'))
  | BS_NotTrue : forall st,
      (BNot2 BTrue2) / st =b> BFalse2
  | BS_NotFalse : forall st,
      (BNot2 BFalse2) / st =b> BTrue2
  | BS_NotStep : forall st b1 b1',
      b1 / st =b> b1' ->
      (BNot2 b1) / st =b> (BNot2 b1')
  | BS_AndTrueTrue : forall st,
      (BAnd2 BTrue2 BTrue2) / st =b> BTrue2
  | BS_AndTrueFalse : forall st,
      (BAnd2 BTrue2 BFalse2) / st =b> BFalse2
  | BS_AndFalse : forall st b2,
      (BAnd2 BFalse2 b2) / st =b> BFalse2
  | BS_AndTrueStep : forall st b2 b2',
      b2 / st =b> b2' ->
      (BAnd2 BTrue2 b2) / st =b> (BAnd2 BTrue2 b2')
  | BS_AndStep : forall st b1 b1' b2,
      b1 / st =b> b1' ->
      (BAnd2 b1 b2) / st =b> (BAnd2 b1' b2)

  where " t '/' st '=b>' t' " := (bstep st t t').

(******************COMMANDS***************)

Reserved Notation " t '/' st '=>' t' '/' st' "
                  (at level 40, st at level 39, t' at level 39).

Definition total_map (A:Type) := id -> A.

Definition t_empty {A:Type} (v : A) : total_map A :=
  (fun _ => v).

Definition t_update {A:Type} (m : total_map A)
                    (x : id) (v : A) :=
  fun x' => if beq_id x x' then v else m x'.


Inductive cstep : (com * state) -> (com * state) -> Prop :=
  | CS_AssStep : forall st i a a',
      a / st =a> a' ->
     (i ::= a) / st => (i ::= a') / st
  | CS_Ass : forall st i n,
      (i ::= (ANum2 n)) / st => SKIP / (t_update st i n)
  | CS_SeqStep : forall st c1 c1' st' c2,
      c1 / st => c1' / st' ->
      (c1 ;; c2) / st => (c1' ;; c2) / st'
  | CS_SeqFinish : forall st c2,
      (SKIP ;; c2) / st => c2 / st
  | CS_IfTrue : forall st c1 c2,
      IFB BTrue2 THEN c1 ELSE c2 FI / st => c1 / st
  | CS_IfFalse : forall st c1 c2,
      IFB BFalse2 THEN c1 ELSE c2 FI / st => c2 / st
  | CS_IfStep : forall st b b' c1 c2,
      b / st =b> b' ->
          IFB b THEN c1 ELSE c2 FI / st 
      => (IFB b' THEN c1 ELSE c2 FI) / st
  | CS_While : forall st b c1,
          (WHILE b DO c1 END) / st
      => (IFB b THEN (c1;; (WHILE b DO c1 END)) ELSE SKIP FI) / st

  where " t '/' st '=>' t' '/' st' " := (cstep (t,st) (t',st')).


(*************************************CONCURRENT IMP - EXAMPLE 3****************************)

Module CImp.

Inductive com : Type :=
  | CSkip : com
  | CAss : id -> aexp2 -> com
  | CSeq : com -> com -> com
  | CIf : bexp2 -> com -> com -> com
  | CWhile : bexp2 -> com -> com
  (* New: *)
  | CPar : com -> com -> com.

Notation "'SKIP'" :=
  CSkip.
Notation "x '::=' a" :=
  (CAss x a) (at level 60).
Notation "c1 ;; c2" :=
  (CSeq c1 c2) (at level 80, right associativity).
Notation "'WHILE' b 'DO' c 'END'" :=
  (CWhile b c) (at level 80, right associativity).
Notation "'IFB' b 'THEN' c1 'ELSE' c2 'FI'" :=
  (CIf b c1 c2) (at level 80, right associativity).
Notation "'PAR' c1 'WITH' c2 'END'" :=
  (CPar c1 c2) (at level 80, right associativity).

Inductive cstep : (com * state) -> (com * state) -> Prop :=
    (* Old part *)
  | CS_AssStep : forall st i a a',
      a / st =a> a' ->
      (i ::= a) / st => (i ::= a') / st
  | CS_Ass : forall st i n,
      (i ::= (ANum2 n)) / st => SKIP / (t_update st i n)
  | CS_SeqStep : forall st c1 c1' st' c2,
      c1 / st => c1' / st' ->
      (c1 ;; c2) / st => (c1' ;; c2) / st'
  | CS_SeqFinish : forall st c2,
      (SKIP ;; c2) / st => c2 / st
  | CS_IfTrue : forall st c1 c2,
      (IFB BTrue2 THEN c1 ELSE c2 FI) / st => c1 / st
  | CS_IfFalse : forall st c1 c2,
      (IFB BFalse2 THEN c1 ELSE c2 FI) / st => c2 / st
  | CS_IfStep : forall st b b' c1 c2,
      b /st =b> b' ->
          (IFB b THEN c1 ELSE c2 FI) / st 
      => (IFB b' THEN c1 ELSE c2 FI) / st
  | CS_While : forall st b c1,
          (WHILE b DO c1 END) / st 
      => (IFB b THEN (c1;; (WHILE b DO c1 END)) ELSE SKIP FI) / st
    (* New part: *)
  | CS_Par1 : forall st c1 c1' c2 st',
      c1 / st => c1' / st' ->
      (PAR c1 WITH c2 END) / st => (PAR c1' WITH c2 END) / st'
  | CS_Par2 : forall st c1 c2 c2' st',
      c2 / st => c2' / st' ->
      (PAR c1 WITH c2 END) / st => (PAR c1 WITH c2' END) / st'
  | CS_ParDone : forall st,
      (PAR SKIP WITH SKIP END) / st => SKIP / st
  where " t '/' st '=>' t' '/' st' " := (cstep (t,st) (t',st')).

Definition cmultistep := multi cstep.

Notation " t '/' st '=>*' t' '/' st' " :=
   (multi cstep (t,st) (t',st'))
   (at level 40, st at level 39, t' at level 39).

(**************************EXAMPLE - CONCURRENT EXECUTION IN SMALL STEP PROOFS - EXAMPLE 3************************)

Definition X : id := Id 0.
Definition Y : id := Id 1.
Definition Z : id := Id 2.

Definition par_loop : com :=
  PAR Y ::= ANum2 1
  WITH
    WHILE BEq2 (AId2 Y) (ANum2 0) DO
      X ::= APlus2 (AId2 X) (ANum2 1)
    END
  END.


Example par_loop_example_0:
  exists st',
       par_loop / empty_state =>* SKIP / st'
    /\ st' X = 0.
Proof.
  eapply ex_intro. split.
  unfold par_loop.
  eapply multi_step. apply CS_Par1.
    apply CS_Ass.
  eapply multi_step. apply CS_Par2. apply CS_While.
  eapply multi_step. apply CS_Par2. apply CS_IfStep.
    apply BS_Eq1. apply AS_Id.
  eapply multi_step. apply CS_Par2. apply CS_IfStep.
    apply BS_Eq. simpl.
  eapply multi_step. apply CS_Par2. apply CS_IfFalse.
  eapply multi_step. apply CS_ParDone.
  eapply multi_refl.
  reflexivity. Qed.

Example par_loop_example_2:
  exists st',
       par_loop / empty_state =>* SKIP / st'
    /\ st' X = 2.
Proof.
  eapply ex_intro. split.
  eapply multi_step. apply CS_Par2. apply CS_While.
  eapply multi_step. apply CS_Par2. apply CS_IfStep.
    apply BS_Eq1. apply AS_Id.
  eapply multi_step. apply CS_Par2. apply CS_IfStep.
    apply BS_Eq. simpl.
  eapply multi_step. apply CS_Par2. apply CS_IfTrue.
  eapply multi_step. apply CS_Par2. apply CS_SeqStep.
    apply CS_AssStep. apply AS_Plus_1. apply AS_Id.
  eapply multi_step. apply CS_Par2. apply CS_SeqStep.
    apply CS_AssStep. apply AS_Plus2.
  eapply multi_step. apply CS_Par2. apply CS_SeqStep.
    apply CS_Ass.
  eapply multi_step. apply CS_Par2. apply CS_SeqFinish.

  eapply multi_step. apply CS_Par2. apply CS_While.
  eapply multi_step. apply CS_Par2. apply CS_IfStep.
    apply BS_Eq1. apply AS_Id.
  eapply multi_step. apply CS_Par2. apply CS_IfStep.
    apply BS_Eq. simpl.
  eapply multi_step. apply CS_Par2. apply CS_IfTrue.
  eapply multi_step. apply CS_Par2. apply CS_SeqStep.
    apply CS_AssStep. apply AS_Plus_1. apply AS_Id.
  eapply multi_step. apply CS_Par2. apply CS_SeqStep.
    apply CS_AssStep. apply AS_Plus2.
  eapply multi_step. apply CS_Par2. apply CS_SeqStep.
    apply CS_Ass.

  eapply multi_step. apply CS_Par1. apply CS_Ass.
  eapply multi_step. apply CS_Par2. apply CS_SeqFinish.
  eapply multi_step. apply CS_Par2. apply CS_While.
  eapply multi_step. apply CS_Par2. apply CS_IfStep.
    apply BS_Eq1. apply AS_Id.
  eapply multi_step. apply CS_Par2. apply CS_IfStep.
    apply BS_Eq. simpl.
  eapply multi_step. apply CS_Par2. apply CS_IfFalse.
  eapply multi_step. apply CS_ParDone.
  eapply multi_refl.
  reflexivity. Qed.



(*****************************************COQ - TYPES***********************************)


Lemma auto_example_1 : forall P Q R S T U : Prop,
  (P -> Q) ->
  (P -> R) ->
  (T -> R) ->
  (S -> T -> U) ->
  ((P->Q) -> (P->S)) ->
  T ->
  P ->
  U.
Proof. auto. Qed.

(** When searching for potential proofs of the current goal, [auto]
    and [eauto] consider the hypotheses in the current context
    together with a _hint database_ of other lemmas and constructors.
    Some of the lemmas and constructors we've already seen -- e.g.,
    [conj], [or_introl], and [or_intror] -- are installed in this hint
    database by default. *)

Lemma auto_example_2 : forall P Q R : Prop,
  Q ->
  (Q -> R) ->
  P \/ (Q /\ R).
Proof.
  auto. Qed.

(** We can extend the hint database just for the purposes of one
    application of [auto] or [eauto] by writing [auto using ...].
    E.g., if [conj], [or_introl], and [or_intror] had _not_ already
    been in the hint database, we could have done this instead: *)

Lemma auto_example_2a : forall P Q R : Prop,
  Q ->
  (Q -> R) ->
  P \/ (Q /\ R).
Proof.
  auto using conj, or_introl, or_intror.  Qed.

(** Of course, in any given development there will also be some of our
    own specific constructors and lemmas that are used very often in
    proofs.  We can add these to the global hint database by writing
      Hint Resolve T.
    at the top level, where [T] is a top-level theorem or a
    constructor of an inductively defined proposition (i.e., anything
    whose type is an implication).  As a shorthand, we can write
      Hint Constructors c.
    to tell Coq to do a [Hint Resolve] for _all_ of the constructors
    from the inductive definition of [c].
    It is also sometimes necessary to add
      Hint Unfold d.
    where [d] is a defined symbol, so that [auto] knows to expand
    uses of [d] and enable further possibilities for applying
    lemmas that it knows about. *)

(** Here are some [Hint]s we will find useful. *)

Hint Constructors multi.
Hint Resolve beq_id_eq beq_id_false_not_eq.

(** Warning: Just as with Coq's other automation facilities, it is
    easy to overuse [auto] and [eauto] and wind up with proofs that
    are impossible to understand later!
    Also, overuse of [eauto] can make proof scripts very slow.  Get in
    the habit of using [auto] most of the time and [eauto] only when
    necessary.
    For much more detailed information about using [auto] and [eauto],
    see the chapter [UseAuto]. *)

(* ###################################################################### *)
(** ** The [Proof with] Tactic *)

(** If you start a proof by saying [Proof with (tactic)] instead of
    just [Proof], then writing [...] instead of [.] after a tactic in
    the body of the proof will try to solve all generated subgoals
    with [tactic] (and fail if this doesn't work).
    One common use of this facility is "[Proof with auto]" (or
    [eauto]).  We'll see many examples of this later in the file. *)

(* ###################################################################### *)
(** ** The [solve by inversion] Tactic *)

(** Here's another nice automation feature: it often arises that the
    context contains a contradictory assumption and we want to use
    [inversion] on it to solve the goal.  We'd like to be able to say
    to Coq, "find a contradictory assumption and invert it" without
    giving its name explicitly.
    Doing [solve by inversion] will find a hypothesis that can be
    inverted to solve the goal, if there is one.  The tactics [solve
    by inversion 2] and [solve by inversion 3] are slightly fancier
    versions which will perform two or three inversions in a row, if
    necessary, to solve the goal.
    (These tactics are not actually built into Coq -- their
    definitions are in [Sflib].)
    Caution: Overuse of [solve by inversion] can lead to slow proof
    scripts. *)

(* ###################################################################### *)
(** ** The [try solve] Tactic *)

(** If [t] is a tactic, then [try solve [t]] is a tactic that
      - if [t] solves the goal, behaves just like [t], or
      - if [t] cannot completely solve the goal, does
        nothing.
    More generally, [try solve [t1 | t2 | ...]] will try to solve the
    goal by using [t1], [t2], etc.  If none of them succeeds in
    completely solving the goal, then [try solve [t1 | t2 | ...]] does
    nothing. *)

(* ###################################################################### *)
(** ** The [f_equal] Tactic *)

(** [f_equal] replaces a goal of the form [f x1 x2 ... xn = f y1 y2
    ... yn], where [f] is some function, with the subgoals [x1 = y1],
    [x2 = y2],...,[xn = yn].  It is useful for avoiding explicit
    rewriting steps, and often the generated subgoals can be quickly
    cleared by [auto].  This tactic is not fundamental, in the sense
    that it can always be replaced by a sequence of [assert]s.
    However in some cases it can be very handy. *)

(* ###################################################################### *)
(** ** The [normalize] Tactic *)

(** When experimenting with definitions of programming languages in
    Coq, we often want to see what a particular concrete term steps
    to -- i.e., we want to find proofs for goals of the form [t ==>*
    t'], where [t] is a completely concrete term and [t'] is unknown.
    These proofs are simple but repetitive to do by hand. Consider for
    example reducing an arithmetic expression using the small-step
    relation [astep] defined in the previous chapter: *)

Definition amultistep st := multi (astep st).
Notation " t '/' st '==>a*' t' " := (amultistep st t t')
  (at level 40, st at level 39).

Example astep_example1 :
  (APlus2 (ANum2 3) (AMult2 (ANum2 3) (ANum2 4))) / empty_state
  ==>a* (ANum2 15).
Proof.
  apply multi_step with (APlus2 (ANum2 3) (ANum2 12)).
    apply AS_Plus_2.
      apply av_num.
      apply AS_Mult2.
  apply multi_step with (ANum2 15).
    apply AS_Plus2.
  apply multi_refl.
Qed.

(** We repeatedly applied [multi_step] until we got to a normal
    form. The proofs that the intermediate steps are possible are
    simple enough that [auto], with appropriate hints, can solve
    them. *)

Hint Constructors astep aval.
Example astep_example1' :
  (APlus2 (ANum2 3) (AMult2 (ANum2 3) (ANum2 4))) / empty_state
  ==>a* (ANum2 15).
Proof.
  eapply multi_step. auto. simpl.
  eapply multi_step. auto. simpl.
  apply multi_refl.
Qed.

(** The following custom [Tactic Notation] definition captures this
    pattern.  In addition, before each [multi_step] we print out the
    current goal, so that the user can follow how the term is being
    evaluated. *)



(** The [normalize] tactic also provides a simple way to calculate
    what the normal form of a term is, by proving a goal with an
    existential variable in it. *)


(* ###################################################################### *)
(** * Typed Arithmetic Expressions *)

(** To motivate the discussion of type systems, let's begin as
    usual with an extremely simple toy language.  We want it to have
    the potential for programs "going wrong" because of runtime type
    errors, so we need something a tiny bit more complex than the
    language of constants and addition that we used in chapter
    [Smallstep]: a single kind of data (just numbers) is too simple,
    but just two kinds (numbers and booleans) already gives us enough
    material to tell an interesting story.

    The language definition is completely routine.  The only thing to
    notice is that we are _not_ using the [asnum]/[aslist] trick that
    we used in chapter [ImpList] to make all the operations total by
    forcibly coercing the arguments to [+] (for example) into numbers.
    Instead, we simply let terms get stuck if they try to use an
    operator with the wrong kind of operands: the [step] relation
    doesn't relate them to anything. *)

(* ###################################################################### *)
(** ** Syntax *)

(** Informally:
    t ::= true
        | false
        | if t then t else t
        | 0
        | succ t
        | pred t
        | iszero t
    Formally:
*)

Inductive tm : Type :=
  | ttrue : tm
  | tfalse : tm
  | tif : tm -> tm -> tm -> tm
  | tzero : tm
  | tsucc : tm -> tm
  | tpred : tm -> tm
  | tiszero : tm -> tm.

(** _Values_ are [true], [false], and numeric values... *)

Inductive bvalue : tm -> Prop :=
  | bv_true : bvalue ttrue
  | bv_false : bvalue tfalse.

Inductive nvalue : tm -> Prop :=
  | nv_zero : nvalue tzero
  | nv_succ : forall t, nvalue t -> nvalue (tsucc t).

Definition value (t:tm) := bvalue t \/ nvalue t.

Hint Constructors bvalue nvalue.
Hint Unfold value.

(* ###################################################################### *)
(** ** Operational Semantics *)

(** Informally:
                    ------------------------------                  (ST_IfTrue)
                    if true then t1 else t2 ==> t1

                   -------------------------------                 (ST_IfFalse)
                   if false then t1 else t2 ==> t2

                              t1 ==> t1'
                      -------------------------                         (ST_If)
                      if t1 then t2 else t3 ==>
                        if t1' then t2 else t3

                              t1 ==> t1'
                         --------------------                         (ST_Succ)
                         succ t1 ==> succ t1'

                             ------------                         (ST_PredZero)
                             pred 0 ==> 0

                           numeric value v1
                        ---------------------                     (ST_PredSucc)
                        pred (succ v1) ==> v1

                              t1 ==> t1'
                         --------------------                         (ST_Pred)
                         pred t1 ==> pred t1'

                          -----------------                     (ST_IszeroZero)
                          iszero 0 ==> true

                           numeric value v1
                      --------------------------                (ST_IszeroSucc)
                      iszero (succ v1) ==> false

                              t1 ==> t1'
                       ------------------------                     (ST_Iszero)
                       iszero t1 ==> iszero t1'
    Formally:
*)

Reserved Notation "t1 '==>' t2" (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_IfTrue : forall t1 t2,
      (tif ttrue t1 t2) ==> t1
  | ST_IfFalse : forall t1 t2,
      (tif tfalse t1 t2) ==> t2
  | ST_If : forall t1 t1' t2 t3,
      t1 ==> t1' ->
      (tif t1 t2 t3) ==> (tif t1' t2 t3)
  | ST_Succ : forall t1 t1',
      t1 ==> t1' ->
      (tsucc t1) ==> (tsucc t1')
  | ST_PredZero :
      (tpred tzero) ==> tzero
  | ST_PredSucc : forall t1,
      nvalue t1 ->
      (tpred (tsucc t1)) ==> t1
  | ST_Pred : forall t1 t1',
      t1 ==> t1' ->
      (tpred t1) ==> (tpred t1')
  | ST_IszeroZero :
      (tiszero tzero) ==> ttrue
  | ST_IszeroSucc : forall t1,
       nvalue t1 ->
      (tiszero (tsucc t1)) ==> tfalse
  | ST_Iszero : forall t1 t1',
      t1 ==> t1' ->
      (tiszero t1) ==> (tiszero t1')

where "t1 '==>' t2" := (step t1 t2).

Tactic Notation "step_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "ST_IfTrue" | Case_aux c "ST_IfFalse" | Case_aux c "ST_If"
  | Case_aux c "ST_Succ" | Case_aux c "ST_PredZero"
  | Case_aux c "ST_PredSucc" | Case_aux c "ST_Pred"
  | Case_aux c "ST_IszeroZero" | Case_aux c "ST_IszeroSucc"
  | Case_aux c "ST_Iszero" ].

Hint Constructors step.

(** Notice that the [step] relation doesn't care about whether
    expressions make global sense -- it just checks that the operation
    in the _next_ reduction step is being applied to the right kinds
    of operands.  For example, the term [succ true] (i.e., [tsucc
    ttrue] in the formal syntax) cannot take a step, but the
    almost-as-obviously-nonsensical term
       succ (if true then true else true)
    can take _one_ step. *)

(* ###################################################################### *)
(** ** Normal Forms and Values *)

(** The first interesting thing about the [step] relation in this
    language is that the strong progress theorem from the Smallstep
    chapter fails!  That is, there are terms that are normal
    forms (they can't take a step) but not values (because we have not
    included them in our definition of possible "results of
    evaluation").  Such terms are _stuck_. *)

Notation step_normal_form := (normal_form step).

Definition stuck (t:tm) : Prop :=
  step_normal_form t /\ ~ value t.

Hint Unfold stuck.

(** **** Exercise: 2 stars (some_term_is_stuck) *)
Example some_term_is_stuck :
  exists t, stuck t.
Proof.
  exists (tsucc ttrue).
  unfold stuck, normal_form, value.
  split; unfold not; intros.
  solve by inversion 3.
  solve by inversion 3.
Qed.

(** However, although values and normal forms are not the same in this
    language, the former set is included in the latter.  This is
    important because it shows we did not accidentally define things
    so that some value could still take a step. *)

(** **** Exercise: 3 stars, optional (value_is_nf) *)
(** Hint: You will reach a point in this proof where you need to
    use an induction to reason about a term that is known to be a
    numeric value.  This induction can be performed either over the
    term itself or over the evidence that it is a numeric value.  The
    proof goes through in either case, but you will find that one way
    is quite a bit shorter than the other.  For the sake of the
    exercise, try to complete the proof both ways. *)

Lemma value_is_nf : forall t,
  value t -> step_normal_form t.
Proof.
  intros.
  unfold normal_form, not.
  intros.
  inversion H0.
  inversion H.
  inversion H2.
  subst.
  inversion H1.
  subst.
  inversion H1.
  assert (forall t, nvalue t -> ~ (exists t', t ==> t')).
    unfold not.
    intros.
    induction H3.
    solve by inversion 2.
    apply IHnvalue.
    inversion H4.
    inversion H5.
    exists t1'.
    assumption.
  apply H3 in H0.
  assumption.
  assumption.
Qed.

(** **** Exercise: 3 stars, optional (step_deterministic) *)
(** Using [value_is_nf], we can show that the [step] relation is
    also deterministic... *)

Lemma prev_nvalue :
  forall t,
    nvalue (tsucc t) -> nvalue t.
Proof.
  intros.
  inversion H.
  apply H1.
Qed.

Theorem step_deterministic:
  deterministic step.
Proof with eauto.
  unfold deterministic.
  intros x y1 y2 Hy1 Hy2.
  generalize dependent y2.
  step_cases (induction Hy1) Case; subst; intros.
  Case "ST_IfTrue".
    inversion Hy2; try reflexivity.
    solve by inversion.
  Case "ST_IfFalse".
    inversion Hy2; try reflexivity.
    solve by inversion.
  Case "ST_If".
    inversion Hy2; subst; try solve by inversion.
    f_equal.
    auto.
  Case "ST_Succ".
    inversion Hy2; subst.
    f_equal.
    auto.
  Case "ST_PredZero".
    inversion Hy2.
    reflexivity.
    solve by inversion.
  Case "ST_PredSucc".
    generalize dependent y2.
    induction t1; intros; try (inversion Hy2; solve by inversion).
    inversion Hy2...
    solve by inversion 2.
    induction y2; try (solve by inversion 2).
    f_equal.
    apply IHt1.
    apply prev_nvalue...
    Admitted.

(* ###################################################################### *)
(** ** Typing *)

(** The next critical observation about this language is that,
    although there are stuck terms, they are all "nonsensical", mixing
    booleans and numbers in a way that we don't even _want_ to have a
    meaning.  We can easily exclude such ill-typed terms by defining a
    _typing relation_ that relates terms to the types (either numeric
    or boolean) of their final results.  *)

Inductive ty : Type :=
  | TBool : ty
  | TNat : ty.

(** In informal notation, the typing relation is often written
    [|- t : T], pronounced "[t] has type [T]."  The [|-] symbol is
    called a "turnstile".  (Below, we're going to see richer typing
    relations where an additional "context" argument is written to the
    left of the turnstile.  Here, the context is always empty.) *)
(**
                            --------------                             (T_True)
                            |- true : Bool
                           ---------------                            (T_False)
                           |- false : Bool
                |- t1 : Bool    |- t2 : T    |- t3 : T
                --------------------------------------                   (T_If)
                     |- if t1 then t2 else t3 : T
                              ----------                               (T_Zero)
                              |- 0 : Nat
                             |- t1 : Nat
                           ----------------                            (T_Succ)
                           |- succ t1 : Nat
                             |- t1 : Nat
                           ----------------                            (T_Pred)
                           |- pred t1 : Nat
                             |- t1 : Nat
                         -------------------                         (T_IsZero)
                         |- iszero t1 : Bool
*)

Inductive has_type : tm -> ty -> Prop :=
  | T_True :
       has_type ttrue TBool
  | T_False :
       has_type tfalse TBool
  | T_If : forall t1 t2 t3 T,
       has_type t1 TBool ->
       has_type t2 T ->
       has_type t3 T ->
       has_type (tif t1 t2 t3) T
  | T_Zero :
       has_type tzero TNat
  | T_Succ : forall t1,
       has_type t1 TNat ->
       has_type (tsucc t1) TNat
  | T_Pred : forall t1,
       has_type t1 TNat ->
       has_type (tpred t1) TNat
  | T_Iszero : forall t1,
       has_type t1 TNat ->
       has_type (tiszero t1) TBool.


Tactic Notation "has_type_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "T_True" | Case_aux c "T_False" | Case_aux c "T_If"
  | Case_aux c "T_Zero" | Case_aux c "T_Succ" | Case_aux c "T_Pred"
  | Case_aux c "T_Iszero" ].

Hint Constructors has_type.

(* ###################################################################### *)
(** *** Examples *)

(** It's important to realize that the typing relation is a
    _conservative_ (or _static_) approximation: it does not calculate
    the type of the normal form of a term. *)

Example has_type_1 :
  has_type (tif tfalse tzero (tsucc tzero)) TNat.
Proof.
  apply T_If.
    apply T_False.
    apply T_Zero.
    apply T_Succ.
      apply T_Zero.
Qed.

(** (Since we've included all the constructors of the typing relation
    in the hint database, the [auto] tactic can actually find this
    proof automatically.) *)

Example has_type_not :
  ~ has_type (tif tfalse tzero ttrue) TBool.
Proof.
  intros Contra. solve by inversion 2.  Qed.



(* ###################################################################### *)
(** ** Progress *)

(** The typing relation enjoys two critical properties.  The first is
    that well-typed normal forms are values (i.e., not stuck). *)

(** **** Exercise: 3 stars, recommended (finish_progress_informal) *)
(** Complete the following proof: *)

(** _Theorem_: If [|- t : T], then either [t] is a value or else
    [t ==> t'] for some [t']. *)

(** _Proof_: By induction on a derivation of [|- t : T].
      - If the last rule in the derivation is [T_If], then [t = if t1
        then t2 else t3], with [|- t1 : Bool], [|- t2 : T] and [|- t3
        : T].  By the IH, either [t1] is a value or else [t1] can step
        to some [t1'].
            - If [t1] is a value, then it is either an [nvalue] or a
              [bvalue].  But it cannot be an [nvalue], because we know
              [|- t1 : Bool] and there are no rules assigning type
              [Bool] to any term that could be an [nvalue].  So [t1]
              is a [bvalue] -- i.e., it is either [true] or [false].
              If [t1 = true], then [t] steps to [t2] by [ST_IfTrue],
              while if [t1 = false], then [t] steps to [t3] by
              [ST_IfFalse].  Either way, [t] can step, which is what
              we wanted to show.
            - If [t1] itself can take a step, then, by [ST_If], so can
              [t].
    (* FILL IN HERE *)
[]
*)

(** **** Exercise: 3 stars (finish_progress) *)
Theorem progress : forall t T,
  has_type t T ->
  value t \/ exists t', t ==> t'.
Proof with auto.
  intros t T HT.
  has_type_cases (induction HT) Case...
  (* The cases that were obviously values, like T_True and
     T_False, were eliminated immediately by auto *)
  Case "T_If".
    right. inversion IHHT1; clear IHHT1.
    SCase "t1 is a value". inversion H; clear H.
      SSCase "t1 is a bvalue". inversion H0; clear H0.
        SSSCase "t1 is ttrue".
          exists t2...
        SSSCase "t1 is tfalse".
          exists t3...
      SSCase "t1 is an nvalue".
        solve by inversion 2.  (* on H and HT1 *)
    SCase "t1 can take a step".
      inversion H as [t1' H1].
      exists (tif t1' t2 t3)...
  Case "T_Succ".
    inversion IHHT.
    left.
      unfold value.
      right.
      inversion H.
      inversion H0; subst; solve by inversion.
      constructor...
    right.
      inversion H.
      exists (tsucc x)...
  Case "T_Pred".
    inversion IHHT.
    right.
      inversion H.
      inversion H0; subst; solve by inversion.
      inversion H0.
      exists (tzero)...
      exists (t)...
    right.
      inversion H.
      exists (tpred x)...
  Case "T_Iszero".
    inversion IHHT.
    right.
      inversion H.
      inversion H0; subst; solve by inversion.
      inversion H0.
      exists (ttrue)...
      exists (tfalse)...
    right.
      inversion H.
      exists (tiszero x)...
Qed.

(* ###################################################################### *)
(** ** Type Preservation *)

(** The second critical property of typing is that, when a well-typed
    term takes a step, the result is also a well-typed term.
    This theorem is often called the _subject reduction_ property,
    because it tells us what happens when the "subject" of the typing
    relation is reduced.  This terminology comes from thinking of
    typing statements as sentences, where the term is the subject and
    the type is the predicate. *)

(** **** Exercise: 3 stars, recommended (finish_preservation_informal) *)
(** Complete the following proof: *)

(** _Theorem_: If [|- t : T] and [t ==> t'], then [|- t' : T]. *)

(** _Proof_: By induction on a derivation of [|- t : T].
      - If the last rule in the derivation is [T_If], then [t = if t1
        then t2 else t3], with [|- t1 : Bool], [|- t2 : T] and [|- t3
        : T].
        Inspecting the rules for the small-step reduction relation and
        remembering that [t] has the form [if ...], we see that the
        only ones that could have been used to prove [t ==> t'] are
        [ST_IfTrue], [ST_IfFalse], or [ST_If].
           - If the last rule was [ST_IfTrue], then [t' = t2].  But we
             know that [|- t2 : T], so we are done.
           - If the last rule was [ST_IfFalse], then [t' = t3].  But we
             know that [|- t3 : T], so we are done.
           - If the last rule was [ST_If], then [t' = if t1' then t2
             else t3], where [t1 ==> t1'].  We know [|- t1 : Bool] so,
             by the IH, [|- t1' : Bool].  The [T_If] rule then gives us
             [|- if t1' then t2 else t3 : T], as required.
    (* FILL IN HERE *)
[]
*)





(* ###################################################################### *)
(** ** Type Soundness *)

(** Putting progress and preservation together, we can see that a
    well-typed term can _never_ reach a stuck state.  *)


(*********************************THANKYOU**************************)









