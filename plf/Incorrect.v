(** * Incorrect: Incorrectness Logic. Follows the POPL'20 paper. *)

Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From PLF Require Import Maps.
From Coq Require Import Bool.Bool.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.
From Coq Require Import Arith.PeanoNat. Import Nat.
From Coq Require Import Lia.
From PLF Require Export Imp.
From PLF Require Import Hoare.
Import Himp. (* For `x:=nondet()` in the paper *)
Print com.
Set Default Goal Selector "!".

Print valid_hoare_triple.
(* An alternative but equivalent definition. *)
Definition valid_hoare_triple'
           (P : Assertion) (c : com) (Q : Assertion) : Prop :=
  forall st,
    P st ->
      forall st',
      st =[ c ]=> st' -> Q st'.
Lemma valid_hoare_triple_equivalent:
  forall (P Q : Assertion) (c : com),
  valid_hoare_triple P c Q <-> valid_hoare_triple' P c Q.
Proof.
  intros; split; unfold valid_hoare_triple, valid_hoare_triple'.
  - eauto.
  - eauto.
Qed.

(* Compare to valid_hoare_triple' *)
Definition valid_incorrectness_triple
           (P : Assertion) (c : com) (Q : Assertion) : Prop :=
  forall st',
    Q st' ->
      exists st,
      st =[ c ]=> st' /\ P st.

Notation "[[ P ]] c [[ Q ]]" :=
  (valid_incorrectness_triple P c Q)
    (at level 90, c custom com at level 99)
    : hoare_spec_scope.

(* Compare to hoare_consequence in Hoare.v *)
Theorem incorrectness_consequence : forall (P P' Q Q' : Assertion) c,
  [[P']] c [[Q']] ->
  P' ->> P ->
  Q ->> Q' ->
  [[P]] c [[Q]].
Proof.
  unfold valid_incorrectness_triple, "->>".
  intros P P' Q Q' c. intros H HP HQ.
  intros st' Hst'.
  specialize (HQ st' Hst').
  specialize (H st' HQ).
  destruct H as [ st [ H Hst ] ].
  exists st. auto.
Qed.

(* Weaken presumes: more initial states *)
Theorem incorrectness_pre : forall (P P' Q : Assertion) c,
  [[P']] c [[Q]] ->
  P' ->> P ->
  [[P]] c [[Q]].
Proof.
  intros.
  eapply incorrectness_consequence; eauto.
Qed.

(* Strength achieves: less final states *)
Theorem incorrectness_post : forall (P Q Q' : Assertion) c,
  [[P]] c [[Q']] ->
  Q ->> Q' ->
  [[P]] c [[Q]].
Proof.
  intros.
  eapply incorrectness_consequence; eauto.
Qed.

(* The case where there are no paths
 * In IL, an achieves=False is always valid, just like in HL with an ensures=True.
 *)
Theorem incorrectness_post_false : forall (P Q : Assertion) c,
  (forall st, ~ Q st) ->
  [[P]] c [[Q]].
Proof.
  unfold valid_incorrectness_triple. intros.
  apply H in H0. destruct H0.
Qed.

(* However a dual result is not available in IL. *)
Theorem incorrectness_pre_true : forall (P Q : Assertion) c,
  (forall st, P st) ->
  [[P]] c [[Q]].
Proof.
  unfold valid_incorrectness_triple. intros.
  (* What if st' is just unreachable from st by executing c? *)
Abort.

(* We can merge paths in IL, just like we combine information in HL.
 *   {{P}} c {{Q /\ Q'}}
 *)
Theorem incorrectness_disjunction: forall P Q Q' c,
  [[P]] c [[Q]] ->
  [[P]] c [[Q']] ->
  [[P]] c [[Q \/ Q']].
Proof.
  unfold valid_incorrectness_triple. intros.
  destruct H1.
  - apply H in H1. auto.
  - apply H0 in H1. auto.
Qed.

Theorem incorrectness_skip: forall P,
  [[P]] skip [[P]].
Proof.
  unfold valid_incorrectness_triple. intros.
  eexists. split; eauto; try constructor.
Qed.

(* Handling errors:
 * O'Hearn's paper incorporates error state directly into the logic.
 * Another equivalent choice is to define PROGRAM STATE as a tuple of (var -> val, error?).
 * And have the evaluation rule:
 *   (valuation, error?=True) =[ c ]=> (valuation, error?=True)
 * forall commands.
 *
 * The module HoareAssertAssume already does so actually.
 *)

Theorem incorrectness_seq: forall P Q R c1 c2,
  [[P]] c1 [[R]] ->
  [[R]] c2 [[Q]] ->
  [[P]] c1; c2 [[Q]].
Proof.
  unfold valid_incorrectness_triple. intros P Q R c1 c2 Hc1 Hc2 st'' Hst''.
  apply Hc2 in Hst''. destruct Hst'' as [ st' [ Hc2' Hst' ] ].
  apply Hc1 in Hst'. destruct Hst' as [ st [ Hc1' Hst ] ].
  exists st. split; auto. econstructor; eauto.
Qed.


Theorem incorrectness_if_true: forall P Q (b:bexp) c1 c2,
  [[P /\ b]] c1 [[Q]] ->
  [[P]] if b  then c1 else c2 end [[Q]].
Proof.
  unfold valid_incorrectness_triple. intros P Q b c1 c2 Hc1 st' Hst'.
  apply Hc1 in Hst'. destruct Hst' as [ st [ Hc1' [ HP Hb ] ] ].
  exists st. split; auto.
  (* Uncomment if using just Imp instead of Himp (with havoc). *)
  (*
  constructor.
  - simpl in Hb; auto.
  - auto.
  *)
Qed.

Theorem incorrectness_if_false: forall P Q (b:bexp) c1 c2,
  [[P /\ ~ b]] c2 [[Q]] ->
  [[P]] if b then c1 else c2 end [[Q]].
Proof.
  unfold valid_incorrectness_triple. intros P Q b c1 c2 Hc1 st' Hst'.
  apply Hc1 in Hst'. destruct Hst' as [ st [ Hc1' [ HP Hb ] ] ].
  exists st. split; auto. apply E_IfFalse.
  - simpl in Hb. apply not_true_is_false in Hb. auto.
  - auto.
Qed.

(* Not particularly useful.
   But compare to hoare_if (after rewriting with and_ind):

  ({{ P /\ b }} c1 {{Q}}  /\  {{ P /\ ~ b}} c2 {{Q}})
  ->
  {{P}} if b then c1 else c2 end {{Q}}.
*)
Theorem incorrectness_if: forall P Q (b:bexp) c1 c2,
  ([[P /\ b]] c1 [[Q]]  \/  [[P /\ ~ b]] c2 [[Q]])
  ->
  [[P]] if b then c1 else c2 end [[Q]].
Proof.
  intros. destruct H.
  - apply incorrectness_if_true. auto.
  - apply incorrectness_if_false. auto.
Qed.

Theorem incorrectness_asgn_floyd: forall P X a,
  [[P]] X := a [[ fun st => exists m, P (X !-> m; st) /\ st X = aeval (X !-> m; st) a ]].
Proof.
  unfold valid_incorrectness_triple. intros P X a st' [ m [ Hst' H ] ].
  exists (X !-> m; st'). split; auto.
  rewrite <-t_update_same with (x:=X).
  rewrite <-t_update_shadow with (v1:=m) (v2:=st' X).
  constructor. auto.
Qed.

(* As said in the paper, incorrectness_asgn_hoare is unsound.
 * An equivalent form of the previous theorem, similar to that in Hoare.v.
 *)
Theorem incorrectness_asgn_floyd': forall P X a m,
  [[fun st => P st /\ st X = m]] X := a [[ fun st => P (X !-> m; st) /\ st X = aeval (X !-> m; st) a ]].
Proof.
  unfold valid_incorrectness_triple. intros P X a m st' [ Hst' H ].
  exists (X !-> m; st'). repeat split.
  - rewrite <-t_update_same with (x:=X).
    rewrite <-t_update_shadow with (v1:=m) (v2:=st' X).
    constructor. auto.
  - auto.
  - rewrite t_update_eq. auto.
Qed.

(* Compare to havoc_pre in Hoare.v.
 * We're basically substituting forall with exists. *)
Definition havoc_presumes (X : string) (Q : Assertion) (st : state) : Prop
  := (exists m, Q (X !-> m; st)).
(* How do I get rid of the universe inconsistency error? wtf I have to define this havoc_pre. *)

(* Nondet can be simulated by a free variable. *)
Theorem incorrectness_havoc_bw: forall Q X,
  [[ havoc_presumes X Q ]] havoc X [[Q]].
Proof.
  unfold havoc_presumes, valid_incorrectness_triple. intros Q X st' HQ.
  exists st'; split.
  - rewrite <-t_update_same with (x:=X). constructor.
  - exists (st' X). rewrite t_update_same. auto.
Qed.

(* Ok ... I made this up, not the same as in the paper. *)
Theorem incorrectness_havoc_fw: forall P X,
  [[P]] havoc X [[fun st => forall (n : nat), P (X !-> n; st)]].
Proof.
  unfold valid_incorrectness_triple. intros P X st' Hst'.
  exists (X !-> st' X; st'). split; auto.
  rewrite t_update_same. rewrite <-t_update_same with (x:=X).
  constructor.
Qed.

Theorem incorrectness_while_0: forall P (b:bexp) c,
  [[P]] while b do c end [[P /\ ~b]].
Proof.
  unfold valid_incorrectness_triple. intros P b c st' [ HP Hb ].
  exists st'. split; auto. apply E_WhileFalse.
  unfold bassertion in Hb. apply not_true_is_false. auto.
Qed.

(* A large potion of code is used to prove incorrectness_while_ind.
 * This is our difference from O'Hearn's paper,
 * where he does not directly define whiles but instead model then with kleene star and choices.
 *)

(* ceval_fuel (CWhile...) n s0 s1:
  After exactly n iterations of the while (the body executed n times),
  which means during these iterations the loop condition always tests true,
  starting from s0 state, the execution ends in s1 state.

  IT DOES NOT SAY WHETHER THE LOOP TERMINATES IN s1.
  TEST  beval b s1  TO DETERMINE THAT.

 * This is to help us improve knowledge over a loop than `ceval (CWhile..) st0 stn` by
 * 1. tracking the number of iterations performed, which we may use for induction
 * 2. ceval always exits the loop i.e. the loop condition is not satisfied in stn.
 *    Sometimes we want to reason about a round of iteration that does not end up with exiting the loop.
 * Basically, we're just introducing a "middle-step" semantics just for while statements.
 *)
Inductive ceval_fuel : com -> nat -> state -> state -> Prop :=
  | EF_zero : forall (b:bexp) (c:com) st,
      ceval_fuel (CWhile b c) 0 st st
  | EF_Sn : forall (b:bexp) (c:com) st0 st1 stSn (n:nat),
      beval st0 b = true ->
      ceval c st0 st1 ->
      ceval_fuel (CWhile b c) n st1 stSn ->
      ceval_fuel (CWhile b c) (S n) st0 stSn.

Require Import Coq.Program.Equality.
(* Another pseudo-constructor.
 * Defined as a lemma so we do not end up with mutually definable constructors,
 * which could damage our understanding of correctness.
               1 -> n+1
  EF_Sn:  -------------
          0 -> 1 -> n+1

  Compare to

          0 -> n
  EF_Sn': -------------
          0 -> n -> n+1
 *)
Lemma EF_Sn': forall (b:bexp) (c:com) (n:nat) st0 stn stSn,
      ceval_fuel (CWhile b c) n st0 stn ->
      beval stn b = true ->
      ceval c stn stSn ->
      ceval_fuel (CWhile b c) (S n) st0 stSn.
Proof.
  intros b c n st0 stn stSn HEFn.
  intros Hbn Hone_n_Sn.
  dependent induction HEFn.
  - apply EF_Sn with (st1:=stSn); auto. constructor.
  - specialize (IHHEFn b c Logic.eq_refl Hbn Hone_n_Sn).
    rename stSn0 into stSn, stSn into stSSn, Hone_n_Sn into Hone_Sn_SSn.
    apply EF_Sn with (st1:=st1); auto.
Qed.

(* Four equivalence theorems between the "big-step" ceval and "middle-step" ceval_fuel *)
Theorem ceval_fuel_equiv1: forall (b:bexp) (c:com) st stn,
  ceval (CWhile b c) st stn ->
  exists n, ceval_fuel (CWhile b c) n st stn /\ beval stn b = false.
Proof.
  intros b c st stn Heval.
  dependent induction Heval.
  + exists 0. constructor; try constructor; auto.
  + specialize (IHHeval2 b c Logic.eq_refl).
    clear IHHeval1. destruct IHHeval2 as [n [ HEF Hb ] ].
    exists (S n). split; auto.
    apply EF_Sn with (st1 := st'); auto.
Qed.
Theorem ceval_fuel_equiv2: forall (b:bexp) (c:com) st stn (n:nat),
  ceval_fuel (CWhile b c) n st stn /\ beval stn b = false ->
  ceval (CWhile b c) st stn.
Proof.
  intros b c st stn n [ HEF Hb ].
  dependent induction HEF.
  + constructor; auto.
  + specialize (IHHEF b c Logic.eq_refl Hb).
    eapply E_WhileTrue; eauto.
Qed.
Theorem ceval_fuel_equiv3: forall (b:bexp) (c:com) st stn,
  (exists n, ceval_fuel (CWhile b c) n st stn /\ beval stn b = false) ->
  ceval (CWhile b c) st stn.
Proof.
  intros b c st stn [ n [ HEF Hb ] ].
  dependent induction n.
  - inversion HEF; auto.
  - inversion HEF; subst.
    (* We're stuck here!
       We already have

    H3 : st =[ c ]=> st1
    H6 : ceval_fuel <{ while b do c end }> n st1 stn
    HEF : ceval_fuel <{ while b do c end }> (S n) st stn

      But neither (especially H6 and HEF) can help with the induction hypothesis

    IHn : ceval_fuel <{ while b do c end }> n st stn ->
          beval stn b = false -> st =[ while b do c end ]=> stn

      In fact, it's impossible to satisfy `ceval_fuel xx n st stn`.
      It takes (S n) iterations from st to stn, not n.

    This is because, our induction hypothesis is too weak (not universally quantified over n).
    *)
  Restart.
  (* Thank god we have already proven one theorem with stronger induction hypothesis. *)
  intros b c st stn [ n [ HEF Hb ] ].
  eapply ceval_fuel_equiv2. eauto.
Qed.
(* All "equivalence" theorems must be two-ways, right? *)
Theorem ceval_fuel_equiv4: forall (b:bexp) (c:com) st st',
  st =[ while b do c end ]=> st' <->
  exists n, ceval_fuel (CWhile b c) n st st' /\ beval st' b = false.
Proof.
  split. { apply ceval_fuel_equiv1. } { apply ceval_fuel_equiv3. }
Qed.

(* Hard to directly prove incorrectness_while_ind. That's why we have this theorem and all the fuss earlier. *)
Theorem incorrectness_while_ind_fuel: forall (b:bexp) c (I:nat->Assertion),
  (forall n, [[I n /\ b]] c [[I (S n)]]) ->
  forall n stn, I n stn -> exists st0, I 0 st0 /\ ceval_fuel (CWhile b c) n st0 stn.
Proof.
  intros b c I Hone. induction n.
  - intros. exists stn. split; trivial. constructor.
  - intros stSn HISn. unfold valid_incorrectness_triple in Hone.
    pose proof (Hone _ _ HISn).
    destruct H as [ stn [ Hcstn [ HIn Hbn ] ] ].
    pose proof (IHn _ HIn).
    destruct H as [ st0 [ HI0 HEF ] ].
    exists st0. split; auto.
    apply EF_Sn' with (stn:=stn); auto.
Qed.

(* Ok I made this up. It's not the the paper.
 * But I was inspired by https://hexgolems.com/2020/04/incorrectness-logic-by-example/.
 *)
Theorem incorrectness_while_cont: forall (b:bexp) c (I:nat->Assertion),
  (forall n, [[I n /\ b]] c [[I (S n)]]) ->
  forall n, [[I 0]] while b do c end [[I n /\ ~b]].
Proof.
  intros b c I Hbody n. unfold valid_incorrectness_triple.
  intros st [ HIst Hbst ].
  pose proof (incorrectness_while_ind_fuel b c I Hbody n st HIst).
  destruct H as [ st0 [ HI0 HEF ] ].
  exists st0. split; auto.
  apply ceval_fuel_equiv4. exists n. split; auto.
  unfold bassertion in Hbst. apply not_true_is_false in Hbst. auto.
Qed. (* Finally. This sh*t is tougher than I thought! Or did I miss anything obvious? *)

(* https://hexgolems.com/2020/04/incorrectness-logic-by-example/ *)
