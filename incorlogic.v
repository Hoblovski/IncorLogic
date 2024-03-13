Require Import Setoid.

Section IncorrectnessLogic.
(***********************************
 * Language declarations and first class predicates.
 ***********************************)

(* We do not care the exact definitions of program commands or states.
   Be it Imp, be it C, be it lambda calculus, as long as they satisfy our axioms, our code handles them all.
*)
Parameter com: Set.
Parameter st: Set.
(* The denotation of a command is (st -> st -> Prop), rather than (st -> st).
   The latter forces a computability (and determinism) issue. *)
Parameter exec: com -> st -> st -> Prop.

Definition pred := st -> Prop.
Definition pred_or (p q : pred) : pred := (fun st => p st \/ q st).
Definition pred_and (p q : pred) : pred := (fun st => p st /\ q st).
Definition pred_not (p q : pred) : pred := (fun st => ~ (p st)).
Definition pred_imply (p q : pred) : Prop := (forall st, p st -> q st).
Notation "P => Q" := (pred_imply P Q) (at level 81).
Definition pred_exec (c : com) (p : pred) : pred := (fun st' => exists st, p st /\ exec c st st').

Search _ (?a /\ ?b <-> ?b /\ ?a).
Lemma pred_and_comm: forall p q, pred_imply (pred_and p q) (pred_and q p).
Proof. unfold pred_imply, pred_and. intuition. Qed.
Lemma pred_or_comm: forall p q, pred_imply (pred_or p q) (pred_or q p).
Proof. unfold pred_imply, pred_or. intuition. Qed.
Search _ (?a /\ ?b -> ?a).
Lemma pred_and_proj1: forall p q, pred_imply (pred_and p q) p.
Proof. unfold pred_imply, pred_and. intuition. Qed.
Lemma pred_and_proj2: forall p q, pred_imply (pred_and p q) q.
Proof. unfold pred_imply, pred_and. intuition. Qed.
Search _ (?a -> ?a \/ ?b).
Lemma pred_or_introl: forall p q, pred_imply p (pred_or p q).
Proof. unfold pred_imply, pred_or. intuition. Qed.
Check or_intror.
Lemma pred_or_intror: forall p q, pred_imply p (pred_or p q).
Proof. unfold pred_imply, pred_or. intuition. Qed.

Search (forall (P : Prop), P -> P).
Search (forall (P Q R : Prop), (P -> Q) -> (Q -> R) -> (P -> R)).
Search ((_ -> _) -> (_ -> _) -> (_ -> _)).

Lemma pred_imply_refl: forall p, pred_imply p p.
Proof. unfold pred_imply. intuition. Qed.
Lemma pred_imply_trans: forall p q r, pred_imply p q -> pred_imply q r -> pred_imply p r.
Proof. unfold pred_imply. intuition. Qed.
Lemma pred_exec_monotonic:
  forall (P P' : pred) (c : com), pred_imply P P' -> 
  pred_imply (pred_exec c P) (pred_exec c P').
Proof.
  intros. unfold pred_exec, pred_imply in *.
  intros st' [ st [ Hst Hexec ] ].
  exists st. intuition.
Qed.

Search _ (_ -> _ -> (_ \/ _ -> _)).
Lemma pred_or_ind: forall (P P' Q : pred),
  pred_imply P Q ->
  pred_imply P' Q ->
  pred_imply (pred_or P P') Q.
Proof. unfold pred_imply, pred_or. intuition. Qed.


(***********************************
 * Hoare Triples
 ***********************************)
Parameter HoareTriple: pred -> com -> pred -> Prop.

Notation "{{ P }} c {{ Q }}" := (HoareTriple P c Q) (at level 90).
(* A logical definition of hoare triple, treating predicates like functions from states to Props.
   As contrary to set-oriented view in HoareTripleSemanticsDef2, though they are equivalent as we'll prove. *)
Definition HoareTripleSemanticsDef1 (P Q : pred) (c : com) : Prop :=
  (forall s, P s ->
   forall s', exec c s s' ->
   Q s').
Axiom HoareTripleSemantics:
  forall (P Q : pred) (c : com), HoareTriple P c Q <->
  HoareTripleSemanticsDef1 P Q c.
Lemma HoareConseq:
  forall (P Q : pred) (c : com), HoareTriple P c Q -> 
  forall (P' Q' : pred), (pred_imply P' P) -> (pred_imply Q Q') ->
  HoareTriple P' c Q'.
Proof.
  intros.
  rewrite (HoareTripleSemantics P Q c) in H.
  rewrite (HoareTripleSemantics P' Q' c).
  unfold HoareTripleSemanticsDef1 in *.
  intros.
  assert (P s); auto.
  apply H with (s':=s') in H4; auto.
Qed.

(* Treating pred like Sets. pred_exec c is a set to set mapping. *)
Definition HoareTripleSemanticsDef2 (P Q : pred) (c : com) : Prop :=
  pred_imply (pred_exec c P) Q.
Lemma HoareSemanticsEquiv:
  forall P Q c, HoareTripleSemanticsDef1 P Q c <-> HoareTripleSemanticsDef2 P Q c.
Proof. split; unfold HoareTripleSemanticsDef2, HoareTripleSemanticsDef1; intros. {
  unfold pred_imply, pred_exec. intros st' [st [Hst Hexec]].
  apply H with (s':=st') in Hst; auto.
} {
  unfold pred_imply, pred_exec in *.
  apply H. exists s. auto.
} Qed.
Lemma HoareTripleSemantics2:
  forall (P Q : pred) (c : com), HoareTriple P c Q <->
  HoareTripleSemanticsDef2 P Q c.
Proof. intros P Q c.
  rewrite <- (HoareSemanticsEquiv P Q c).
  apply HoareTripleSemantics.
Qed.


(***********************************
 * Incorrectness Triples
 ***********************************)
Parameter IncorTriple: pred -> com -> pred -> Prop.
Notation "[[ P ]] c [[ Q ]]" := (IncorTriple P c Q) (at level 90).
Definition IncorTripleSemanticsDef1 (P Q : pred) (c : com) : Prop :=
  (forall s', Q s' ->
   exists s, exec c s s' /\ P s).
Definition IncorTripleSemanticsDef2 (P Q : pred) (c : com) : Prop :=
  pred_imply Q (pred_exec c P).
Lemma IncorSemanticsEquiv:
  forall P Q c, IncorTripleSemanticsDef1 P Q c <-> IncorTripleSemanticsDef2 P Q c.
Proof. split; unfold IncorTripleSemanticsDef1, IncorTripleSemanticsDef2; intros. {
  unfold pred_imply, pred_exec. intros st' Hst'.
  apply H in Hst'. destruct Hst' as [st [Hexec Hst] ].
  exists st. auto.
} {
  unfold pred_imply, pred_exec in *.
  apply H in H0. destruct H0 as [ st [ Hst Hexec ] ].
  exists st. auto.
} Qed.
Axiom IncorTripleSemantics:
  forall (P Q : pred) (c : com), IncorTriple P c Q <-> IncorTripleSemanticsDef2 P Q c.



(***********************************
 * Formalizations of the paper's theorems.
 ***********************************)
(* ∧∨ Symmetry in Fig. 1 *)
Lemma IncorPostor:
  forall (P Q Q' : pred) (c : com),
  IncorTriple P c Q ->
  IncorTriple P c Q' -> 
  IncorTriple P c (pred_or Q Q').
Proof.
  intros.
  rewrite IncorTripleSemantics in *. unfold IncorTripleSemanticsDef2 in *.
  apply pred_or_ind; auto.
Qed.
(* ⇑⇓ Symmetry in Fig. 1 *)
Lemma IncorConseq:
  forall (P Q : pred) (c : com), IncorTriple P c Q -> 
  forall (P' Q' : pred), (pred_imply P P') -> (pred_imply Q' Q) ->
  IncorTriple P' c Q'.
Proof.
  intros.
  rewrite IncorTripleSemantics in *. unfold IncorTripleSemanticsDef2 in *.
  pose proof (pred_exec_monotonic P P' c H0).
  repeat (eapply pred_imply_trans; eauto).
Qed.
(* Principle of Agreement in Fig. 1 *)
Lemma PrincipleAgreement:
  forall (u u' o o' : pred) (c : com),
  [[ u ]] c [[ u' ]] ->
  u => o ->
  {{ o }} c {{ o' }} ->
  u' => o'.
Proof.
  intros. rewrite IncorTripleSemantics, HoareTripleSemantics2 in *.
  unfold IncorTripleSemanticsDef2, HoareTripleSemanticsDef2 in *.
  eapply pred_imply_trans; eauto.
  eapply pred_imply_trans; eauto.
  apply pred_exec_monotonic. auto.
Qed.
(* Principle of Denial in Fig. 1: just the dual. Omitted. *)
End IncorrectnessLogic.
