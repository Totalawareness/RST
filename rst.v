Require Import Coq.Init.Nat.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.PeanoNat.
Require Import Lia.

(* Use boolean scopes for easier reading *)
Open Scope bool_scope.

(******************************************************************************)
(* 1. Definition of the Expression Type (Expr)                               *)
(*    - STAR:  The distinguished symbol (⋆).                               *)
(*    - CIRC:  The other symbol in the minimal alphabet (◦).                   *)
(*    - DOT:   Concatenation operator (·).                                   *)
(*    - ENC:   Enclosure operator (< , >).                                  *)
(******************************************************************************)

Inductive Expr : Type :=
  | STAR : Expr
  | CIRC : Expr
  | DOT  : Expr -> Expr -> Expr
  | ENC  : Expr -> Expr -> Expr.


(******************************************************************************)
(* 2. The occStar Function                                                    *)
(*    Calculates the number of occurrences of STAR in an expression.        *)
(******************************************************************************)

Fixpoint occStar (e : Expr) : nat :=
  match e with
  | STAR    => 1
  | CIRC    => 0
  | DOT a b => occStar a + occStar b
  | ENC a b => occStar a + occStar b
  end.


(******************************************************************************)
(* 3. The Derivable Predicate                                                 *)
(*    Defines when an expression is considered "derivable" in RST.           *)
(*    - base_star, base_circ: Base cases for STAR and CIRC.                   *)
(*    - rule_dot:  DOT e1 e2 is derivable if e1 and e2 are derivable AND     *)
(*                 at most one of them contains STAR.                         *)
(*    - rule_enc:  ENC e1 e2 is derivable if e1 and e2 are derivable AND     *)
(*                 at most one of them contains STAR.                         *)
(******************************************************************************)

Inductive Derivable : Expr -> Prop :=
  | base_star : Derivable STAR
  | base_circ : Derivable CIRC
  | rule_dot : forall e1 e2,
      Derivable e1 ->
      Derivable e2 ->
      (occStar e1 = 0 \/ occStar e2 = 0) ->  (* Non-duplication constraint *)
      Derivable (DOT e1 e2)
  | rule_enc : forall e1 e2,
      Derivable e1 ->
      Derivable e2 ->
      (occStar e1 = 0 \/ occStar e2 = 0) ->  (* Non-duplication constraint *)
      Derivable (ENC e1 e2).


(******************************************************************************)
(* 4. The Non-Duplication Theorem                                              *)
(*    Theorem: If an expression 'e' is derivable, then occStar e <= 1.       *)
(*    This is the *core* theorem of the paper.                               *)
(******************************************************************************)

Lemma no_dup_star : forall e, Derivable e -> occStar e <= 1.
Proof.
  intros e Hd.
  induction Hd; simpl.
  - lia.  (* Case STAR: occStar STAR = 1 <= 1 *)
  - lia.  (* Case CIRC: occStar CIRC = 0 <= 1 *)
  - (* Case DOT a b *)
    specialize (IHHd1) as IH1.  (* Rename induction hypotheses for clarity *)
    specialize (IHHd2) as IH2.
    destruct H as [H0e1 | H0e2].  (* Hypothesis from rule_dot/rule_enc *)
    + rewrite H0e1 in *. lia.     (* If occStar e1 = 0, then the sum is <= 1 *)
    + rewrite H0e2 in *. lia.     (* If occStar e2 = 0, then the sum is <= 1 *)
  - (* Case ENC a b: Identical to DOT case *)
    specialize (IHHd1) as IH1.
    specialize (IHHd2) as IH2.
    destruct H as [H0e1 | H0e2].
    + rewrite H0e1 in *. lia.
    + rewrite H0e2 in *. lia.
Qed.


(******************************************************************************)
(* 5. Exhaustive Closure Lemma                                                *)
(*   Lemma: If e is derivable, it must be one of STAR, CIRC, DOT, or ENC     *)
(******************************************************************************)
Lemma closure_exhaustive : forall e,
  Derivable e ->
   (e = STAR)
   \/ (e = CIRC)
   \/ (exists e1 e2, e = DOT e1 e2 /\ Derivable e1 /\ Derivable e2 /\ (occStar e1 = 0 \/ occStar e2 = 0))
   \/ (exists e1 e2, e = ENC e1 e2 /\ Derivable e1 /\ Derivable e2 /\ (occStar e1 = 0 \/ occStar e2 = 0)).
Proof.
  intros e Hd.
  inversion Hd; subst.  (* Deconstruct the derivation of 'e' *)
  - left. reflexivity.   (* Case: e = STAR *)
  - right. left. reflexivity.  (* Case: e = CIRC *)
  - right. right. left.  (* Case: e = DOT e1 e2 *)
    exists e1, e2.
    repeat split; auto.  (* 'auto' can often solve simple goals *)
  - right. right. right. (* Case: e = ENC e1 e2 *)
    exists e1, e2.
    repeat split; auto.
Qed.


(******************************************************************************)
(* 6. The isDerivable Function (Boolean Parser)                               *)
(*    A recursive function that checks if an expression is derivable.       *)
(*    This is the *algorithmic* counterpart to the inductive predicate.     *)
(******************************************************************************)

Fixpoint isDerivable (e : Expr) : bool :=
  match e with
  | STAR => true
  | CIRC => true
  | DOT a b =>
      if isDerivable a && isDerivable b then
        if (Nat.eqb (occStar a) 0) || (Nat.eqb (occStar b) 0)
        then true else false
      else false
  | ENC a b =>
      if isDerivable a && isDerivable b then
        if (Nat.eqb (occStar a) 0) || (Nat.eqb (occStar b) 0)
        then true else false
      else false
  end.


(******************************************************************************)
(* 7. Equivalence Theorems: Parser <-> Derivability                           *)
(*    These lemmas prove that the 'isDerivable' function correctly implements *)
(*    the 'Derivable' predicate.                                            *)
(******************************************************************************)

(* Lemma: If isDerivable e = true, then e is Derivable. *)
Lemma parse_implies_derivable : forall e,
  isDerivable e = true -> Derivable e.
Proof.
  intro e.
  induction e; simpl; intros H.
  - apply base_star.
  - apply base_circ.
  - destruct (isDerivable e1 && isDerivable e2) eqn:He; try discriminate.
    destruct ((Nat.eqb (occStar e1) 0) || (Nat.eqb (occStar e2) 0)) eqn:Hc; try discriminate.
    apply rule_dot.
    + apply IHe1. apply andb_true_iff in He. destruct He; assumption.
    + apply IHe2. apply andb_true_iff in He. destruct He; assumption.
    + apply orb_true_iff in Hc. destruct Hc as [Hx|Hy].
      * left.  apply Nat.eqb_eq in Hx. assumption.
      * right. apply Nat.eqb_eq in Hy. assumption.
  - destruct (isDerivable e1 && isDerivable e2) eqn:He; try discriminate.
    destruct ((Nat.eqb (occStar e1) 0) || (Nat.eqb (occStar e2) 0)) eqn:Hc; try discriminate.
    apply rule_enc.
    + apply IHe1. apply andb_true_iff in He. destruct He; assumption.
    + apply IHe2. apply andb_true_iff in He. destruct He; assumption.
    + apply orb_true_iff in Hc. destruct Hc as [Hx|Hy].
      * left.  apply Nat.eqb_eq in Hx. assumption.
      * right. apply Nat.eqb_eq in Hy. assumption.
Qed.

(* Lemma: If e is Derivable, then isDerivable e = true. *)
Lemma derivable_implies_parse : forall e,
  Derivable e -> isDerivable e = true.
Proof.
  intros e Hd.
  induction Hd; simpl.
  - reflexivity.  (* Case STAR *)
  - reflexivity.  (* Case CIRC *)
  - (* Case DOT *)
    rewrite IHHd1, IHHd2.
    destruct (Nat.eqb (occStar e1) 0) eqn:Heq1;
    destruct (Nat.eqb (occStar e2) 0) eqn:Heq2; simpl.
    + reflexivity.
    + (* Case: occStar e1 = 0, occStar e2 != 0 *)
      apply Nat.eqb_eq in Heq1.
      reflexivity.
    + (* Case: occStar e1 != 0, occStar e2 = 0 *)
      apply Nat.eqb_eq in Heq2.
      reflexivity.
    + (* Case: occStar e1 != 0, occStar e2 != 0 *)
      destruct H as [He1 | He2].
      * apply Nat.eqb_eq in He1. rewrite He1 in Heq1. discriminate.
      * apply Nat.eqb_eq in He2. rewrite He2 in Heq2. discriminate.
  - (* Case ENC: Identical to DOT case *)
    rewrite IHHd1, IHHd2.
    destruct (Nat.eqb (occStar e1) 0) eqn:Heq1;
    destruct (Nat.eqb (occStar e2) 0) eqn:Heq2; simpl.
    + reflexivity.
    + apply Nat.eqb_eq in Heq1. reflexivity.
    + apply Nat.eqb_eq in Heq2. reflexivity.
    + destruct H as [He1 | He2].
      * apply Nat.eqb_eq in He1. rewrite He1 in Heq1. discriminate.
      * apply Nat.eqb_eq in He2. rewrite He2 in Heq2. discriminate.
Qed.


(******************************************************************************)
(* 8. Falsifiability Lemma                                                     *)
(*    Lemma: If occStar e >= 2, then e is NOT Derivable.                    *)
(*    This directly corresponds to the falsifiability criterion.            *)
(******************************************************************************)

Lemma falsifiabilite_locale : forall e,
  occStar e >= 2 -> ~ Derivable e.
Proof.
  intros e Hge Hder.
  pose proof (no_dup_star e Hder) as Hle.  (* Use the Non-Duplication Theorem *)
  lia.  (* Linear integer arithmetic: Hge (>= 2) and Hle (<= 1) are contradictory *)
Qed.