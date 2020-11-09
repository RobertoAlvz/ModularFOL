Require Import Coq.Vectors.Vector.
From Coq Require Import List.
Import ListNotations.

Class Signature := Sig { Funcs : Type; f_ar : Funcs -> nat ; Preds : Type; p_ar : Preds -> nat }.

Context {Sigma : Signature}.

Inductive term : Type :=
  | Var (x : nat)
  | Func : forall f:Funcs, Vector.t term (f_ar f) -> term.

Fixpoint subst_term (sigma : nat -> term) (s : term) : term := match s with 
  | Var n => sigma n
  | Func f args => Func f (Vector.map (subst_term sigma) args)
end.

Inductive formula : Type :=
  | Bot
  | Pred : forall (P : Preds), Vector.t term (p_ar P) -> formula
  | Imp (p q : formula)
  | Univ (p : formula).

Fixpoint subst_form (sigma : nat -> term) (s : formula) : formula := match s with
  | Bot => Bot
  | Pred P args => Pred P (Vector.map (subst_term sigma) args)
  | Imp p q => Imp (subst_form sigma p) (subst_form sigma q)
  | Univ p => Univ (subst_form (fun n => sigma (S n)) p)
end.

Notation "p ~> q" := (Imp p q) (at level 51, right associativity).
Notation "! p" := (p ~> Bot) (at level 35, right associativity).

Definition instantiate t := subst_form (fun n => match n with 0 => t | n => Var n end).
Definition shifted := map (subst_form (fun n => Var (S n))).

Reserved Notation "H |- p" (at level 70).
Implicit Types H : list formula.
Inductive nd H : formula -> Prop :=
  | ndHyp p  : In p H -> H |- p
  | ndExp p  : H |- Bot  ->  H |- p
  | ndII p q : p::H |- q  -> H |- p ~> q
  | ndIE p q : H |- p ~> q  ->  H |- p  -> H |- q
  | ndUI p : shifted H |- p -> H |- Univ p
  | ndUE t p : H |- Univ p -> H |- instantiate t p 
where "H |- p" := (nd H p).

Theorem weakening A B p : A |- p -> incl A B -> B |- p.
Proof. induction 1; intro Hinc.
  -apply ndHyp. now apply (Hinc p).
  -now apply ndExp, IHnd.
  -apply ndII. admit.
  -apply (ndIE _ _ _ (IHnd1 Hinc) (IHnd2 Hinc)).
  -apply ndUI. admit.
  -now apply ndUE, IHnd.
Admitted.

Theorem double_neg_int H p : H |- p -> H |- !!p.
Proof. induction 1; apply ndII.
  -assert (!p :: H |- !p). {apply ndHyp. now left. }
   assert (!p :: H |- p). {apply ndHyp. now right. }
   apply (ndIE _ _ _ H1 H2).
  -apply (weakening H _ ). assumption. intros p1 H1. now right.
  -admit.
  -admit.
  -admit.
  -admit.
Admitted.