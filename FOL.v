Require Export syntax.

Reserved Notation "A |- p" (at level 70).
Inductive deduction (formula : Type) (A : list formula) : formula -> Prop :=
  | ndHyp p : In p A -> A |- p
where "A |- p" := (deduction _ A p).

Lemma weakening (formula : Type) (A B : list formula) p : A |- p -> incl A B -> B |- p.
Proof. induction 1; intro Hinc. apply ndHyp. now apply (Hinc p). Qed.

Section implicative.
  Variable formula : Type.

  Inductive f_implicative : Type -> Type:=
    | Bot : f_implicative formula
    | Imp : formula -> formula -> f_implicative formula.
  Notation "p ~> q" := (Imp p q) (at level 51, right associativity).
  Notation "⊥" := (Bot).
  Notation "¬ p" := (p ~> ⊥) (at level 50).

  Reserved Notation "A |-I p" (at level 70).
(*   Is it correct to mix formula and f_implicative on the right of |- ? *)
  Inductive deduction_implicative (A : list formula) : formula + f_implicative formula -> Prop :=
    | ndExp p  : A |-I inr ⊥ -> A |-I inr p
    | ndII p q : p::A |- q  -> A |-I inr (p ~> q)
    | ndIE p q : A |-I inr (p ~> q)  ->  A |-I inl p  -> A |-I inl q
  where "A |-I p" := (deduction_implicative A p).

  Lemma weakening_imp A B p : A |-I p -> incl A B -> B |-I p.
  Proof. induction 1 as [ p nd | p q nd | p q nd_pq H1 nd_p ]; intro Hinc.
    -now apply ndExp, IHnd.
    -apply ndII. apply (weakening formula (p::A)). assumption.
     intros a [Hhd | Htl]. now left. right. now apply (Hinc a).
    -apply (ndIE _ p). now apply H1. now apply IHnd_p.
  Qed.

  Lemma double_neg A p : A |-I inr p -> A |-I ¬¬p.

End implicative.
