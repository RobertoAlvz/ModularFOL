Require Export syntax.


Notation "p ~> q" := (In_form_imp (Impl _ p q)) (at level 60).
Notation "⊥" := (In_form_imp (Fal _)).
Notation "¬ p" := (p ~> ⊥) (at level 60).

Reserved Notation "A |- p" (at level 70).
Inductive nd (A : list form) : form -> Prop :=
  | ndHyp p : In p A -> A |- p
  | ndExp p : A |- In_form_imp (Fal _)  -> A |- p
  | ndII p q : p :: A |- q -> A |- In_form_imp (Impl _ p q)
  | ndIE p q : A |- In_form_imp (Impl _ p q) -> A |- p -> A |- q
where "A |- p" := (nd A p).

Lemma weakening A B p : A |- p -> incl A B -> B |- p.
Proof. induction 1; intro Hinc.
  -apply ndHyp. now apply (Hinc p).
  -apply ndExp. now apply IHnd.
  -apply ndII. admit.
  -apply (ndIE _ p). now apply IHnd1. now apply IHnd2.
Admitted.

Lemma double_neg A p : A |- p -> A |- In_form_imp ()

