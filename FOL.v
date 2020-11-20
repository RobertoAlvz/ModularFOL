Require Export syntax.

Section implicative.

  Notation "« p »" := (In_form_imp p).
  Notation "p ~> q" := (Impl _ «p» «q») (at level 60).
  Notation "⊥" := (Fal _).
  Notation "¬ p" := (p ~> ⊥) (at level 60).

  Reserved Notation "A |- p" (at level 70).
  Inductive nd (A : list (form_imp form)) : form_imp form -> Prop :=
    | ndHyp p : In p A -> A |- p
    | ndExp p : A |- ⊥  -> A |- p
    | ndII p q : p :: A |- q -> A |- p ~> q
    | ndIE p q : A |- p ~> q -> A |- p  -> A |- q
  where "A |- p" := (nd A p).

  Lemma weakening A B p : A |- p -> incl A B -> B |- p.
  Proof. induction 1; intro Hinc.
    -apply ndHyp. now apply (Hinc p).
    -apply ndExp. now apply IHnd.
    -apply ndII. admit.
    -apply (ndIE _ p). now apply IHnd1. now apply IHnd2.
  Admitted.

  Lemma double_neg A p : A |- p -> A |- ¬¬p.
  Proof. induction 1; apply ndII.
    -apply (ndIE _ p). apply ndHyp. now left. apply ndHyp. now right.
    -apply (weakening A). assumption.
     {intros a Hin. now right. }
    -apply (ndIE _ (p~>q)). {apply ndHyp. now left. } apply ndII, (weakening (p::A)). assumption.
     intros a [Hhd | Htl]. now left. right. now right.
    -apply (ndIE _ q). apply ndHyp. now left.
     apply (weakening A). { now apply (ndIE _ p). }
     { intros a Hin. now right. }
  Qed.

End implicative.

Section universals.

  Notation "« p »" := (In_form_univ p).
  Notation "∀ p ":= (All _ «p») (at level 60).

  Definition shifted : list (form_univ form) -> list (form_univ form)
    := fun l => l.
  Definition subst : form_univ form -> term -> form_univ form
    := fun f t => f.

  Reserved Notation "A |- p" (at level 70).
  Inductive ndU (A : list (form_univ form)) : form_univ form -> Prop :=
    | ndUI p : shifted A |- p -> A |- ∀ p
    | ndUE p t : A |- ∀ p -> A |- subst p t
  where "A |- p" := (ndU A p).

  Lemma weakening_univ A B p : A |- p -> incl A B -> B |- p.
  Proof.
  Admitted.

  Lemma double_neg A p : A |- p -> A |- ¬¬p.
  Proof.
  Admitted.

End universals.