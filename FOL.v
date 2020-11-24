Require Export syntax.

Section implicative.

  Variable form : Type.
  
  Variable count : form -> nat.

  Variable nd : list form -> form -> Prop.
  Notation "A ⊢ p" := (nd A p) (at level 70).
  Variable ndHyp : forall A p, In p A -> A ⊢ p.

(*   Notation "« p »" := (In_form_implicative p).
  Notation "p ~> q" := (Impl _ «p» «q») (at level 60). *)
  Notation "⊥" := (Fal _).
  Notation "¬ p" := (p ~> ⊥) (at level 60).

  Definition count_imp (p : form_implicative form) := match p with
    | ⊥ => 1
    | Impl _ p q => count p + count q
  end.

  Reserved Notation "A |- p" (at level 70).
  Inductive nd_imp (A : list (form_implicative form)) : form_implicative form -> Prop :=
    | ndExp p : A |- ⊥ -> A |- p
    | ndII p q : (p :: A) |- q -> A |- p ~> q
    | ndIE p q : A |- p ~> q -> A |- p -> A |- q
  where "A |- p" := (nd_imp A p).

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

  Variable form : Type.
    
  Variable count : form -> nat.
  Notation "| p |" := count p.

  Variable nd : list form -> form -> Prop.
  Notation "A ⊢ p" := (nd A p).

  Notation "« p »" := (In_form_univ p).
  Notation "∀ p ":= (All _ p) (at level 60).

  Definition count_univ (p : form_univ form) : nat := match p with 
    | ∀ p => |p|
  end.

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