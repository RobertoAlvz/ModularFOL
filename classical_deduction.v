Require Export implicativesyntax.
Require Export implicative_deduction.

Reserved Notation "A ⊢ p" (at level 70).
Reserved Notation "A ⊢_c p" (at level 70).

Section classical.
  Context {Sigma : Signature}.

  Variable form : Type.
  Variable retract_implicative : included form_implicative form.

  Variable nd : list form -> form -> Prop.
  Notation "A ⊢ p" := (nd A p) (at level 70).

  Inductive nd_classic (A : list form) : form -> Prop :=
    | ndDN p : A ⊢ (¬¬p) -> A ⊢_c p
  where "A ⊢_c p" := (nd_classic A p).

  Variable agree : forall A p, A ⊢_c p -> A ⊢ p.

  Variable weakening : forall A B p, A ⊢ p -> incl A B -> B ⊢ p.
  Lemma weakening_classic A B p: A ⊢_c p -> incl A B -> B ⊢ p.
  Proof. destruct 1. intro. now apply agree,ndDN, (weakening A).
  Defined.

End classical.

Notation "A ⊢_c p" := (nd_classic A p) (at level 70).