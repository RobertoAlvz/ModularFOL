Require Export unscoped header_extensible.

Require Export conjunctivesyntax implicativesyntax.

Reserved Notation "A ⊢ p" (at level 70).
Reserved Notation "A ⊢C p" (at level 70).

Notation "p ∧ q" := (Conj_ _ _ p q) (at level 60).

Section Conjunctive.
  Variable form : Type.
  Variable retract : retract (form_conjunctive form) form.

  Variable nd : list form -> form -> Prop.
  Notation "A ⊢ p" := (nd A p) (at level 70).

  Inductive nd_conj (A : list form) : form -> Prop :=
    | ndCI p q : A ⊢ p -> A ⊢ q -> A ⊢C (p ∧ q)
    | ndCE1 p q : A ⊢ p ∧ q -> A ⊢C p
    | ndCE2 p q : A ⊢ p ∧ q -> A ⊢C q
  where "A ⊢C p" := (nd_conj A p).
  Variable agree : forall A p, A ⊢C p -> A ⊢ p.

  Variable weakening : forall A B p, A ⊢ p -> incl A B -> B ⊢ p.
  Lemma weakening_conj A B p : A ⊢C p -> incl A B -> B ⊢C p.
  Proof. destruct 1; intro Hinc.
    -apply ndCI. all: now apply (weakening A).
    -now apply (ndCE1 _ _ q), (weakening A).
    -now apply (ndCE2 _ p q), (weakening A).
  Defined.

  Variable translate : form -> form.
  Definition translate_conj (p : form_conjunctive form) : form := match p with
    | Conj _ p q => (translate p) ∧ (translate q)
  end.

End Conjunctive.