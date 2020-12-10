Require Export unscoped header_extensible.

Require Export disjunctivesyntax implicativesyntax.

Reserved Notation "A ⊢ p" (at level 70).
Reserved Notation "A ⊢D p" (at level 70).

Notation "p ∨ q" := (Disj_ _ _ p q) (at level 60).

Section Disjunctive.
  Variable form : Type.
  Variable retract : retract (form_disjunctive form) form.

  Variable nd : list form -> form -> Prop.
  Notation "A ⊢ p" := (nd A p) (at level 70).

  Inductive nd_disj (A : list form) : form -> Prop :=
    | ndDI1 p q : A ⊢ p -> A ⊢D p ∨ q
    | ndDI2 p q : A ⊢ q -> A ⊢D p ∨ q
    | ndDE p q r: A ⊢ p ∨ q -> p::A ⊢ r -> q::A ⊢ r -> A ⊢D r
  where "A ⊢D p" := (nd_disj A p).
  Variable agree : forall A p, A ⊢D p -> A ⊢ p.

  Variable weakening : forall A B p, A ⊢ p -> incl A B -> B ⊢ p.
  Lemma weakening_disj A B p : A ⊢D p -> incl A B -> B ⊢D p.
  Proof. destruct 1; intro Hinc; [ now apply ndDI1, (weakening A) | now apply ndDI2, (weakening A) | ].
    -apply (ndDE _ p q). now apply (weakening A).
      +apply (weakening (p::A)), incl_cons; [assumption | now left | now apply incl_tl ].
      +apply (weakening (q::A)), incl_cons; [assumption | now left | now apply incl_tl ].
  Defined.

  Variable retract_implicative : included form_implicative form.

  Variable translate : form -> form.
  Definition translate_disj (p : form_disjunctive form) : _ := match p with
    | Disj _ p q => ¬¬((translate p) ∨ (translate q))
  end.

End Disjunctive.