Require Export unscoped header_extensible.

Require Export atomicsyntax implicativesyntax.

Reserved Notation "A ⊢ p" (at level 70).
Reserved Notation "A ⊢A p" (at level 70).

Section atomic.
  Variable form : Type.
  Variable retract : retract (form_atomic) form.

  Variable nd : list form -> form -> Prop.
  Notation "A ⊢ p" := (nd A p) (at level 70).

  Inductive nd_atomic (A : list form) : form -> Prop :=
    | ndAgree p : A ⊢ p -> A ⊢A p
    | ndAH p : In p A -> A ⊢A p
  where "A ⊢A p" := (nd_atomic A p).
  Variable agree : forall A p, A ⊢A p -> A ⊢ p.

  Variable weakening : forall A B p, A ⊢ p -> incl A B -> B ⊢ p.
  Lemma weakening_atomic A B p : A ⊢A p -> incl A B -> B ⊢A p.
  Proof. destruct 1; intro Hinc;
     [ now apply ndAgree, (weakening A)
     | now apply ndAH, (Hinc p) ].
  Defined.

  Variable retract_implicative : included form_implicative form.

  Variable translate : form -> form.
  Definition translate_atomic (p : form_atomic) : form := ¬¬(inj p).

  Variable translation_int : forall A p, A ⊢ p -> (map translate A) ⊢ (translate p).
  Lemma translation_int_atom A p : A ⊢A p -> (map translate A) ⊢A (translate p).
  Proof. intro. now apply ndAgree, translation_int, agree.
  Defined.

  Variable translation_elim : forall A p, (map translate A) ⊢ (translate p) -> A ⊢ p.
  Lemma translation_elim_atom A p : (map translate A) ⊢A (translate p) -> A ⊢A p.
  Proof. intro. now apply ndAgree, translation_elim, agree.
  Defined.

End atomic.