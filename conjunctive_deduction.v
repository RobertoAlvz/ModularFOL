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
    | ndAgree p : A ⊢ p -> A ⊢C p
    | ndCI p q : A ⊢ p -> A ⊢ q -> A ⊢C (p ∧ q)
    | ndCE1 p q : A ⊢ p ∧ q -> A ⊢C p
    | ndCE2 p q : A ⊢ p ∧ q -> A ⊢C q
  where "A ⊢C p" := (nd_conj A p).
  Variable agree : forall A p, A ⊢C p -> A ⊢ p.

  Variable weakening : forall A B p, A ⊢ p -> incl A B -> B ⊢ p.
  Lemma weakening_conj A B p : A ⊢C p -> incl A B -> B ⊢C p.
  Proof. destruct 1; intro Hinc.
    -now apply ndAgree, (weakening A).
    -apply ndCI. all: now apply (weakening A).
    -now apply (ndCE1 _ _ q), (weakening A).
    -now apply (ndCE2 _ p q), (weakening A).
  Defined.

  Variable retract_implicative : included form_implicative form.
(*   Variable retract_imp_conj : included form_implicative (form_conjunctive form). *)

  Variable translate : form -> form.
  Definition translate_conj (p : form_conjunctive form) : form := match p with
    | Conj _ p q => ¬¬((translate p) ∧ (translate q))
  end.

  Variable translation_int : forall A p, A ⊢ p -> (map translate A) ⊢ (translate p).
  Lemma translation_int_conj A p : A ⊢C p -> (map translate A) ⊢C (translate p).
  Proof. intro. apply agree in H. apply translation_int in H. now apply ndAgree.
  Defined.

  Variable translation_elim : forall A p, (map translate A) ⊢ (translate p) -> A ⊢ p.
  Lemma translation_elim_conj A p : (map translate A) ⊢C (translate p) -> A ⊢C p.
  Proof. intro. now apply ndAgree, translation_elim, agree.
  Defined.

End Conjunctive.