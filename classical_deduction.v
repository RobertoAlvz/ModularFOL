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


Section translation.

  Variable form : Type.
  Variable nd : list form -> form -> Prop.
  Variable cnd : list form -> form -> Prop.
  Variable retract_implicative : included form_implicative form.

  Notation "A ⊢[ nd ] p" := (@nd_classic form _ nd A p) (at level 70).
  Variable translate : form -> form.
  Notation "« p »" := (translate p).
  Notation "«/ A »" := (map translate A).

  Variable translation_helper : forall A p, nd A (¬¬«p») -> nd A «p».
  Variable translation_dn : forall p, «¬¬p» = ¬¬«p».

  Variable translation : forall A p, cnd A p -> nd «/A» «p».
  Lemma translation_cls A p: A ⊢[cnd] p -> nd «/A» «p».
  Proof. destruct 1. apply translation_helper. rewrite <- translation_dn. now apply translation.
  Defined.

End translation.

Notation "A ⊢_c p" := (nd_classic A p) (at level 70).