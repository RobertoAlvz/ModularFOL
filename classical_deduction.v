Require Export implicativesyntax.

Reserved Notation "A ⊢ p" (at level 70).
Reserved Notation "A ⊢c p" (at level 70).


Section classical.
  Context {Sigma : Signature}.

  Variable form : Type.
  Variable retract_implicative : included form_implicative form.

  Variable nd : list form -> form -> Prop.
  Notation "A ⊢ p" := (nd A p) (at level 70).

  Inductive nd_classic (A : list form) : form -> Prop :=
    | ndDN p : A ⊢ (¬¬p) -> A ⊢c p
  where "A ⊢c p" := (nd_classic A p).

(* Variable agree : forall A p, A ⊢I p -> A ⊢ p. *)

  Variable weakening : forall A B p, A ⊢ p -> incl A B -> B ⊢ p.
  Lemma weakening_classic A B p: A ⊢c p -> incl A B -> B ⊢c p.
  Proof. destruct 1. intro. now apply ndDN, (weakening A).
  Defined.

End classical.

Notation "A ⊢c p" := (nd_classic A p) (at level 70).

Section translation.

  Variable form : Type.
  Variable nd : list form -> form -> Prop.
  Variable cnd : list form -> form -> Prop.
  Variable retract_implicative : included form_implicative form.

  Notation "A ⊢[ nd ] p" := (@nd_classic form _ nd A p) (at level 70).
  Variable translate : form -> form.
  Notation "« p »" := (translate p).
  Notation "«/ A »" := (map translate A).
  Variable dne : forall A p, cnd A (¬¬p) -> cnd A p.

  Variable embed : forall A p, nd A p -> cnd A p.
  Lemma embed_class A p : A ⊢[nd] p -> A ⊢[cnd] p.
  Proof. destruct 1. now apply ndDN, embed.
  Defined.

  Variable dn_int : forall A p , nd A p -> nd A (¬¬p).

  Variable translation : forall A p, cnd A p -> nd «/A» «p».
  Lemma translation_class A p: A ⊢[cnd] p -> nd «/A» «p».
  Proof. destruct 1. apply dne in H. now apply translation.
  Defined.
End translation.