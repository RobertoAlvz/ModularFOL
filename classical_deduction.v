Require Export implicativesyntax.

Reserved Notation "A ⊢ p" (at level 70).
Reserved Notation "A ⊢c p" (at level 70).


Section classical.

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