Require Export unscoped header_extensible.

Require Export existentialsyntax implicativesyntax.

Reserved Notation "A ⊢ p" (at level 70).
Reserved Notation "A ⊢E p" (at level 70).

Notation "∃ p" := (inj (Exist _ p)) (at level 60).

Section Existential.
  Variable form : Type.
  Variable retract : retract (form_existential form) form.
  Variable subst_form : (fin -> term) -> form -> form.

  Variable nd : list form -> form -> Prop.
  Notation "A ⊢ p" := (nd A p) (at level 70).

  Inductive nd_exst (A : list form) : form -> Prop :=
    | ndEI p t : A ⊢ subst_form (scons t (var_term)) p -> A ⊢E (∃ p)
    | ndEE p q : A ⊢ (∃ p) -> p :: A ⊢ q -> A ⊢E q
  where "A ⊢E p" := (nd_exst A p).
  Variable agree : forall A p, A ⊢E p -> A ⊢ p.

  Variable weakening : forall A B p, A ⊢ p -> incl A B -> B ⊢ p.
  Lemma weakening_exst A B p : A ⊢E p -> incl A B -> B ⊢E p.
  Proof. destruct 1; intro Hinc; [ now apply (ndEI _ p t), (weakening A) | apply (ndEE _ p q) ].
    -now apply (weakening A).
    -apply (weakening (p::A)), incl_cons; [assumption | now left | now apply incl_tl ].
  Defined.

  Variable retract_implicative : included form_implicative form.

  Variable translate : form -> form.
  Definition translate_exst (p : form_existential form) : _ := match p with
    | Exist _ q => ¬¬(∃ (translate q))
  end.

End Existential.

Section translation.

  Variable form : Type.
  Variable subst_form : (fin -> term) -> form -> form.
  Variable retract_existential : included form_existential form.
  Variable retract_implicative : included form_implicative form.
  Variable translate : form -> form.

  Notation "A ⊢[ nd ] p" := (@nd_exst _ _ subst_form nd A p) (at level 70).
  Notation "« p »" := (translate p).
  Notation "«/ A »" := (map translate A).

  Variable translation_inj : forall p, «inj p» = (translate_exst form  _ _ translate p).

  Require Import classical_deduction.

  Variable nd : list form -> form -> Prop.
  Variable cnd : list form -> form -> Prop.

  Variable embed : forall A p, nd A p -> cnd A p.
  Lemma embed_exst A p : A ⊢[nd] p -> A ⊢[cnd] p.
  Proof. destruct 1. now apply (ndEI _ _ _ _ _ _ t), embed. apply (ndEE _ _ _ _ _ p); now apply embed.
  Defined.

  Variable translation : forall A p, cnd A p -> nd «/A» «p».
  Lemma translation_exst A p: A ⊢[cnd] p -> «/A» ⊢[nd] «p».
  Proof. Admitted.
End translation.