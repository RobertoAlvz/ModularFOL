Require Export unscoped header_extensible.

Require Export disjunctivesyntax implicativesyntax.

Reserved Notation "A ⊢ p" (at level 70).
Reserved Notation "A ⊢D p" (at level 70).

Notation "p ∨ q" := (inj (Disj _ p q)) (at level 60).

Section Disjunctive.
  Context {Sigma : Signature}.

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
  Notation "« p »" := (translate p).
  Notation "«/ A »" := (map translate A).

  Variable subst_form : (fin -> term) -> form -> form.
  Variable subst_form_inj : forall sigma p, subst_form sigma (inj p) = subst_form_disjunctive _ subst_form _ sigma p.
  Variable subst_dn : forall sigma p, subst_form sigma (¬¬p) = ¬¬(subst_form sigma p).
  Variable translation_subst : forall sigma q, «subst_form sigma q» = subst_form sigma «q».
  Lemma translation_subst_disj sigma p :  « subst_form_disjunctive _ subst_form _ sigma p » = subst_form sigma (translate_disj p).
  Proof. destruct p; cbn. unfold Disj_. rewrite translation_inj. cbn. rewrite subst_dn. repeat apply congr_Impl_.
    rewrite subst_form_inj. cbn. apply congr_Disj_; apply translation_subst. all: reflexivity.
  Defined.

End Disjunctive.

Section translation.
  Notation "A ⊢[ nd ] p" := (@nd_disj _ _ nd A p) (at level 70).
  Context {Sigma : Signature}.

  Require Import classical_deduction.
  Variable form : Type.
  Variable retract : retract (form_disjunctive form) form.
  Variable retract_implicative : included form_implicative form.

  Variable translate : form -> form.
  Notation "« p »" := (translate p).
  Notation "«/ A »" := (map translate A).

  Variable translation_inj : forall p, «inj p» = (translate_disj _ _  _ translate p).


  Variable nd : list form -> form -> Prop.
  Variable cnd : list form -> form -> Prop.

  Variable embed : forall A p, nd A p -> cnd A p.
  Lemma embed_disj A p : A ⊢[nd] p -> A ⊢[cnd] p.
  Proof. destruct 1; [ apply ndDI1 | apply ndDI2 | apply (ndDE _ _ _ _ p q) ]; now apply embed.
  Defined.

  Variable translation : forall A p, cnd A p -> nd «/A» «p».
  Lemma translation_disj A p: A ⊢[cnd] p -> «/A» ⊢[nd] «p».
  Proof. Admitted.

  Variable subst_form : (fin -> term) -> form -> form.
  Variable translation_subst : forall sigma q, «subst_form sigma q» = subst_form sigma «q».
  Lemma translation_subst_disj sigma q: «subst_form sigma (inj q)» = subst_form sigma «inj q».
  Proof. destruct q; repeat now rewrite translation_subst.
  Defined.

End translation.