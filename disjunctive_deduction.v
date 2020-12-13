Require Export unscoped header_extensible.
Require Export disjunctivesyntax implicativesyntax.
Require Import classical_deduction implicative_deduction.

Reserved Notation "A ⊢ p" (at level 70).
Reserved Notation "A ⊢_disj p" (at level 70).

Notation "p ∨ q" := (inj (Disj _ p q)) (at level 60).

Section Disjunctive.
  Context {Sigma : Signature}.

  Variable form : Type.
  Variable retract : retract (form_disjunctive form) form.

  Variable nd : list form -> form -> Prop.
  Notation "A ⊢ p" := (nd A p) (at level 70).

  Inductive nd_disj (A : list form) : form -> Prop :=
    | ndDI1 p q : A ⊢ p -> A ⊢_disj p ∨ q
    | ndDI2 p q : A ⊢ q -> A ⊢_disj p ∨ q
    | ndDE p q r: A ⊢ p ∨ q -> p::A ⊢ r -> q::A ⊢ r -> A ⊢_disj r
  where "A ⊢_disj p" := (nd_disj A p).

  Variable weakening : forall A B p, A ⊢ p -> incl A B -> B ⊢ p.
  Lemma weakening_disj A B p : A ⊢_disj p -> incl A B -> B ⊢_disj p.
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

  Variable agree : forall A p, A ⊢_disj p -> A ⊢ p.
  Variable dne : forall A p, A ⊢ (¬¬p) -> A ⊢ p.
  Variable dni : forall A p, A ⊢ p -> A ⊢ (¬¬p).
  Variable imp_nd : forall A p, nd_imp _ _ nd A p -> A ⊢ p.
  Variable translation_inj : forall p, «inj p» = translate_disj  p.
  Variable translation_bwd : forall A p, «/A» ⊢ «p» -> A ⊢ p.
  Lemma translation_bwd_disj A p: «/A» ⊢ (translate_disj p) -> A ⊢ inj p.
  Proof. destruct p; cbn.  intro. apply dne in H. apply (ndDE _ _ _ «f ∨ f0») in H; [ now apply translation_bwd, agree | | ];
    rewrite translation_inj; cbn; now apply dni, (weakening «/A»), incl_tl.
  Defined.

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

  Variable form : Type.
  Variable nd : list form -> form -> Prop.
  Variable cnd : list form -> form -> Prop.
  Variable retract : retract (form_disjunctive form) form.
  Variable retract_implicative : included form_implicative form.

  Variable translate : form -> form.
  Notation "« p »" := (translate p).
  Notation "«/ A »" := (map translate A).
  Variable translation_inj : forall p, «inj p» = (translate_disj _ _  _ translate p).


  Variable embed : forall A p, nd A p -> cnd A p.
  Lemma embed_disj A p : A ⊢[nd] p -> A ⊢[cnd] p.
  Proof. destruct 1; [ apply ndDI1 | apply ndDI2 | apply (ndDE _ _ _ _ p q) ]; now apply embed.
  Defined.

  Variable imp_nd : forall A p, nd_imp form _ (nd_disj _ _ nd) A p -> A ⊢[nd] p.
  Variable weakening : forall A B p, nd A p -> incl A B -> nd B p.

  Lemma dn_int_disj A p: A ⊢[nd] p -> A ⊢[nd] (¬¬p).
  Proof. intro. apply imp_nd, ndII, imp_nd, (ndIE _ _ _ _ p).
    -apply imp_nd, ndHyp. now left.
    -now apply (weakening_disj _ _ _ weakening A), incl_tl.
  Qed.

  Variable disj_cnd : forall A p, cnd A p -> A ⊢[cnd] p.
  Variable translation : forall A p, cnd A p -> nd «/A» «p».
  Lemma translation_disj A p: A ⊢[cnd] p -> «/A» ⊢[nd] «p».
  Proof. destruct 1.
    -rewrite translation_inj. cbn. now apply dn_int_disj, ndDI1, translation.
    -rewrite translation_inj. cbn. now apply dn_int_disj, ndDI2, translation.
    -apply (ndDE _ _ _ _ «p» «q»).

 Admitted.

End translation.