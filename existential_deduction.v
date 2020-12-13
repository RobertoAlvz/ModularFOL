Require Export unscoped header_extensible.
Require Export existentialsyntax implicativesyntax.
Require Import classical_deduction implicative_deduction.

Reserved Notation "A ⊢ p" (at level 70).
Reserved Notation "A ⊢E p" (at level 70).

Notation "∃ p" := (inj (Exist _ p)) (at level 60).

Section Existential.
  Context {Sigma : Signature}.

  Variable form : Type.
  Variable retract : retract (form_existential form) form.
  Variable subst_form : (fin -> term) -> form -> form.

  Variable nd : list form -> form -> Prop.
  Notation "A ⊢ p" := (nd A p) (at level 70).

  Inductive nd_exst (A : list form) : form -> Prop :=
    | ndEI p t : A ⊢ subst_form (scons t (var_term)) p -> A ⊢E (∃ p)
    | ndEE p q : A ⊢ (∃ p) -> p :: A ⊢ q -> A ⊢E q
  where "A ⊢E p" := (nd_exst A p).

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
  Notation "« p »" := (translate p).
  Notation "«/ A »" := (map translate A).

  Variable agree : forall A p, A ⊢E p -> A ⊢ p.
  Variable dne : forall A p, A ⊢ (¬¬p) -> A ⊢ p.
  Variable dni : forall A p, A ⊢ p -> A ⊢ (¬¬p).
  Variable subst_var: forall p, subst_form (var_term 0, var_term) p = p.
  Variable imp_nd : forall A p, nd_imp _ _ nd A p -> A ⊢ p.
  Variable translation_inj : forall p, «inj p» = translate_exst  p.
  Variable translation_bwd : forall A p, A ⊢ «p» -> A ⊢ p.
  Lemma translation_bwd_disj A p: A ⊢E (translate_exst p) -> A ⊢E inj p.
  Proof. destruct p; cbn. intro. apply agree, dne in H. apply (ndEE _ _ (∃ f)) in H. assumption.
    -apply agree, (ndEI _ _ (var_term 0)). rewrite subst_var. apply translation_bwd, imp_nd, ndHyp. now left.
  Defined.


  Variable subst_form_inj : forall sigma p, subst_form sigma (inj p) = subst_form_existential _ subst_form _ sigma p.
  Variable subst_dn : forall sigma p, subst_form sigma (¬¬p) = ¬¬(subst_form sigma p).
  Variable translation_subst : forall sigma q, «subst_form sigma q» = subst_form sigma «q».
  Lemma translation_subst_exst sigma p :  « subst_form_existential _ subst_form _ sigma p » = subst_form sigma (translate_exst p).
  Proof. destruct p; cbn. unfold Exist_. rewrite translation_inj. cbn. rewrite subst_dn. repeat apply congr_Impl_.
    rewrite subst_form_inj. cbn. apply congr_Exist_; apply translation_subst. all: reflexivity.
  Defined.

End Existential.

Section translation.
  Context {Sigma : Signature}.

  Variable form : Type.
  Variable nd : list form -> form -> Prop.
  Variable cnd : list form -> form -> Prop.
  Variable subst_form : (fin -> term) -> form -> form.
  Variable retract_implicative : included form_implicative form.
  Variable retract_existential : included form_existential form.
  Variable translate : form -> form.

  Notation "A ⊢[ nd ] p" := (@nd_exst _ _ _ subst_form nd A p) (at level 70).
  Notation "« p »" := (translate p).
  Notation "«/ A »" := (map translate A).

  Variable translation_inj : forall p, «inj p» = translate_exst _ _ _ translate p.
  Variable translation_subst : forall sigma q, «subst_form sigma q» = subst_form sigma «q».

  Variable embed : forall A p, nd A p -> cnd A p.
  Lemma embed_exst A p : A ⊢[nd] p -> A ⊢[cnd] p.
  Proof. destruct 1. now apply (ndEI _ _ _ _ _ _ t), embed. apply (ndEE _ _ _ _ _ p); now apply embed.
  Defined.

  Variable imp_nd : forall A p, nd_imp form _ (nd_exst _ _ subst_form nd) A p -> A ⊢[nd] p.
  Variable weakening : forall A B p, nd A p -> incl A B -> nd B p.

  Lemma dn_int_exst A p: A ⊢[nd] p -> A ⊢[nd] (¬¬p).
  Proof. intro. apply imp_nd, ndII, imp_nd, (ndIE _ _ _ _ p).
    -apply imp_nd, ndHyp. now left.
    -now apply (weakening_exst _ _ _ _ weakening A), incl_tl.
  Qed.
  Variable translation : forall A p, cnd A p -> nd «/A» «p».
  Lemma translation_exst A p: A ⊢[cnd] p -> «/A» ⊢[nd] «p».
  Proof. destruct 1.
    -rewrite translation_inj. apply dn_int_exst, (ndEI _ _ _ _ _ _ t). rewrite <- translation_subst. now apply translation.
    -apply (ndEE _ _ _ _ _ «p»). admit. rewrite <- map_cons. now apply translation.
  Admitted.
End translation.