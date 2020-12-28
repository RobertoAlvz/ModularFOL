Require Export unscoped header_extensible.
Require Export existentialsyntax implicativesyntax.
Require Import classical_deduction implicative_deduction.

Reserved Notation "A ⊢ p" (at level 70).
Reserved Notation "A ⊢_exst p" (at level 70).

Notation "∃ p" := (inj (Exist _ p)) (at level 60).

Section Existential.
  Context {Sigma : Signature}.

  Variable form : Type.
  Variable retract : retract (form_existential form) form.
  Variable subst_form : (fin -> term) -> form -> form.

  Variable nd : list form -> form -> Prop.
  Notation "A ⊢ p" := (nd A p) (at level 70).

  Definition up_ctx (A : list form) := map (subst_form (S >> var_term)) A.
  Inductive nd_exst (A : list form) : form -> Prop :=
    | ndEI p t : A ⊢ subst_form (scons t (var_term)) p -> A ⊢_exst (∃ p)
    | ndEE p q : A ⊢ (∃ p) -> p :: (up_ctx A) ⊢ subst_form (S >> var_term) q -> A ⊢_exst q
  where "A ⊢_exst p" := (nd_exst A p).

  Variable weakening : forall A B p, A ⊢ p -> incl A B -> B ⊢ p.
  Lemma weakening_exst A B p : A ⊢_exst p -> incl A B -> B ⊢_exst p.
  Proof. revert B. destruct 1; intro Hinc; [ now apply (ndEI _ p t), (weakening A) | apply (ndEE _ p q) ].
    -now apply (weakening A).
    -apply (weakening (p::up_ctx A)), incl_cons; [assumption | now left | apply incl_tl ].
      unfold up_ctx. now apply incl_map.
  Defined.

  Variable retract_implicative : included form_implicative form.

  Variable translate : form -> form.
  Definition translate_exst (p : form_existential form) : _ := match p with
    | Exist _ q => ¬¬(∃ (translate q))
  end.
  Notation "« p »" := (translate p).
  Notation "«/ A »" := (map translate A).


  Variable agree : forall A p, A ⊢_exst p -> A ⊢ p.
  Variable agree_cls : forall A p, nd_classic _ _ nd A p -> A ⊢ p.
  Variable agree_imp : forall A p, nd_imp _ _ nd A p -> A ⊢ p.
  Variable imp_nd : forall A p, nd_imp _ _ nd A p -> A ⊢ p.
  Variable subst_form_inj : forall sigma p, subst_form sigma (inj p) = subst_form_existential _ subst_form _ sigma p.
  Variable translation_inj : forall p, «inj p» = translate_exst  p.
  Variable aux : forall p, subst_form (scons (var_term 0) (var_term)) (subst_form (up_term_term (S >> var_term)) p) = p.
  Variable translation_bwd : forall A p, A ⊢ «p» <-> A ⊢ p.
  Lemma translation_bwd_exst A p: A ⊢ (translate_exst p) <-> A ⊢ inj p.
  Proof. destruct p. cbn. split; intro.
    - assert (Hc : A ⊢ ∃ «f»). {now apply agree_cls,ndDN. }
      apply (ndEE _ _ (∃ f)) in Hc. now apply agree. rewrite subst_form_inj. cbn. apply agree,(ndEI _ _ (var_term 0)).
      rewrite aux. apply translation_bwd, agree_imp,ndHyp. now left.
    -apply agree_imp,ndII,agree_imp,(ndIE _ _ _ _ (∃«f»)). apply agree_imp,ndHyp. now left.
      apply (weakening A). 2:now apply incl_tl. apply (ndEE _ _ (∃«f»)) in H. now apply agree.
      rewrite subst_form_inj. cbn. apply agree,(ndEI _ _ (var_term 0)). rewrite aux. apply translation_bwd.
      apply agree_imp,ndHyp. now left.
  Defined.

  Variable subst_dn : forall sigma p, subst_form sigma (¬¬p) = ¬¬(subst_form sigma p).
  Variable translation_subst : forall sigma q, «subst_form sigma q» = subst_form sigma «q».
  Lemma translation_subst_exst sigma p :  « subst_form_existential _ subst_form _ sigma p » = subst_form sigma (translate_exst p).
  Proof. destruct p; cbn. unfold Exist_. rewrite translation_inj. cbn. rewrite subst_dn. repeat apply congr_Impl_.
    rewrite subst_form_inj. cbn. apply congr_Exist_; apply translation_subst. all: reflexivity.
  Defined.

  Variable cut : forall A p q,  A ⊢ p -> (p :: A) ⊢ q -> A ⊢ q.
  Lemma translation_helper_exst A p : A ⊢ (¬¬(translate_exst p)) -> A ⊢ translate_exst p.
  Proof. destruct p. cbn. intro. apply (cut _ _ _ H). apply agree_imp,ndII,agree_imp,(ndIE _ _ _ _ (¬¬¬(∃«f»))).
    apply agree_imp,ndHyp. right. now left. apply agree_imp,ndII,agree_imp,(ndIE _ _ _ _ (¬(∃«f»))).
    apply agree_imp,ndHyp. now left. apply agree_imp,ndHyp. right. now left.
  Defined.

  Lemma translation_map A: up_ctx «/A» = «/up_ctx A».
  Proof. unfold up_ctx. repeat rewrite map_map. apply map_ext. intro p. symmetry. apply translation_subst.
  Qed.
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

  Variable weakening : forall A B p, nd A p -> incl A B -> nd B p.

(*   Lemma dn_int_exst A p: A ⊢[nd] p -> A ⊢[nd] (¬¬p).
  Proof. intro. apply imp_nd, ndII, imp_nd, (ndIE _ _ _ _ p).
    -apply imp_nd, ndHyp. now left.
    -now apply (weakening_exst _ _ _ _ weakening A), incl_tl.
  Qed. *)
  Variable dni : forall A p, nd A p -> nd A (¬¬p).

  Variable agree_cnd : forall A p, A ⊢[cnd] p -> cnd A p.
  Variable agree_nd : forall A p, A ⊢[nd] p -> nd A p. 
  Variable agree_cls : forall A p, nd_classic _ _ cnd A p -> cnd A p.
  Variable agree_imp : forall A p, nd_imp _ _ nd A p -> nd A p.
 Variable aux : forall p, subst_form (scons (var_term 0) (var_term)) (subst_form (up_term_term (S >> var_term)) p) = p.

  Variable translation : forall A p, cnd A p -> nd «/A» «p».
  Lemma translation_exst A p: A ⊢[cnd] p -> «/A» ⊢[nd] «p».
  Proof. destruct 1.
    -rewrite translation_inj. cbn. admit.
    -apply (ndEE _ _ _ _ _ «(subst_form (up_term_term (S >> var_term)) p)»).  apply agree_nd, (ndEI _ _ _ _ _ _ (var_term 0)).
      rewrite <- translation_subst. rewrite aux. apply translation. admit.
      rewrite <- translation_subst. rewrite translation_map. rewrite <- map_cons. apply translation.
      apply agree_cnd,(ndEE _ _ _ _ _ p).

  Admitted.
End translation.