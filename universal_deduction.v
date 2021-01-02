Require Export unscoped header_extensible.

Require Export implicativesyntax universalsyntax termsyntax.
Require Import classical_deduction implicative_deduction.

Reserved Notation "A ⊢ p" (at level 70).
Reserved Notation "A ⊢_univ p" (at level 70).

Section universals.
  Context {Sigma : Signature}.

  Variable form : Type.
  Variable retract_univ : retract (form_universal form) form.
  Variable subst_form : (fin -> term) -> form -> form.

  Variable count : form -> nat.
  Definition count_univ (p : form_universal form) : nat := match p with 
    | All _ p => count p
  end.

  Variable nd : list form -> form -> Prop.
  Notation "A ⊢ p" := (nd A p) (at level 70).

  Definition up_ctx (A : list form) := map (subst_form (S >> var_term)) A.
  Inductive nd_univ (A : list form) : form -> Prop :=
    | ndUI p : up_ctx A ⊢ p -> A ⊢_univ ∀ p
    | ndUE p t : A ⊢ ∀ p -> A ⊢_univ subst_form (scons t (var_term)) p
  where "A ⊢_univ p" := (nd_univ A p).

  Variable weakening : forall A B p, A ⊢ p -> incl A B -> B ⊢ p.
  Lemma weakening_univ A B p : A ⊢_univ p -> incl A B -> B ⊢_univ p.
  Proof. intro. revert B. destruct H; intros B Hinc; [ apply ndUI | now apply ndUE, (weakening A) ].
    -apply (weakening (up_ctx A) (up_ctx B)); [ assumption | unfold up_ctx ]. now apply incl_map.
  Defined.

  Variable translate : form -> form.
  Notation "« p »" := (translate p).
  Notation "«/ A »" := (map translate A).
  Definition translate_univ (p : form_universal form) : _ := match p with
    | All _ q => ∀ (translate q)
  end.

  Variable translation_inj : forall p, «inj p» = translate_univ  p.
  Variable subst_form_inj : forall sigma p, subst_form sigma (inj p) = subst_form_universal _ subst_form _ sigma p.
  Variable translation_subst : forall sigma q, «subst_form sigma q» = subst_form sigma «q».
  Lemma translation_subst_univ sigma p :  « subst_form_universal _ subst_form _ sigma p » = subst_form sigma (translate_univ p).
  Proof. destruct p. cbn. rewrite subst_form_inj. unfold All_. rewrite translation_inj. cbn. apply congr_All_, translation_subst.
  Defined.

  Variable agree : forall A p, nd_univ A p -> A ⊢ p.
  Variable  cut : forall A p q, A ⊢ p -> (p :: A) ⊢ q -> A ⊢ q.
  Variable subst_helper : forall p, subst_form (scons (var_term 0) (var_term)) (subst_form (up_term_term (S >> var_term)) p) = p.

  Variable retract_imp : retract (form_implicative form) form.
  Variable subst_form_inj_imp : forall sigma p, subst_form sigma (inj p) = subst_form_implicative _ subst_form _ sigma p.
  Variable agree_imp : forall A p, nd_imp _ _ nd A p -> A ⊢ p.
  Variable translation_bwd : forall A p,  A ⊢ «p» <-> A ⊢ p.
  Lemma translation_bwd_univ A p: A ⊢ translate_univ p <-> A ⊢ inj p.
  Proof. destruct p. cbn. split; intro; apply (cut _ _ _ H), agree,ndUI,translation_bwd; cbn;
    rewrite subst_form_inj; cbn; rewrite <- subst_helper;
    apply agree,ndUE, agree_imp,ndHyp; now left.
  Defined.

  Lemma translation_map A: up_ctx «/A» = «/up_ctx A».
  Proof. unfold up_ctx. repeat rewrite map_map. apply map_ext. intro p. symmetry. apply translation_subst.
  Qed.
  Variable translation_helper : forall p A, A ⊢ (¬¬«p») -> A ⊢ «p».
  Lemma translation_helper_univ A p : A ⊢ (¬¬(translate_univ p)) -> A ⊢ translate_univ p.
  Proof. intro H. apply (cut _ _ _ H). destruct p. cbn. apply agree,ndUI, translation_helper. cbn.
    repeat (rewrite subst_form_inj_imp; cbn ).
    apply agree_imp,ndII,agree_imp,(ndIE _ _ _ _ (¬(subst_form (S >> var_term) (∀«f»)))).
    apply agree_imp,ndHyp. right. now left.
    apply agree_imp,ndII,agree_imp,(ndIE _ _ _ _ «f»). apply agree_imp,ndHyp. right. now left.
    rewrite subst_form_inj. cbn. rewrite <- subst_helper. apply agree,ndUE,agree_imp,ndHyp. now left.
  Defined.

End universals.

Notation "A ⊢_univ p" := (nd_univ A p) (at level 70).

Section translation.
  Context {Sigma : Signature}.

  Variable form : Type.
  Variable nd : list form -> form -> Prop.
  Variable cnd : list form -> form -> Prop.
  Variable subst_form : (fin -> term) -> form -> form.
  Variable retract_univ : retract (form_universal form) form.
  Variable translate : form -> form.

  Notation "A ⊢[ nd ] p" := (@nd_univ _ form _ subst_form nd A p) (at level 70).
  Notation "« p »" := (translate p).
  Notation "«/ A »" := (map translate A).

  Variable translation_inj : forall p, «inj p» = translate_univ _ _ translate p.
  Variable translation_subst : forall sigma q, «subst_form sigma q» = subst_form sigma «q».

(*   Lemma translation_subst_univ sigma q: «subst_form sigma (inj q)» = subst_form sigma «inj q».
  Proof. destruct q. rewrite translation_subst. rewrite translation_inj. auto.
  Defined. *)


  Variable translation : forall A p, cnd A p -> nd «/A» «p».
  Lemma translation_univ A p: A ⊢[cnd] p -> «/A» ⊢[nd] «p».
  Proof. destruct 1.
    -rewrite translation_inj. cbn. apply ndUI. rewrite translation_map. now apply translation. now apply translation_subst.
    -rewrite translation_subst. apply ndUE. { pose (translation_inj (All _ p)). cbn in e. rewrite <- e. now apply translation. }
  Defined.

  Variable embed : forall A p, nd A p -> cnd A p.
  Lemma embed_univ A p : A ⊢[nd] p -> A ⊢[cnd] p.
  Proof. destruct 1; [ now apply ndUI, embed | now apply ndUE, embed ].
  Defined.

End translation.