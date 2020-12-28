Require Export unscoped header_extensible.

Require Export atomicsyntax implicativesyntax.
Require Import classical_deduction.

Reserved Notation "A ⊢ p" (at level 70).
Reserved Notation "A ⊢A p" (at level 70).

Section atomic.
  Context {Sigma : Signature}.

  Variable form : Type.

  Variable retract : retract (form_atomic) form.
  Variable retract_implicative : included form_implicative form.

  Variable translate : form -> form.
  Definition translate_atomic (p : form_atomic) : form := ¬¬(inj p).
  Notation "« p »" := (translate p).
  Notation "«/ A »" := (map translate A).

  Variable translation_inj : forall p, «inj p» = translate_atomic  p.
  Variable subst_form : (fin -> term) -> form -> form.
  Variable subst_form_inj : forall sigma p, subst_form sigma (inj p) = subst_form_atomic _ _ sigma p.
  Variable subst_dn : forall sigma p, subst_form sigma (¬¬p) = ¬¬(subst_form sigma p).
  Variable translation_subst : forall sigma q, «subst_form sigma q» = subst_form sigma «q».
  Lemma translation_subst_atm sigma p : « subst_form_atomic _ _ sigma p » = subst_form sigma (translate_atomic p).
  Proof. destruct p. cbn. unfold Pred_. rewrite translation_inj. unfold translate_atomic. rewrite subst_dn.
    rewrite subst_form_inj. reflexivity.
  Defined.

  Variable nd : list form -> form -> Prop.
  Notation "A ⊢ p" := (nd A p) (at level 70).
  Variable cnd_retract : forall A p, nd_classic _ _ nd A p -> A ⊢ p.
  Variable translation_bwd : forall A p,  A ⊢ «p» -> A ⊢ p.
  Lemma translation_bwd_atm A p: A ⊢ translate_atomic p -> A ⊢ inj p.
  Proof. destruct p; cbn. intro. apply translation_bwd. now rewrite translation_inj.
  Defined.

  Variable cut : forall A p q,  A ⊢ p -> (p :: A) ⊢ q -> A ⊢ q.
  Variable agree_imp : forall A p, nd_imp _ _ nd A p -> A ⊢ p.
  Variable translation_helper : forall A p, A ⊢ (¬¬«p») -> A ⊢ «p».
  Lemma translation_helper_atm A p : A ⊢ (¬¬(translate_atomic p)) -> A ⊢ translate_atomic p.
  Proof. unfold translate_atomic. intro. apply (cut _ _ _ H).
    apply agree_imp,ndII,agree_imp,(ndIE _ _ _ _ (¬¬¬(inj p))).
    apply agree_imp,ndHyp. right. now left.
    apply agree_imp,ndII,agree_imp,(ndIE _ _ _ _ (¬(inj p))). apply agree_imp,ndHyp. now left.
    apply agree_imp,ndHyp. right. now left.
  Defined.

End atomic.