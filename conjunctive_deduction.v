Require Export unscoped header_extensible.

Require Export implicativesyntax conjunctivesyntax.
Require Import classical_deduction.

Reserved Notation "A ⊢ p" (at level 70).
Reserved Notation "A ⊢_conj p" (at level 70).

Notation "p ∧ q" := (inj (Conj _ p q)) (at level 60).

Section Conjunctive.
  Context {Sigma : Signature}.

  Variable form : Type.
  Variable retract_conj : retract (form_conjunctive form) form.

  Variable nd : list form -> form -> Prop.
  Notation "A ⊢ p" := (nd A p) (at level 70).

  Inductive nd_conj (A : list form) : form -> Prop :=
    | ndCI p q : A ⊢ p -> A ⊢ q -> A ⊢_conj (p ∧ q)
    | ndCE1 p q : A ⊢ p ∧ q -> A ⊢_conj p
    | ndCE2 p q : A ⊢ p ∧ q -> A ⊢_conj q
  where "A ⊢_conj p" := (nd_conj A p).
  Variable agree : forall A p, A ⊢_conj p -> A ⊢ p.

  Variable weakening : forall A B p, A ⊢ p -> incl A B -> B ⊢ p.
  Lemma weakening_conj A B p : A ⊢_conj p -> incl A B -> B ⊢ p.
  Proof. destruct 1; intro Hinc; apply agree.
    -apply ndCI. all: now apply (weakening A).
    -now apply (ndCE1 _ _ q), (weakening A).
    -now apply (ndCE2 _ p q), (weakening A).
  Defined.

  Variable translate : form -> form.
  Definition translate_conj (p : form_conjunctive form) : _ := match p with
    | Conj _ p q => (translate p) ∧ (translate q)
  end.
  Notation "« p »" := (translate p).
  Notation "«/ A »" := (map translate A).

  Variable translation_inj : forall p, translate (inj p) = translate_conj  p.
  Variable translation_bwd : forall A p, A ⊢ translate p <-> A ⊢ p.
  Lemma translation_bwd_conj A p: A ⊢ (translate_conj p) <-> A ⊢ inj p.
  Proof. destruct p; cbn. split; intro.
    -assert (H1 : A ⊢ «f»). {now apply agree,(ndCE1 _ _ «f0»). }
     assert (H2 : A ⊢ «f0»). {now apply agree,(ndCE2 _ «f»). }
      apply agree, ndCI; now apply translation_bwd.
    -assert (H1 : A ⊢ f). {now apply agree,(ndCE1 _ _ f0). }
     assert (H2 : A ⊢ f0). {now apply agree,(ndCE2 _ f). }
      apply agree, ndCI; now apply translation_bwd. 
  Defined.

  Variable subst_form : (fin -> term) -> form -> form.
  Variable subst_form_inj : forall sigma p, subst_form sigma (inj p) = subst_form_conjunctive _ subst_form _ sigma p.
  Variable translation_subst : forall sigma q, «subst_form sigma q» = subst_form sigma «q».
  Lemma translation_subst_conj sigma p :  « subst_form_conjunctive _ subst_form _ sigma p » = subst_form sigma (translate_conj p).
  Proof. destruct p; cbn. unfold Conj_. rewrite translation_inj. rewrite subst_form_inj. cbn. apply congr_Conj_; apply translation_subst.
  Defined.

  Variable cut : forall A p q,  A ⊢ p -> (p :: A) ⊢ q -> A ⊢ q.
  Variable retract_imp : retract (form_implicative form) form.
  Variable agree_imp : forall A p, nd_imp _ _ nd A p -> A ⊢ p.
  Variable translation_helper : forall A p, A ⊢ (¬¬«p») -> A ⊢ «p».
  Lemma translation_helper_conj A p : A ⊢ (¬¬(translate_conj p)) -> A ⊢ translate_conj p.
  Proof. destruct p. cbn. intro. apply (cut _ _ _ H), agree, ndCI; apply translation_helper, agree_imp,ndII.
    -apply agree_imp,(ndIE _ _ _ _ (¬(«f»∧«f0»))),agree_imp,ndII,agree_imp,(ndIE _ _ _ _ «f»).
     { apply agree_imp,ndHyp. right. now left. } { apply agree_imp,ndHyp. right. now left. }
     apply agree,(ndCE1 _ _ «f0»),agree_imp,ndHyp. now left.
    -apply agree_imp,(ndIE _ _ _ _ (¬(«f»∧«f0»))),agree_imp,ndII,agree_imp,(ndIE _ _ _ _ «f0»).
     { apply agree_imp,ndHyp. right. now left. } { apply agree_imp,ndHyp. right. now left. }
     apply agree,(ndCE2 _ «f»),agree_imp,ndHyp. now left.
  Defined.


End Conjunctive.

Section translation.
  Notation "A ⊢[ nd ] p" := (@nd_conj _ _ nd A p) (at level 70).
  Context {Sigma : Signature}.

  Variable form : Type.
  Variable nd : list form -> form -> Prop.
  Variable cnd : list form -> form -> Prop.
  Variable retract : retract (form_conjunctive form) form.
  Variable retract_implicative : included form_implicative form.

  Variable translate : form -> form.
  Notation "« p »" := (translate p).
  Notation "«/ A »" := (map translate A).

  Variable translation_inj : forall p, «inj p» = translate_conj _ _ translate p.

  Variable agree_cnd : forall A p, A ⊢[cnd] p -> cnd A p.
  Variable embed : forall A p, nd A p -> cnd A p.
  Lemma embed_conj A p : A ⊢[nd] p -> cnd A p.
  Proof. destruct 1; apply agree_cnd.
    -apply ndCI; now apply embed.
    -now apply (ndCE1 _ _ _ _  _ q), embed.
    -now apply (ndCE2 _ _ _ _ p), embed.
  Defined.

  Variable agree_nd : forall A p, A ⊢[nd] p -> nd A p.
  Variable translation : forall A p, cnd A p -> nd «/A» «p».
  Lemma translation_conj A p: A ⊢[cnd] p -> nd «/A» «p».
  Proof. destruct 1; apply agree_nd.
    -rewrite translation_inj. cbn. apply ndCI; now apply translation.
    -apply (ndCE1 _ _ _ _ _ «q»). { pose (translation_inj (Conj _ p q)). cbn in e. rewrite <- e. now apply translation. }
    -apply (ndCE2 _ _ _ _ «p»). { pose (translation_inj (Conj _ p q)). cbn in e. rewrite <- e. now apply translation. }
  Defined.

End translation.