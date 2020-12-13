Require Export implicativesyntax.
Require Import classical_deduction.

Reserved Notation "A ⊢ p" (at level 70).
Reserved Notation "A ⊢I p" (at level 70).


Section implicative.
  Context {Sigma : Signature}.

  Variable form : Type.
  Variable retract_implicative : included form_implicative form.

  Variable count : form -> nat.
  Definition count_imp (p : form_implicative form) := match p with
    | Fal _  => 1
    | Impl _ p q => count p + count q
  end.

  Variable nd : list form -> form -> Prop.
  Notation "A ⊢ p" := (nd A p) (at level 70).

  Inductive nd_imp (A : list form) : form -> Prop :=
    | ndHyp p : In p A -> A ⊢I p
    | ndExp p : A ⊢ ⊥  -> A ⊢I p
    | ndII p q : (p :: A) ⊢ q -> A ⊢I p ~> q
    | ndIE p q : A ⊢ p ~> q -> A ⊢ p -> A ⊢I q
  where "A ⊢I p" := (nd_imp A p).

  Variable weakening : forall A B p, A ⊢ p -> incl A B -> B ⊢ p.
  Lemma weakening_imp A B p : A ⊢I p -> incl A B -> B ⊢I p.
  Proof. intro. revert B. destruct H; intros B Hinc;
    [ now apply ndHyp, (Hinc p)
    | now apply ndExp, (weakening A) 
    | apply ndII 
    | now apply (ndIE _ p _ (weakening _ _ _ H Hinc)), (weakening A) ].
    - apply (weakening (p::A) (p::B) _ H), incl_cons; [ now left | now apply incl_tl ].
  Defined.


  Variable translate : form -> form.
  Notation "« p »" := (translate p).
  Notation "«/ A »" := (map translate A).
  Definition translate_imp (p : form_implicative form) : _ := match p with
    | Fal _ => ⊥
    | Impl _ p q => «p» ~> «q»
  end.

  Variable translation_inj : forall p, «inj p» = translate_imp  p.

  Variable translation_bwd : forall A p,  «/A» ⊢ «p» -> A ⊢ p.
  Lemma translation_bwd_imp A p: «/A» ⊢ translate_imp p -> A ⊢ inj p.
  Proof. destruct p; cbn; intro; apply translation_bwd; rewrite translation_inj; auto.
  Defined.

  Variable subst_form : (fin -> term) -> form -> form.
  Variable subst_form_inj : forall sigma p, subst_form sigma (inj p) = subst_form_implicative _ subst_form _ sigma p.
  Variable translation_subst : forall sigma q, «subst_form sigma q» = subst_form sigma «q».
  Lemma translation_subst_imp sigma p :  « subst_form_implicative _ subst_form _ sigma p » = subst_form sigma (translate_imp p).
  Proof. destruct p; cbn. 
    -rewrite subst_form_inj. unfold Fal_. rewrite translation_inj. reflexivity.
    -rewrite subst_form_inj. unfold Impl_. rewrite translation_inj. cbn. apply congr_Impl_; apply translation_subst.
  Defined.

End implicative.

Notation "A ⊢I p" := (nd_imp A p) (at level 70).

Section translation.
  Context {Sigma : Signature}.

  Notation "A ⊢[ nd ] p" := (@nd_imp _ _ nd A p) (at level 70).
  Variable form : Type.
  Variable nd : list form -> form -> Prop.
  Variable cnd : list form -> form -> Prop.

  Variable retract_implicative : included form_implicative form.

  Variable translate : form -> form.
  Notation "« p »" := (translate p).
  Notation "«/ A »" := (map translate A).


  Variable embed : forall A p, nd A p -> cnd A p.
  Lemma embed_imp A p : A ⊢[nd] p -> A ⊢[cnd] p.
  Proof. destruct 1; [ now apply ndHyp | now apply ndExp, embed | now apply ndII, embed | ]. apply (ndIE _ _ _ _ p); now apply embed.
  Defined.

  Variable translation_inj : forall p, «inj p» = translate_imp _ _ translate p.

  Variable translation : forall A p, cnd A p -> nd «/A» «p».
  Lemma translation_imp A p: A ⊢[cnd] p -> «/A» ⊢[nd] «p».
  Proof. destruct 1.
    -now apply ndHyp, in_map.
    -apply ndExp. apply translation in H. rewrite translation_inj in H. now cbn in H.
    -rewrite translation_inj. cbn. apply ndII. rewrite <- map_cons. now apply translation.
    -apply (ndIE _ _ _ _ «p»). 2:now apply translation. {pose (translation_inj (Impl _ p q)). cbn in e. rewrite <- e. now apply translation. }
  Defined.


End translation.