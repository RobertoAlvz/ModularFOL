Require Export implicativesyntax.
(* Require Import classical_deduction.
 *)
Reserved Notation "A ⊢ p" (at level 70).
Reserved Notation "A ⊢_imp p" (at level 70).


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
    | ndHyp p : In p A -> A ⊢_imp p
    | ndExp p : A ⊢ ⊥  -> A ⊢_imp p
    | ndII p q : (p :: A) ⊢ q -> A ⊢_imp p ~> q
    | ndIE p q : A ⊢ p ~> q -> A ⊢ p -> A ⊢_imp q
  where "A ⊢_imp p" := (nd_imp A p).
  Variable agree : forall A p, nd_imp A p -> A ⊢ p.

  Variable weakening : forall A B p, A ⊢ p -> incl A B -> B ⊢ p.
  Lemma weakening_imp A B p : A ⊢_imp p -> incl A B -> B ⊢ p.
  Proof. intro. revert B. destruct H; intros B Hinc; apply agree;
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

  Variable cut : forall A p q,  A ⊢ p -> (p :: A) ⊢ q -> A ⊢ q.
  Variable translation_bwd : forall A p,  A ⊢ «p» <-> A ⊢ p.
  Lemma translation_bwd_imp A p: A ⊢ translate_imp p <-> A ⊢ inj p.
  Proof. destruct p; cbn; [ reflexivity |]. split; intro H; apply (cut _ _ _ H).
    -apply agree,ndII,translation_bwd, agree,(ndIE _ «f»). apply agree,ndHyp. right. now left.
     apply translation_bwd,agree,ndHyp. now left.
    -apply agree,ndII,translation_bwd. apply agree,(ndIE _ f). apply agree,ndHyp. right. now left.
     apply translation_bwd,agree,ndHyp. now left.
  Defined.

(*   Variable dni : forall A p, A ⊢ p -> A ⊢ (¬¬p). *)

  Variable translation_helper : forall A p, A ⊢ (¬¬«p») -> A ⊢ «p».
  Lemma translation_helper_imp A p : A ⊢ (¬¬(translate_imp p)) -> A ⊢ translate_imp p.
  Proof. destruct p; cbn; intro.
    -apply agree,(ndIE _ (¬⊥)). assumption. apply agree,ndII,agree,ndHyp. now left.
    -apply agree,ndII, translation_helper, agree,ndII,agree ,(ndIE _ (¬¬(«f»~>«f0»))).
      +apply agree,ndII, agree,(ndIE _ (¬(«f»~>«f0»))). apply agree,ndHyp. now left. apply agree,ndII,agree,(ndIE _ «f0»).
       apply agree,ndHyp. right. right. now left. apply agree,(ndIE _ «f»).
       apply agree,ndHyp. now left.
       apply agree,ndHyp. right. right. right. now left.
      +apply (weakening A),incl_tl. assumption. now apply incl_tl.
  Defined.


  Variable subst_form : (fin -> term) -> form -> form.
  Variable subst_form_inj : forall sigma p, subst_form sigma (inj p) = subst_form_implicative _ subst_form _ sigma p.
  Variable translation_subst : forall sigma q, «subst_form sigma q» = subst_form sigma «q».
  Lemma translation_subst_imp sigma p :  « subst_form_implicative _ subst_form _ sigma p » = subst_form sigma (translate_imp p).
  Proof. destruct p; cbn. 
    -rewrite subst_form_inj. unfold Fal_. rewrite translation_inj. reflexivity.
    -rewrite subst_form_inj. unfold Impl_. rewrite translation_inj. cbn. apply congr_Impl_; apply translation_subst.
  Defined.

  Variable subst_comp: forall sigma tau p, subst_form sigma (subst_form tau p) = subst_form (sigma >> subst_term tau) p.
  Lemma subst_comp_imp sigma tau p: subst_form sigma (subst_form tau (inj p)) = subst_form (sigma >> subst_term tau) (inj p).
  Proof. rewrite subst_form_inj. destruct p; cbn; [unfold Fal_ | unfold Impl_]; repeat rewrite subst_form_inj; cbn.
  -reflexivity.
  -apply congr_Impl_; apply subst_comp.
  Defined.

  Variable subst_helper: forall p, subst_form (var_term 0, var_term) (subst_form (up_term_term (S >> var_term)) p) = p.
  Lemma subst_helper_imp p : subst_form (var_term 0, var_term) (subst_form (up_term_term (S >> var_term)) (inj p)) = (inj p).
  Proof. destruct p; cbn; rewrite subst_form_inj; cbn; [unfold Fal_ | unfold Impl_]; rewrite subst_form_inj; cbn;
    [reflexivity | apply congr_Impl_; apply subst_helper ].
  Defined.

End implicative.

Notation "A ⊢_imp p" := (nd_imp A p) (at level 70).

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

  Variable agree_cnd : forall A p, A ⊢[cnd] p -> cnd A p.
  Variable embed : forall A p, nd A p -> cnd A p.
  Lemma embed_imp A p : A ⊢[nd] p -> cnd A p.
  Proof. destruct 1; apply agree_cnd;
    [ now apply ndHyp | now apply ndExp, embed | now apply ndII, embed | ].
    apply (ndIE _ _ _ _ p); now apply embed.
  Defined.

  Variable translation_inj : forall p, «inj p» = translate_imp _ _ translate p.

  Variable agree_nd : forall A p, A ⊢[nd] p -> nd A p.
  Variable translation : forall A p, cnd A p -> nd «/A» «p».
  Lemma translation_imp A p: A ⊢[cnd] p -> nd «/A» «p».
  Proof. destruct 1; apply agree_nd.
    -now apply ndHyp, in_map.
    -apply ndExp. apply translation in H. rewrite translation_inj in H. now cbn in H.
    -rewrite translation_inj. cbn. apply ndII. rewrite <- map_cons. now apply translation.
    -apply (ndIE _ _ _ _ «p»). 2:now apply translation. {pose (translation_inj (Impl _ p q)). cbn in e. rewrite <- e. now apply translation. }
  Defined.


End translation.