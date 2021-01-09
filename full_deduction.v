Require Export implicative_deduction universal_deduction atomic_deduction conjunctive_deduction disjunctive_deduction existential_deduction classical_deduction.

Require Import fullsyntax.

Section translation.
Context {Sigma : Signature}.

Inductive nd : list form -> form -> Prop := 
  | ndI A p : nd_imp form _ nd A p -> A ⊢ p
  | ndU A p : nd_univ form _ subst_form nd A p -> A ⊢ p
  | ndC A p : nd_conj form _ nd A p -> A ⊢ p
  | ndD A p : nd_disj form _ nd A p -> A ⊢ p
  | ndE A p : nd_exst form _ subst_form nd A p -> A ⊢ p
where "A ⊢ p" := (nd A p).

Fixpoint weakening A B p (H : A ⊢ p) : incl A B -> B ⊢ p.
Proof. destruct H; intro Hinc.
  -now apply (weakening_imp form _ nd ndI weakening A B).
  -now apply (weakening_univ form _ subst_form nd ndU weakening A B).
  -now apply (weakening_conj form _ nd ndC weakening A B).
  -now apply (weakening_disj form _ nd ndD weakening A B).
  -now apply (weakening_exst form _ subst_form nd ndE weakening A B).
Defined.


Fixpoint translate (p : form) : form := match p with
  | In_form_atomic p      => translate_atomic form _ _ p
  | In_form_implicative p => translate_imp form _ translate p
  | In_form_universal p   => translate_univ form _ translate p
  | In_form_conjunctive p => translate_conj form _ translate p
  | In_form_disjunctive p => translate_disj form _ _ translate p
  | In_form_existential p => translate_exst form _ _ translate p
end.

Notation "« p »" := (translate p).
Notation "«/ A »" := (map translate A).

Reserved Notation "A ⊢c p" (at level 70).
Inductive cnd : list form -> form -> Prop :=
  | cndI A p : nd_imp form _ cnd A p -> A ⊢c p
  | cndU A p : nd_univ form _ subst_form cnd A p -> A ⊢c p
  | cndC A p : nd_conj form _ cnd A p -> A ⊢c p
  | cndD A p : nd_disj form _ cnd A p -> A ⊢c p
  | cndE A p : nd_exst form _ subst_form cnd A p -> A ⊢c p
  | cndDN A p : nd_classic form _ cnd A p -> A ⊢c p
where "A ⊢c p" := (cnd A p).


Fixpoint weakening_c A B p (H : A ⊢c p) : incl A B -> B ⊢c p.
Proof. destruct H; intro Hinc.
  -now apply (weakening_imp form _ cnd cndI weakening_c A B).
  -now apply (weakening_univ form _ subst_form cnd cndU weakening_c A B).
  -now apply (weakening_conj form _ cnd cndC weakening_c A B).
  -now apply (weakening_disj form _ cnd cndD weakening_c A B).
  -now apply (weakening_exst form _ subst_form cnd cndE weakening_c A B).
  -now apply (weakening_classic form _ cnd cndDN weakening_c A B).
Defined.

Fixpoint translation_subst sigma p : « subst_form sigma p » = subst_form sigma « p ».
Proof. destruct p;
  [ eapply translation_subst_atm
  | eapply translation_subst_imp
  | eapply translation_subst_univ
  | eapply translation_subst_conj
  | eapply translation_subst_disj
  | eapply translation_subst_exst
  ]; eauto.
Defined.

Lemma cut A p q : A ⊢ p -> (p :: A) ⊢ q -> A ⊢ q.
Proof.
  intros. apply ndI,(ndIE _ _ _ _ p). now apply ndI,ndII. now apply (weakening A).
Qed.

Lemma cut_c A p q : A ⊢c p -> (p :: A) ⊢c q -> A ⊢c q.
Proof.
  intros. apply cndI,(ndIE _ _ _ _ p). now apply cndI,ndII. now apply (weakening_c A).
Qed.

Lemma subst_helper p: subst_form (var_term 0, var_term) (subst_form (up_term_term (S >> var_term)) p) = p.
Proof. rewrite compComp_form. apply idSubst_form. destruct x; now reflexivity. Defined.

Fixpoint translation_helper A p : A ⊢ (¬¬«p») -> A ⊢ «p».
Proof. destruct p.
  -eapply translation_helper_atm. exact cut. exact ndI.
  -eapply translation_helper_imp. exact ndI. exact weakening. apply translation_helper.
  -eapply (translation_helper_univ _ _ subst_form); eauto.
   exact ndU. exact cut. exact subst_helper. exact ndI.
  -eapply translation_helper_conj. exact ndC. apply cut. exact ndI. exact translation_helper.
  -eapply translation_helper_disj. exact ndI. apply cut.
  -eapply translation_helper_exst. exact ndI. apply cut.
Defined.

Lemma dni A p : A ⊢ p -> A ⊢ (¬¬p).
Proof. intro. apply ndI, ndII, ndI, (ndIE _ _ _ _ p).
  -apply ndI,ndHyp. now left.
  -now apply (weakening A), incl_tl.
Defined.

Lemma dni_c A p : A ⊢c p -> A ⊢c (¬¬p).
Proof. intro. apply cndI, ndII, cndI, (ndIE _ _ _ _ p).
  -apply cndI,ndHyp. now left.
  -now apply (weakening_c A), incl_tl.
Defined.

Fixpoint embed A p (H : A ⊢ p) : A ⊢c p.
Proof. destruct H.
  -now apply (embed_imp _ nd cnd _ cndI embed).
  -now apply (embed_univ _  nd cnd _ _ cndU embed).
  -now apply (embed_conj _ nd cnd _ cndC embed).
  -now apply (embed_disj _ nd cnd _ cndD embed).
  -now apply (embed_exst _ nd cnd _ _ cndE embed).
Defined.

Lemma dne A p : A ⊢c (¬¬p) -> A ⊢c p.
Proof. intro. now apply cndDN, ndDN. Defined.

Fixpoint translation_fwd A p (H : A ⊢c p) : «/A» ⊢ «p».
Proof. destruct H.
  -eapply (translation_imp _ nd cnd _ _ _ ndI); eauto.
  -eapply (translation_univ _ nd cnd _ _ _ _ _ ndU); eauto.
  -eapply (translation_conj _ nd cnd _ _ _ ndC); eauto.
  -eapply (translation_disj _ nd cnd _ retract_form_implicative_form _ _ _ dni ndD ndI); eauto.
   exact translation_helper.
  -eapply (translation_exst _ nd cnd _ retract_form_implicative_form _ _ _ _ _ ndE ndI); eauto.
   exact translation_helper.
  -eapply (translation_cls _ nd cnd); eauto.
   exact translation_helper.
  Unshelve. 3,8: exact translation_subst. 5,7: exact weakening. all: intros; reflexivity.
Defined.

Fixpoint translation_bwd A (p : form) : A ⊢c «p» <-> A ⊢c p.
Proof. destruct p; cbn.
  -split.  now apply dne. now apply dni_c.
  -eapply translation_bwd_imp; eauto. exact cndI. exact cut_c.
  -eapply (translation_bwd_univ _ retract_form_universal_form subst_form ); eauto.
   exact cndU. exact cut_c. exact subst_helper. exact cndI.
  -eapply translation_bwd_conj; eauto. exact cndC.
  -eapply translation_bwd_disj; eauto. exact cndD. exact weakening_c. exact cndDN. exact cndI.
  -eapply (translation_bwd_exst _ retract_form_existential_form subst_form); eauto.
   exact cndE. exact weakening_c. exact cndDN. exact cndI. exact subst_helper.
Defined.

Lemma translation_rm_ctx A B p : (A ++ «/B») ⊢c p -> (A ++ B) ⊢c p.
Proof. revert A. induction B; cbn; [auto |].
  intros. specialize (IHB (A ++ (cons a nil))). do 2 rewrite <- app_assoc in IHB. apply IHB. apply cut_c with («a»).
    -apply translation_bwd. apply cndI,ndHyp,in_or_app. right. now left.
    -apply (weakening_c _ _ _ H). unfold incl. intros. destruct (in_app_or _ _ _ H0). right. apply in_or_app. now left.
     destruct H1. now left. right. apply in_or_app. right. apply in_or_app. now right.
Defined.

Theorem translation A p: A ⊢c p <-> «/A» ⊢ «p».
Proof. split.
  -apply translation_fwd.
  -intro. apply translation_rm_ctx with (A := nil). now apply translation_bwd, embed.
Qed.

End translation.
