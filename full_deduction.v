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
Proof. destruct H; intro Hinc; [apply ndI | apply ndU| apply ndC | apply ndD | apply ndE ].
  -now apply (weakening_imp form _ nd weakening A B).
  -now apply (weakening_univ form _ subst_form nd weakening A B).
  -now apply (weakening_conj form _ nd weakening A B).
  -now apply (weakening_disj form _ nd weakening A B).
  -now apply (weakening_exst form _ subst_form nd weakening A B).
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
Proof. destruct H; intro Hinc; [apply cndI | apply cndU| apply cndC | apply cndD | apply cndE | apply cndDN ].
  -now apply (weakening_imp form _ cnd weakening_c A B).
  -now apply (weakening_univ form _ subst_form cnd weakening_c A B).
  -now apply (weakening_conj form _ cnd weakening_c A B).
  -now apply (weakening_disj form _ cnd weakening_c A B).
  -now apply (weakening_exst form _ subst_form cnd weakening_c A B).
  -now apply (weakening_classic form _ cnd weakening_c A B).
Defined.

Fixpoint translation_subst sigma p : « subst_form sigma p » = subst_form sigma « p ».
Proof. destruct p.
  -apply translation_subst_atm. { intro. reflexivity. } { intros. reflexivity. } {intros. reflexivity. }
  -apply translation_subst_imp. { intro. reflexivity. } { intros. reflexivity. } apply translation_subst.
  -apply translation_subst_univ. { intro. reflexivity. } { intros. reflexivity. } apply translation_subst.
  -apply translation_subst_conj. { intro. reflexivity. } { intros. reflexivity. } apply translation_subst.
  -apply translation_subst_disj. { intro. reflexivity. } { intros. reflexivity. } {intros. reflexivity. } apply translation_subst.
  -apply translation_subst_exst. { intro. reflexivity. } { intros. reflexivity. } {intros. reflexivity. } apply translation_subst.
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
Proof. Admitted.

Fixpoint translation_helper A p : A ⊢ (¬¬«p») -> A ⊢ «p».
Proof. destruct p.
  -eapply translation_helper_atm. apply cut. apply ndI.
  -eapply translation_helper_imp. apply weakening. apply ndI. apply translation_helper.
  -eapply (translation_helper_univ _ _ subst_form). { intros. reflexivity. }
   apply ndU. apply cut. apply subst_helper. {intros. reflexivity. } apply ndI. fold translate. intros. now apply translation_helper.
  -eapply translation_helper_conj. apply ndC. apply cut. apply ndI. apply translation_helper.
  -eapply translation_helper_disj. apply ndI. apply cut.
  -eapply translation_helper_exst. apply ndI. apply cut.
Defined.

Lemma translation_dn p : «¬¬p» = ¬¬«p».
Proof. now reflexivity. Defined.

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
Proof. destruct H; [ apply cndI | apply cndU | apply cndC | apply cndD | apply cndE ].
  -now apply (embed_imp _ nd cnd _ embed).
  -now apply (embed_univ _  nd cnd _ _ embed).
  -now apply (embed_conj _ nd cnd _ embed).
  -now apply (embed_disj _ nd cnd _ embed).
  -now apply (embed_exst _ nd cnd _ _ embed).
Defined.

Lemma dne A p : A ⊢c (¬¬p) -> A ⊢c p.
Proof. intro. now apply cndDN, ndDN. Defined.

Fixpoint translation_fwd A p (H : A ⊢c p) : «/A» ⊢ «p».
Proof. destruct H; [apply ndI | apply ndU | apply ndC | apply ndD | apply ndE | ].
  -apply (translation_imp _ nd cnd). { intros. reflexivity. } apply translation_fwd. assumption.
  -apply (translation_univ _ nd cnd). { intros. reflexivity. } apply translation_subst. apply translation_fwd. assumption.
  -apply (translation_conj _ nd cnd). { intros. reflexivity. } apply translation_fwd. assumption.
  -apply (translation_disj _ nd cnd _ retract_form_implicative_form). { intros. reflexivity. } apply embed.
    apply weakening. apply dni. apply cndD. apply ndD. apply cndDN. apply ndI. apply translation_fwd. assumption.
  -apply (translation_exst _ nd cnd _ retract_form_implicative_form). { intros. reflexivity. }
   apply translation_subst. apply embed. apply weakening. apply dni. apply cndE. apply ndE. apply cndDN.
   apply ndI. apply subst_helper. apply translation_fwd. assumption.
  -destruct H. apply translation_helper. rewrite <- translation_dn. now apply translation_fwd.
Admitted.


Fixpoint translation_bwd A (p : form) : A ⊢c «p» <-> A ⊢c p.
Proof. destruct p; cbn.
  -split.  now apply dne. now apply dni_c.
  -eapply translation_bwd_imp. apply cndI. apply cut_c. apply translation_bwd.
  -eapply (translation_bwd_univ _ retract_form_universal_form subst_form ). {intros. reflexivity. }
   apply cndU. apply cut_c. apply subst_helper. apply cndI. apply translation_bwd.
  -eapply (translation_bwd_conj). apply cndC. apply translation_bwd.
  -eapply (translation_bwd_disj). apply weakening_c. apply cndD. apply cndDN. apply cndI. apply translation_bwd.
  -eapply (translation_bwd_exst _ retract_form_existential_form subst_form).
    apply weakening_c. apply cndE. apply cndDN. apply cndI. {intros. reflexivity. } apply subst_helper. apply translation_bwd.
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
