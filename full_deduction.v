Require Export implicative_deduction universal_deduction atomic_deduction conjunctive_deduction disjunctive_deduction existential_deduction classical_deduction.

Require Import fullsyntax.

Section deduction_systems.
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
  | In_form_implicative p => inj (translate_imp form translate p)
  | In_form_universal p   => inj (translate_univ form translate p)
  | In_form_conjunctive p => inj (translate_conj form translate p)
  | In_form_disjunctive p => translate_disj form _ _ translate p
  | In_form_existential p => translate_exst form _ _ translate p
end.

Notation "« p »" := (translate p).
Notation "«/ A »" := (map translate A).


(*   Notation "A |- p" := (nd_classic _ _ nd A p) (at level 70).*)

Reserved Notation "A |- p" (at level 70).
Inductive cnd : list form -> form -> Prop :=
  | cndI A p : nd_imp form _ cnd A p -> A |- p
  | cndU A p : nd_univ form _ subst_form cnd A p -> A |- p
  | cndC A p : nd_conj form _ cnd A p -> A |- p
  | cndD A p : nd_disj form _ cnd A p -> A |- p
  | cndE A p : nd_exst form _ subst_form cnd A p -> A |- p
  | cndDN A p : nd_classic form _ cnd A p -> A |- p
where "A |- p" := (cnd A p).


Fixpoint weakening_c A B p (H : A |- p) : incl A B -> B |- p.
Proof. destruct H; intro Hinc; [apply cndI | apply cndU| apply cndC | apply cndD | apply cndE | apply cndDN ].
  -now apply (weakening_imp form _ cnd weakening_c A B).
  -now apply (weakening_univ form _ subst_form cnd weakening_c A B).
  -now apply (weakening_conj form _ cnd weakening_c A B).
  -now apply (weakening_disj form _ cnd weakening_c A B).
  -now apply (weakening_exst form _ subst_form cnd weakening_c A B).
  -now apply (weakening_classic form _ cnd weakening_c A B).
Defined.

Lemma dn_int A p : A ⊢ p -> A ⊢ (¬¬p).
Proof. intro. apply ndI, ndII, ndI, (ndIE _ _ _ _ p).
  -apply ndI,ndHyp. now left.
  -now apply (weakening A), incl_tl.
Defined.

Fixpoint embed A p (H : A ⊢ p) : A |- p.
Proof. destruct H; [ apply cndI | apply cndU | apply cndC | apply cndD | apply cndE ].
  -now apply (embed_imp _ _ nd cnd embed).
  -now apply (embed_univ _ _ _ nd cnd embed).
  -now apply (embed_conj _ _ nd cnd embed).
  -now apply (embed_disj _ _ nd cnd embed).
  -now apply (embed_exst _ _ _ nd cnd embed).
Defined.

Fixpoint translation_subst sigma p : « subst_form sigma p » = subst_form sigma « p ».
Proof. destruct p; destruct f; auto.
Admitted.
(* Defined. *)

Lemma dne A p : A |- (¬¬p) -> A |- p.
Proof. intro. now apply cndDN, ndDN. Defined.

Fixpoint translation A p (H : A |- p) : «/A» ⊢ «p».
Proof. destruct H.
  -now apply ndI, (translation_imp _ _ _ (fun _ => eq_refl) nd cnd).
  -now apply ndU, (translation_univ form _ _ _ (fun _ => eq_refl) translation_subst nd cnd).
  -now apply ndC, (translation_conj _ _ _ (fun _ => eq_refl) nd cnd).
  -now apply ndD, (translation_disj _ _ _ _ (fun _ => eq_refl) nd cnd embed).
  -now apply ndE, (translation_exst _ _ _ _ _ (fun _ => eq_refl) translation_subst nd cnd embed).
  -destruct H. apply (translation_class _ _ translate nd cnd dne translation).
Defined.

End deduction_systems.
