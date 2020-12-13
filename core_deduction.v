Require Export implicative_deduction universal_deduction classical_deduction.
Require Import coresyntax.

Section translation.
Context {Sigma : Signature}.

Inductive nd : list form -> form -> Prop := 
  | ndI A p : nd_imp form _ nd A p -> A ⊢ p
  | ndU A p : nd_univ form _ subst_form nd A p -> A ⊢ p
where "A ⊢ p" := (nd A p).

Fixpoint weakening A B p (H : A ⊢ p) : incl A B -> B ⊢ p.
Proof. destruct H; intro Hinc; [apply ndI | apply ndU ].
  -now apply (weakening_imp form _ nd weakening A B).
  -now apply (weakening_univ form _ subst_form nd weakening A B).
Defined.

Reserved Notation "A |- p" (at level 70).
Inductive cnd : list form -> form -> Prop := 
  | cndI A p : nd_imp form _ cnd A p -> A |- p
  | cndU A p : nd_univ form _ subst_form cnd A p -> A |- p
  | cndDN A p : nd_classic form _ cnd A p -> A |- p
where "A |- p" := (cnd A p).

Lemma dne A p : A |- (¬¬p) -> A |- p.
Proof. intro. now apply cndDN, ndDN. Defined.

Fixpoint weakening_c A B p (H : A |- p) : incl A B -> B |- p.
Proof. destruct  H; intro Hinc;
  [ now apply cndI, (weakening_imp form _ cnd weakening_c A)
  | now apply cndU, (weakening_univ form _ subst_form cnd weakening_c A)
  | now apply cndDN, (weakening_classic form _ cnd weakening_c A) ].
Defined.

Fixpoint translate (p : form) : form := match p with
  | In_form_implicative p => translate_imp form _ translate p
  | In_form_universal p   => translate_univ form _ translate p
end.
Notation "« p »" := (translate p).
Notation "«/ A »" := (map translate A).

Fixpoint translation_subst sigma p : « subst_form sigma p » = subst_form sigma « p ».
Proof. destruct p.
  -apply translation_subst_imp. { intro. reflexivity. } { intros. reflexivity. } apply translation_subst.
  -apply translation_subst_univ. { intro. reflexivity. } { intros. reflexivity. } apply translation_subst.
Defined.

Fixpoint translation A p (H : A |- p) : «/A» ⊢ «p».
Proof. destruct H; [apply ndI | apply ndU | ].
  -apply (translation_imp _  nd cnd). {intro. reflexivity. } apply translation. assumption.
  -apply (translation_univ _ nd cnd). {intro. reflexivity. } apply translation_subst. apply translation. assumption.
  -apply (translation_class _ nd cnd retract_form_implicative_form). apply dne. apply translation. assumption.
(* Defined.
 *)Admitted.

Fixpoint translation_bwd A (p : form) : «/A» |- «p» -> A |- p.
Proof. destruct p; cbn; intro.
  -apply (translation_bwd_imp _ retract_form_implicative_form _ translate). {intro. reflexivity. } apply translation_bwd. assumption.
  -apply (translation_bwd_univ _ retract_form_universal_form _ translate). {intro. reflexivity. } apply translation_bwd. assumption.
(* Defined.
 *)Admitted.

End translation.
