Require Export implicative_deduction universal_deduction classical_deduction.
Require Import coresyntax.


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
  | In_form_implicative p => inj (translate_imp form translate p)
  | In_form_universal p   => inj (translate_univ form translate p)
end.
Notation "« p »" := (translate p).
Notation "«/ A »" := (map translate A).

Fixpoint translation_subst sigma p : « p [sigma] » = « p » [sigma].
Proof. destruct p; destruct f; auto.
Admitted.

Fixpoint translation A p (H : A |- p) : «/A» ⊢ «p».
Proof. destruct H.
  -now apply ndI, (translation_imp _ _ _ (fun _ => eq_refl) nd cnd).
  -now apply ndU, (translation_univ form _ _ _ (fun _ => eq_refl) (translation_subst) nd cnd).
  -now apply (translation_class _ _ translate nd cnd dne translation).
Admitted.
(* Defined. *)
