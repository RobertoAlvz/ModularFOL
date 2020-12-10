Require Export implicative_deduction universal_deduction classical_deduction.
Require Import coresyntax.

Reserved Notation "A ⊢c p" (at level 70).

Inductive nd : list form -> form -> Prop := 
  | ndI A p : nd_imp form _ nd A p -> A ⊢ p
  | ndU A p : nd_univ form _ subst_form nd A p -> A ⊢ p
where "A ⊢ p" := (nd A p).

Fixpoint weakening A B p (H : A ⊢ p) : incl A B -> B ⊢ p.
Proof. destruct H; intro Hinc; [apply ndI | apply ndU ].
  -now apply (weakening_imp form _ nd weakening A B).
  -now apply (weakening_univ form _ subst_form nd weakening A B).
Defined.

Inductive ndc : list form -> form -> Prop := 
  | ndcI A p : nd_imp form _ ndc A p -> A ⊢c p
  | ndcU A p : nd_univ form _ subst_form ndc A p -> A ⊢c p
  | ndcc A p : nd_classic form _ ndc A p -> A ⊢c p
where "A ⊢c p" := (ndc A p).

Fixpoint weakening_c A B p (H : A ⊢c p) : incl A B -> B ⊢c p.
Proof. destruct  H; intro Hinc;
  [ now apply ndcI, (weakening_imp form _ ndc weakening_c A)
  | now apply ndcU, (weakening_univ form _ subst_form ndc weakening_c A)
  | now apply ndcc, (weakening_classic form _ ndc weakening_c A) ].
Defined.

Section translation.

Fixpoint translate (p : form) : form := match p with
  | In_form_implicative p => inj (translate_imp form translate p)
  | In_form_universal p   => inj (translate_univ form translate p)
end.
Notation "« p »" := (translate p).
Notation "«/ A »" := (map translate A).

Lemma translation_subst p sigma : « p [sigma] » = « p » [sigma].
Proof. Admitted.

Fixpoint translation_int A p (H : A ⊢ p) : «/ A » ⊢ «p».
Proof. destruct H; [apply ndI | apply ndU ].
  -apply translation_int_imp. { intro. auto. } exact translation_int. assumption.
  -apply translation_int_univ. { intro. auto. } exact translation_subst. exact translation_int. assumption.
Defined.


End translation.
