Require Export implicative_deduction universal_deduction atomic_deduction conjunctive_deduction disjunctive_deduction existential_deduction.

Section intuitionistic.

Require Import fullsyntax.

Inductive nd : list form -> form -> Prop := 
  | ndI A p : nd_imp form _ nd A p -> A ⊢ p
  | ndU A p : nd_univ form _ subst_form nd A p -> A ⊢ p
  | ndA A p : nd_atomic form nd A p -> A ⊢ p
  | ndC A p : nd_conj form _ nd A p -> A ⊢ p
  | ndD A p : nd_disj form _ nd A p -> A ⊢ p
  | ndE A p : nd_exst form _ subst_form nd A p -> A ⊢ p
where "A ⊢ p" := (nd A p).

Fixpoint weakening A B p (H : A ⊢ p) : incl A B -> B ⊢ p.
Proof. destruct H; intro Hinc; [apply ndI | apply ndU | apply ndA | apply ndC | apply ndD | apply ndE ].
  -now apply (weakening_imp form _ nd weakening A B).
  -now apply (weakening_univ form _ subst_form nd weakening A B).
  -now apply (weakening_atomic form _ weakening A B).
  -now apply (weakening_conj form _ nd weakening A B).
  -now apply (weakening_disj form _ nd weakening A B).
  -now apply (weakening_exst form _ subst_form nd weakening A B).
Defined.

Section translation.

Fixpoint translate (p : form) : form := match p with
  | In_form_atomic p      => translate_atomic form _ _ p
  | In_form_implicative p => translate_imp form _ translate p
  | In_form_universal p   => translate_univ form _ _ translate p
  | In_form_conjunctive p => translate_conj form _ _ translate p
  | In_form_disjunctive p => translate_disj form _ _ translate p
  | In_form_existential p => translate_exst form _ _ translate p
end.

Fixpoint translation_int A p (H : A ⊢ p) : (map translate A) ⊢ (translate p).
Proof. destruct H; [apply ndI | apply ndU | apply ndA | apply ndC | apply ndD | apply ndE ].
  -now apply (translation_int_imp _ _ _ ndI _ translation_int).
  -now apply (translation_int_univ _ _ _ _ ndU _ translation_int).
  -now apply (translation_int_atom _ _ ndA _ translation_int).
  -now apply (translation_int_conj _ _ _ ndC _ translation_int).
  -now apply (translation_int_disj _ _ _ ndD _ translation_int).
  -now apply (translation_int_exst _ _ _ _ ndE _ translation_int).
Defined.

End translation.

End intuitionistic.