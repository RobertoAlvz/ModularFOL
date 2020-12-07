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

  Variable retract_imp_atom : included form_implicative form_atomic.
  Variable retract_imp_imp  : included form_implicative (form_implicative form).
  Variable retract_imp_univ : included form_implicative (form_universal form).
  Variable retract_imp_conj : included form_implicative (form_conjunctive form).
  Variable retract_imp_disj : included form_implicative (form_disjunctive form).
  Variable retract_imp_exst : included form_implicative (form_existential form).

Fixpoint translate (p : form) : form := match p with
  | In_form_atomic p      => inj (translate_atomic _ p)
  | In_form_implicative p => inj (translate_imp form _ translate p)
  | In_form_universal p   => inj (translate_univ form _ translate p)
  | In_form_conjunctive p => inj (translate_conj form _ translate p)
  | In_form_disjunctive p => inj (translate_disj form _ translate p)
  | In_form_existential p => inj (translate_exst form _ translate p)
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