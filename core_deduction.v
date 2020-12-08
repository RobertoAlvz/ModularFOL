Require Export implicative_deduction universal_deduction.
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
  | ndDN A p : A ⊢c (¬¬p) -> A ⊢c p
where "A ⊢c p" := (ndc A p).

Fixpoint weakening_c A B p (H : A ⊢c p) : incl A B -> B ⊢c p.
Proof. induction H; intro Hinc;
  [ now apply ndcI, (weakening_imp form _ ndc weakening_c A)
  | now apply ndcU, (weakening_univ form _ subst_form ndc weakening_c A)
  | now apply ndDN, IHndc ].
Defined.

Section translation.

Fixpoint translate (p : form) : form := match p with
  | In_form_implicative p => translate_imp form _ translate p
  | In_form_universal p   => translate_univ form _ _ translate p
end.

Notation "« p »" := (translate p).
Notation "«/ A »" := (map translate A).

Fixpoint translation_int A p (H : A ⊢ p) : «/ A » ⊢ «p».
Proof. destruct H; [apply ndI | apply ndU ].
  -now apply (translation_int_imp _ _ _ ndI _ translation_int).
  -now apply (translation_int_univ _ _ _ _ ndU _ translation_int).
Admitted.
(* Defined. *)

Lemma trans_char p : exists q, «p» = (¬¬q).
Proof. destruct p; destruct f; cbn; [ now exists ⊥ | now exists («f»~>«f0») | now exists (∀ «f») ].
Qed.

Fixpoint translation_elim A p : «/A» ⊢c «p» -> A ⊢c p.
Proof. destruct (trans_char p) as [q rw]. rewrite rw. destruct 1 eqn:?; [apply ndcI | apply ndcU | ].
  -apply (translation_elim_imp _ _ _ ndcI _ translation_elim). admit.
  -apply (translation_elim_univ _ _ _ _ ndcU _ translation_elim). admit.
  -admit.
Admitted.
(* Defined. *)

End translation.
