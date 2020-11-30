Require Export syntax.


Notation "p ~> q" := (Impl_ _ _ p q) (at level 60).
Notation "⊥" := (Fal_ _ _).
Notation "¬ p" := (p ~> ⊥) (at level 60).
Notation "∀ p ":= (All_ _ _ p) (at level 60).

Section implicative.

  Variable form : Type.
  Variable retract_implicative : retract (form_implicative form) form.

  Variable count : form -> nat.
  Definition count_imp (p : form_implicative form) := match p with
    | Fal _  => 1
    | Impl _ p q => count p + count q
  end.

  Reserved Notation "A |- p" (at level 70).
  Inductive nd_imp (A : list form) : form -> Prop :=
    | ndHI p : In p A -> A |- p
    | ndExp p : A |- ⊥ -> A |- p
    | ndII p q : (p :: A) |- q -> A |- p ~> q
    | ndIE p q : A |- p ~> q -> A |- p -> A |- q
  where "A |- p" := (nd_imp A p).

  Lemma weakening_imp A B p : A |- p -> incl A B -> B |- p.
  Proof. intro. revert B. induction H; intros B Hinc.
    -apply ndHI. now apply Hinc.
    -apply ndExp. now apply IHnd_imp.
    -apply ndII, (IHnd_imp (p::B)). { apply incl_cons. now left. now apply incl_tl. }
    -apply (ndIE _ p). now apply IHnd_imp1. now apply IHnd_imp2.
  Qed.

  Lemma double_neg_imp A p : A |- p -> A |- ¬¬p.
  Proof. induction 1; apply ndII.
    -apply (ndIE _ p). { apply ndHI. now left. } { apply ndHI. now right. }
    -apply (weakening_imp A). assumption. now apply incl_tl.
    -apply (ndIE _ (p~>q)). { apply ndHI. now left. }
     apply ndII, (weakening_imp (p::A)). assumption.
     { apply incl_cons. now left. now repeat apply incl_tl. }
    -apply (ndIE _ q). { apply ndHI. now left. }
     apply (weakening_imp A). now apply (ndIE _ p). now apply incl_tl.
  Qed.

End implicative.

Section universals.

  Variable form : Type.
  Variable retract_univ : retract (form_univ form) form.
  Variable subst_form : (fin -> term) -> form -> form.
  Variable retract_implicative : retract (form_implicative form) form.

  Variable count : form -> nat.
  Definition count_univ (p : form_univ form) : nat := match p with 
    | Pred _ _ _ => 1
    | All _ p => count p
  end.

  Variable nd : list form -> form -> Prop.

  Definition up_ctx (A : list form) := map (subst_form (S >> var_term)) A.
  Reserved Notation "A |- p" (at level 70).
  Inductive nd_univ (A : list form) : form -> Prop :=
    | ndHU p : In p A -> A |- p
    | ndUI p : up_ctx A |- p -> A |- ∀ p
    | ndUE p t : A |- ∀ p -> A |- subst_form (t ..) p
  where "A |- p" := (nd_univ A p).

  Lemma weakening_univ A B p : A |- p -> incl A B -> B |- p.
  Proof. intro. revert B. induction H; intros B Hinc.
    -apply ndHU. now apply Hinc.
    -apply ndUI, (IHnd_univ (up_ctx B)). unfold up_ctx. now apply incl_map.
    -apply ndUE. now apply IHnd_univ.
  Qed.

  Variable equiv_nd : forall A p, nd_imp _ _ A p <-> nd_univ A p.
  Lemma double_neg_univ A p : A |- p -> A |- ¬¬p.
  Proof. induction 1; apply equiv_nd, ndII.
    -apply (ndIE _ _ _ p). { apply ndHI. now left. } { apply ndHI. now right. }
    -apply (ndIE _ _ _ (∀ p)). { apply ndHI. now left. }
      { apply equiv_nd, ndUI, (weakening_univ (up_ctx A)). assumption.
        unfold up_ctx. now apply incl_map, incl_tl. }
    -apply (ndIE _ _ _ (subst_form (t ..) p)). { apply ndHI. now left. }
      { apply equiv_nd, ndUE, (weakening_univ A). assumption. now apply incl_tl. }
  Qed.

End universals.

Fixpoint count (p : form) := match p with 
  | In_form_implicative p => count_imp _ count p
  | In_form_univ p => count_univ _ count p
end.

Definition nd (A : list form) (p : form) : Prop := match p with
  | In_form_implicative p => nd_imp _ _ A (In_form_implicative p)
  | In_form_univ p => nd_univ _ subst_form _ A (In_form_univ p)
end.
Notation "A |- p" := (nd A p) (at level 70).

Lemma weakening A B p : A |- p -> incl A B -> B |- p.
Proof. destruct p.
  -apply weakening_imp.
  -apply weakening_univ.
Qed.

Lemma double_neg A p : A |- p -> A |- ¬¬p.
Proof. destruct p.
  -apply double_neg_imp.
  -Check double_neg_univ.
Admitted.
