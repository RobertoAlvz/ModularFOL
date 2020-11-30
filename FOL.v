Require Export syntax.

Reserved Notation "A ⊢ p" (at level 70).
Reserved Notation "A ⊢I p" (at level 70).
Reserved Notation "A ⊢U p" (at level 70).

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


  Variable nd : list form -> form -> Prop.
  Notation "A ⊢ p" := (nd A p) (at level 70).
  Inductive nd_imp (A : list form) : form -> Prop :=
    | ndHI p : In p A -> A ⊢I p
    | ndExp p : A ⊢ ⊥ -> A ⊢I p
    | ndII p q : (p :: A) ⊢ q -> A ⊢I p ~> q
    | ndIE p q : A ⊢ p ~> q -> A ⊢ p -> A ⊢I q
  where "A ⊢I p" := (nd_imp A p).
  Variable agree : forall A p, nd A p -> A ⊢I p.

  Variable weakening : forall A B p, A ⊢ p -> incl A B -> B ⊢ p.
  Lemma weakening_imp A B p : A ⊢I p -> incl A B -> B ⊢I p.
  Proof. intro. revert B. induction H; intros B Hinc.
    -apply ndHI. now apply Hinc.
    -apply ndExp. now apply (weakening A).
    -apply ndII. apply (weakening (p::A) (p::B)). assumption. { apply incl_cons. now left. now apply incl_tl. }
    -apply (ndIE _ p). now apply (weakening A B (p~>q)). now apply (weakening A).
  Qed.

(*   Lemma double_neg_imp A p : A ⊢ p -> A ⊢ ¬¬p.
  Proof. apply (ndIE _ p), ndII, ndII. apply (ndIE _ p).
    { apply ndHI. now left. }
    { apply ndHI. right. now left. }
  Qed.
 *)
End implicative.

Section universals.

  Variable form : Type.
  Variable retract_univ : retract (form_univ form) form.
  Variable subst_form : (fin -> term) -> form -> form.

  Variable count : form -> nat.
  Definition count_univ (p : form_univ form) : nat := match p with 
    | Pred _ _ _ => 1
    | All _ p => count p
  end.

  Variable nd : list form -> form -> Prop.
  Notation "A ⊢ p" := (nd A p) (at level 70).
  Definition up_ctx (A : list form) := map (subst_form (S >> var_term)) A.
  Inductive nd_univ (A : list form) : form -> Prop :=
    | ndUI p : up_ctx A ⊢ p -> A ⊢U ∀ p
    | ndUE p t : A ⊢ ∀ p -> A ⊢U subst_form (t ..) p
  where "A ⊢U p" := (nd_univ A p).


  Variable weakening : forall A B p, A ⊢ p -> incl A B -> B ⊢ p.
  Lemma weakening_univ A B p : A ⊢U p -> incl A B -> B ⊢U p.
  Proof. intro. revert B. induction H; intros B Hinc.
    -apply ndUI. apply (weakening (up_ctx A) (up_ctx B)). assumption. unfold up_ctx. now apply incl_map.
    -apply ndUE. now apply (weakening A).
  Qed.

 (*  Variable retract_implicative : retract (form_implicative form) form.
  Variable equiv_nd : forall A p, nd_imp _ _ A p <-> nd_univ A p.
  Lemma double_neg_univ A (p : form) : A ⊢ p -> A ⊢ ¬¬( p).
  Proof. intro. apply equiv_nd. apply (double_neg_imp _ _ A (p)). now apply equiv_nd.
  Qed. *)

End universals.

Fixpoint count (p : form) := match p with 
  | In_form_implicative p => count_imp _ count p
  | In_form_univ p => count_univ _ count p
end.

Inductive nd : list form -> form -> Prop := 
  | ndI A p : nd_imp form _ nd A p -> A ⊢ p
  | ndU A p : nd_univ form _ subst_form nd A p -> A ⊢ p
where "A ⊢ p" := (nd A p).

Fixpoint weakening A B p: A ⊢ p -> incl A B -> B ⊢ p.
Proof. destruct 1; intro Hinc.
    -apply ndI. now apply (weakening_imp _ _ nd weakening A B).
    -apply ndU. now apply (weakening_univ _ _ subst_form nd weakening A B).
Qed.

