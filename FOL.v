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
  Variable retract_implicative : included form_implicative form.

  Variable count : form -> nat.
  Definition count_imp (p : form_implicative form) := match p with
    | Fal _  => 1
    | Impl _ p q => count p + count q
  end.


  Variable nd : list form -> form -> Prop.
  Notation "A ⊢ p" := (nd A p) (at level 70).
  Variable ndH : forall A p, In p A -> A ⊢ p.

  Inductive nd_imp (A : list form) : form -> Prop :=
    | ndHI p : A ⊢ p -> A ⊢I p
    | ndExp p : A ⊢ ⊥ -> A ⊢I p
    | ndII p q : (p :: A) ⊢ q -> A ⊢I p ~> q
    | ndIE p q : A ⊢ p ~> q -> A ⊢ p -> A ⊢I q
  where "A ⊢I p" := (nd_imp A p).

  Variable agree : forall A p, A ⊢I p -> A ⊢ p.

  Variable weakening : forall A B p, A ⊢ p -> incl A B -> B ⊢ p.
  Lemma weakening_imp A B p : A ⊢I p -> incl A B -> B ⊢I p.
  Proof. intro. revert B. induction H; intros B Hinc;
    [ apply ndHI | apply ndExp | apply ndII | apply (ndIE _ p _ (weakening _ _ _ H Hinc)) ].
    1,2,4: now apply (weakening A).
    apply (weakening (p::A) (p::B) _ H), incl_cons; [ now left | now apply incl_tl ].
  Qed.

  Variable retract : included form_implicative (form_implicative form).
  Variable translate : form -> form.
  Definition translate_imp (p : form_implicative form) : form_implicative form := match p with
    | Fal _ => ¬¬⊥
    | Impl _ p q => Impl _ (translate p) (translate q)
  end.

  Variable double_neg : forall A p, A ⊢ p -> A ⊢ translate p.
  Lemma double_neg_imp A p : A ⊢I p -> A ⊢I (translate p).
  Proof. induction 1; apply ndHI, double_neg, agree;
    [ now apply ndHI | now apply ndExp | now apply ndII | now apply (ndIE _ p) ].
  Qed.

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
  Variable ndH : forall A p, In p A -> A ⊢ p.

  Definition up_ctx (A : list form) := map (subst_form (S >> var_term)) A.
  Inductive nd_univ (A : list form) : form -> Prop :=
    | ndHU p : A ⊢ p -> A ⊢U p
    | ndUI p : up_ctx A ⊢ p -> A ⊢U ∀ p
    | ndUE p t : A ⊢ ∀ p -> A ⊢U subst_form (t ..) p
  where "A ⊢U p" := (nd_univ A p).

  Variable agree : forall A p, A ⊢U p -> A ⊢ p.

  Variable weakening : forall A B p, A ⊢ p -> incl A B -> B ⊢ p.
  Lemma weakening_univ A B p : A ⊢U p -> incl A B -> B ⊢U p.
  Proof. intro. revert B. induction H; intros B Hinc; [ apply ndHU | apply ndUI | apply ndUE ].
    1,3: now apply (weakening A).
    -apply (weakening (up_ctx A) (up_ctx B)); [ assumption | unfold up_ctx ]. now apply incl_map.
  Qed.


  Variable retract_implicative : included form_implicative form.
  Variable retract_imp_univ : included form_implicative (form_univ form).

  Variable translate : form -> form.
  Definition translate_univ (p : form_univ form) : _ := match p with
    | Pred _ _ _ => ¬¬p
    | All _ q => All _ (translate q)
  end.

  Variable double_neg : forall A p, A ⊢ p -> A ⊢ translate p.

  Lemma double_neg_univ A p : A ⊢U p -> A ⊢U translate p.
  Proof. induction 1; apply ndHU, double_neg, agree;
    [ now apply ndHU | now apply ndUI | now apply ndUE ].
  Qed.

End universals.

Fixpoint count (p : form) := match p with 
  | In_form_implicative p => count_imp _ count p
  | In_form_univ p => count_univ _ count p
end.

Inductive nd : list form -> form -> Prop := 
  | ndI A p : nd_imp form _ nd A p -> A ⊢ p
  | ndU A p : nd_univ form _ subst_form nd A p -> A ⊢ p
where "A ⊢ p" := (nd A p).

(* Fixpoint weakening A B p : A ⊢ p -> incl A B -> B ⊢ p.
Proof. destruct 1; intro Hinc; [ apply ndI | apply ndU ].
    -now apply (weakening_imp form _ nd weakening A B).
    -now apply (weakening_univ form _ subst_form nd weakening A B).
Qed. *)

Section double_neg.
  Variable retract_imp2imp : included form_implicative (form_implicative form).
  Variable retract_imp2univ : included form_implicative (form_univ form).

  Fixpoint translate (p : form) : form := match p with
    | In_form_implicative p => inj (translate_imp form _ translate p)
    | In_form_univ p => inj (translate_univ form _ translate p)
  end.

(*  Fixpoint double_neg A p: A ⊢ p -> A ⊢ translate p.
  Proof. destruct 1.
    -apply ndI. now apply (double_neg_imp _ _ nd ndI translate double_neg).
    -apply ndU. now apply (double_neg_univ _ _ subst_form nd ndU translate double_neg).
  Qed. *)

End double_neg.