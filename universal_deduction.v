Require Export unscoped header_extensible.

Require Export implicativesyntax univsyntax termsyntax.

Notation "p ~> q" := (Impl_ _ _ p q) (at level 60).
Notation "⊥" := (Fal_ _ _).
Notation "¬ p" := (p ~> ⊥) (at level 60).
Reserved Notation "A ⊢ p" (at level 70).
Reserved Notation "A ⊢U p" (at level 70).
Notation "∀ p ":= (All_ _ _ p) (at level 60).

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
    | ndUE p t : A ⊢ ∀ p -> A ⊢U subst_form (scons t (var_term)) p
  where "A ⊢U p" := (nd_univ A p).

  Variable agree : forall A p, A ⊢U p -> A ⊢ p.

  Variable weakening : forall A B p, A ⊢ p -> incl A B -> B ⊢ p.
  Lemma weakening_univ A B p : A ⊢U p -> incl A B -> B ⊢U p.
  Proof. intro. revert B. destruct H; intros B Hinc; [ apply ndHU | apply ndUI | apply ndUE ].
    1,3: now apply (weakening A).
    -apply (weakening (up_ctx A) (up_ctx B)); [ assumption | unfold up_ctx ]. now apply incl_map.
  Defined.


  Variable retract_implicative : included form_implicative form.
  Variable retract_imp_univ : included form_implicative (form_univ form).

  Variable translate : form -> form.
  Definition translate_univ (p : form_univ form) : _ := match p with
    | Pred _ _ _ => p
    | All _ q => All _ (¬¬(translate q))
  end.

  Variable translation_int : forall A p, A ⊢ p -> (map translate A) ⊢ (translate p).
  Lemma translation_int_univ A p : A ⊢U p -> (map translate A) ⊢U (translate p).
  Proof. intro H. apply agree in H. apply translation_int in H. now apply ndHU.
  Defined.

  Variable translation_elim : forall A p, (map translate A) ⊢ (translate p) -> A ⊢ p.
  Lemma double_neg_elim_imp A p : (map translate A) ⊢U (translate p) -> A ⊢U p.
  Proof. intro. now apply ndHU, translation_elim, agree.
  Defined.

End universals.