Require Export unscoped header_extensible.

Require Export implicativesyntax universalsyntax termsyntax.

Reserved Notation "A ⊢ p" (at level 70).
Reserved Notation "A ⊢U p" (at level 70).

Section universals.

  Variable form : Type.
  Variable retract_univ : retract (form_universal form) form.
  Variable subst_form : (fin -> term) -> form -> form.

  Variable count : form -> nat.
  Definition count_univ (p : form_universal form) : nat := match p with 
    | All _ p => count p
  end.

  Variable nd : list form -> form -> Prop.
  Notation "A ⊢ p" := (nd A p) (at level 70).

  Definition up_ctx (A : list form) := map (subst_form (S >> var_term)) A.
  Inductive nd_univ (A : list form) : form -> Prop :=
    | ndUI p : up_ctx A ⊢ p -> A ⊢U ∀ p
    | ndUE p t : A ⊢ ∀ p -> A ⊢U subst_form (scons t (var_term)) p
  where "A ⊢U p" := (nd_univ A p).

  Variable weakening : forall A B p, A ⊢ p -> incl A B -> B ⊢ p.
  Lemma weakening_univ A B p : A ⊢U p -> incl A B -> B ⊢U p.
  Proof. intro. revert B. destruct H; intros B Hinc; [ apply ndUI | now apply ndUE, (weakening A) ].
    -apply (weakening (up_ctx A) (up_ctx B)); [ assumption | unfold up_ctx ]. now apply incl_map.
  Defined.

  Variable translate : form -> form.
  Definition translate_univ (p : form_universal form) : _ := match p with
    | All _ q => All _ (translate q)
  end.


End universals.

Notation "A ⊢U p" := (nd_univ A p) (at level 70).

Section translation.
Require Import classical_deduction.

  Variable form : Type.
  Variable subst_form : (fin -> term) -> form -> form.
  Variable retract_univ : retract (form_universal form) form.
  Variable translate : form -> form.

  Notation "A ⊢[ nd ] p" := (@nd_univ form _ subst_form nd A p) (at level 70).
  Notation "« p »" := (translate p).
  Notation "«/ A »" := (map translate A).

  Variable translation_inj : forall p, «inj p» = inj (translate_univ _ translate p).
  Variable translation_subst : forall sigma q, «subst_form sigma q» = subst_form sigma «q».

  Lemma translation_subst_univ sigma q: «subst_form sigma (inj q)» = subst_form sigma «inj q».
  Proof. destruct q. rewrite translation_subst. rewrite translation_inj. auto.
  Defined.

  Lemma translation_map A: up_ctx form subst_form (map translate A) = map translate (up_ctx form subst_form A).
  Proof. unfold up_ctx. repeat rewrite map_map. apply map_ext. intro p. symmetry. apply translation_subst.
  Qed.

  Variable nd : list form -> form -> Prop.
  Variable cnd : list form -> form -> Prop.

  Variable embed : forall A p, nd A p -> cnd A p.
  Lemma embed_univ A p : A ⊢[nd] p -> A ⊢[cnd] p.
  Proof. destruct 1; [ now apply ndUI, embed | now apply ndUE, embed ].
  Defined.

  Variable translation : forall A p, cnd A p -> nd «/A» «p».
  Lemma translation_univ A p: A ⊢[cnd] p -> «/A» ⊢[nd] «p».
  Proof. destruct 1.
    +rewrite translation_inj. cbn. apply ndUI. rewrite translation_map. now apply translation.
    +rewrite translation_subst. apply ndUE. { pose (translation_inj (All _ p)). cbn in e. rewrite <- e. now apply translation. }
  Defined.
End translation.