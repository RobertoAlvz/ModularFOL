Require Export unscoped header_extensible.

Require Export existentialsyntax implicativesyntax.

Reserved Notation "A ⊢ p" (at level 70).
Reserved Notation "A ⊢E p" (at level 70).

Notation "∃ p" := (Exist_ _ _ p) (at level 60).

Section Existential.
  Variable form : Type.
  Variable retract : retract (form_existential form) form.
  Variable subst_form : (fin -> term) -> form -> form.

  Variable nd : list form -> form -> Prop.
  Notation "A ⊢ p" := (nd A p) (at level 70).

  Inductive nd_exst (A : list form) : form -> Prop :=
    | ndAgree p : A ⊢ p -> A ⊢E p
    | ndEI p t : A ⊢ subst_form (scons t (var_term)) p -> A ⊢E (∃ p)
    | ndEE p q : A ⊢ (∃ p) -> p :: A ⊢ q -> A ⊢E q
  where "A ⊢E p" := (nd_exst A p).
  Variable agree : forall A p, A ⊢E p -> A ⊢ p.

  Variable weakening : forall A B p, A ⊢ p -> incl A B -> B ⊢ p.
  Lemma weakening_exst A B p : A ⊢E p -> incl A B -> B ⊢E p.
  Proof. destruct 1; intro Hinc; [ now apply ndAgree, (weakening A) | now apply (ndEI _ p t), (weakening A) | apply (ndEE _ p q) ].
    -now apply (weakening A).
    -apply (weakening (p::A)), incl_cons; [assumption | now left | now apply incl_tl ].
  Defined.

  Variable retract_implicative : included form_implicative form.
  Variable retract_imp_exst : included form_implicative (form_existential form).

  Variable translate : form -> form.
  Definition translate_exst (p : form_existential form) : _ := match p with
    | Exist _ q => ¬¬(∃ (translate q))
  end.

  Variable translation_int : forall A p, A ⊢ p -> (map translate A) ⊢ (translate p).
  Lemma translation_int_exst A p : A ⊢E p -> (map translate A) ⊢E (translate p).
  Proof. intro. apply agree in H. apply translation_int in H. now apply ndAgree.
  Defined.

  Variable translation_elim : forall A p, (map translate A) ⊢ (translate p) -> A ⊢ p.
  Lemma translation_elim_exst A p : (map translate A) ⊢E (translate p) -> A ⊢E p.
  Proof. intro. now apply ndAgree, translation_elim, agree.
  Defined.

End Existential.