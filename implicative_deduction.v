Require Export implicativesyntax.

Reserved Notation "A ⊢ p" (at level 70).
Reserved Notation "A ⊢I p" (at level 70).


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

  Inductive nd_imp (A : list form) : form -> Prop :=
    | ndAgree p : A ⊢ p -> A ⊢I p
    | ndHyp p : In p A -> A ⊢I p
    | ndExp p : A ⊢ ⊥ -> A ⊢I p
    | ndII p q : (p :: A) ⊢ q -> A ⊢I p ~> q
    | ndIE p q : A ⊢ p ~> q -> A ⊢ p -> A ⊢I q
  where "A ⊢I p" := (nd_imp A p).

Variable agree : forall A p, A ⊢I p -> A ⊢ p.

  Variable weakening : forall A B p, A ⊢ p -> incl A B -> B ⊢ p.
  Lemma weakening_imp A B p : A ⊢I p -> incl A B -> B ⊢I p.
  Proof. intro. revert B. destruct H; intros B Hinc;
    [ now apply ndAgree, (weakening A) 
    | now apply ndHyp, (Hinc p)
    | now apply ndExp, (weakening A) 
    | apply ndII 
    | now apply (ndIE _ p _ (weakening _ _ _ H Hinc)), (weakening A) ].
    - apply (weakening (p::A) (p::B) _ H), incl_cons; [ now left | now apply incl_tl ].
  Defined.


  Variable translate : form -> form.
  Definition translate_imp (p : form_implicative form) : form := match p with
    | Fal _ => ¬¬⊥
    | Impl _ p q => ¬¬( (translate p) ~> (translate q))
  end.

  Variable translation_int : forall A p, A ⊢ p -> (map translate A) ⊢ (translate p).
  Lemma translation_int_imp A p : A ⊢I p -> (map translate A) ⊢I (translate p).
  Proof. intro H. apply agree in H. apply translation_int in H. now apply ndAgree.
  Defined.

  Variable translation_elim : forall A p, (map translate A) ⊢ (translate p) -> A ⊢ p.
  Lemma double_neg_elim_imp A p : (map translate A) ⊢I (translate p) -> A ⊢I p.
  Proof. intro. now apply ndAgree, translation_elim, agree.
  Defined.
End implicative.

Notation "A ⊢I p" := (nd_imp A p) (at level 70).