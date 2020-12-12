Require Export unscoped header_extensible.

Require Export atomicsyntax implicativesyntax.

Reserved Notation "A ⊢ p" (at level 70).
Reserved Notation "A ⊢A p" (at level 70).

Section atomic.
  Context {Sigma : Signature}.

  Variable form : Type.

  Variable retract : retract (form_atomic) form.
  Variable retract_implicative : included form_implicative form.

  Variable translate : form -> form.
  Definition translate_atomic (p : form_atomic) : form := ¬¬(inj p).
  Notation "« p »" := (translate p).

  Variable subst_form : (fin -> term) -> form -> form.
  Variable translation_subst : forall sigma q, «subst_form sigma q» = subst_form sigma «q».
  Lemma translation_subst_atm sigma q : «subst_form sigma (inj q)» = subst_form sigma «inj q».
  Proof. destruct q; repeat now rewrite translation_subst.
  Defined.

End atomic.