Require Export unscoped header_extensible.

Require Export atomicsyntax implicativesyntax.

Reserved Notation "A ⊢ p" (at level 70).
Reserved Notation "A ⊢A p" (at level 70).

Section atomic.
  Variable form : Type.
  Variable retract : retract (form_atomic) form.

  Variable retract_implicative : included form_implicative form.

  Variable translate : form -> form.
  Definition translate_atomic (p : form_atomic) : form := ¬¬(inj p).

End atomic.