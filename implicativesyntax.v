Require Export unscoped header_extensible.
Require Export termsyntax.

Section form_implicative.
Variable form : Type.

Variable subst_form : forall   (sigmaterm : ( fin ) -> term ) (s : form ), form .

Variable idSubst_form : forall  (sigmaterm : ( fin ) -> term ) (Eqterm : forall x, sigmaterm x = (var_term ) x) (s : form ), subst_form sigmaterm s = s.

Variable ext_form : forall   (sigmaterm : ( fin ) -> term ) (tauterm : ( fin ) -> term ) (Eqterm : forall x, sigmaterm x = tauterm x) (s : form ), subst_form sigmaterm s = subst_form tauterm s.

Variable compSubstSubst_form : forall    (sigmaterm : ( fin ) -> term ) (tauterm : ( fin ) -> term ) (thetaterm : ( fin ) -> term ) (Eqterm : forall x, ((funcomp) (subst_term tauterm) sigmaterm) x = thetaterm x) (s : form ), subst_form tauterm (subst_form sigmaterm s) = subst_form thetaterm s.

Inductive form_implicative  : Type :=
  | Fal : form_implicative 
  | Impl : ( form   ) -> ( form   ) -> form_implicative .

Variable retract_form_implicative : retract form_implicative form.

Definition Fal_  : _ :=
  inj (Fal ).

Definition Impl_  (s0 : form  ) (s1 : form  ) : _ :=
  inj (Impl s0 s1).

Lemma congr_Fal_  : Fal_  = Fal_  .
Proof. congruence. Qed.

Lemma congr_Impl_  { s0 : form   } { s1 : form   } { t0 : form   } { t1 : form   } (H1 : s0 = t0) (H2 : s1 = t1) : Impl_  s0 s1 = Impl_  t0 t1 .
Proof. congruence. Qed.

(* Variable retract_ren_form : forall   (xiterm : ( fin ) -> fin) s, ren_form xiterm (inj s) = ren_form_implicative xiterm s. *)

Definition subst_form_implicative   (sigmaterm : ( fin ) -> term ) (s : form_implicative ) : form  :=
    match s return form  with
    | Fal   => Fal_ 
    | Impl  s0 s1 => Impl_  ((subst_form sigmaterm) s0) ((subst_form sigmaterm) s1)
    end.

Variable retract_subst_form : forall   (sigmaterm : ( fin ) -> term ) s, subst_form sigmaterm (inj s) = subst_form_implicative sigmaterm s.

Definition idSubst_form_implicative  (sigmaterm : ( fin ) -> term ) (Eqterm : forall x, sigmaterm x = (var_term ) x) (s : form_implicative ) : subst_form_implicative sigmaterm s = inj s :=
    match s return subst_form_implicative sigmaterm s = inj s with
    | Fal   => congr_Fal_ 
    | Impl  s0 s1 => congr_Impl_ ((idSubst_form sigmaterm Eqterm) s0) ((idSubst_form sigmaterm Eqterm) s1)
    end.

Definition ext_form_implicative   (sigmaterm : ( fin ) -> term ) (tauterm : ( fin ) -> term ) (Eqterm : forall x, sigmaterm x = tauterm x) (s : form_implicative ) : subst_form_implicative sigmaterm s = subst_form_implicative tauterm s :=
    match s return subst_form_implicative sigmaterm s = subst_form_implicative tauterm s with
    | Fal   => congr_Fal_ 
    | Impl  s0 s1 => congr_Impl_ ((ext_form sigmaterm tauterm Eqterm) s0) ((ext_form sigmaterm tauterm Eqterm) s1)
    end.

Definition compSubstSubst_form_implicative    (sigmaterm : ( fin ) -> term ) (tauterm : ( fin ) -> term ) (thetaterm : ( fin ) -> term ) (Eqterm : forall x, ((funcomp) (subst_term tauterm) sigmaterm) x = thetaterm x) (s : form_implicative ) : subst_form tauterm (subst_form_implicative sigmaterm s) = subst_form_implicative thetaterm s :=
    match s return subst_form tauterm (subst_form_implicative sigmaterm s) = subst_form_implicative thetaterm s with
    | Fal   => (eq_trans) (retract_subst_form (_) (Fal )) (congr_Fal_ )
    | Impl  s0 s1 => (eq_trans) (retract_subst_form (_) (Impl (_) (_))) (congr_Impl_ ((compSubstSubst_form sigmaterm tauterm thetaterm Eqterm) s0) ((compSubstSubst_form sigmaterm tauterm thetaterm Eqterm) s1))
    end.

Lemma instId_form_implicative  : subst_form_implicative (var_term ) = inj .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => idSubst_form_implicative (var_term ) (fun n => eq_refl) ((id) x))). Qed.

Lemma compComp_form_implicative    (sigmaterm : ( fin ) -> term ) (tauterm : ( fin ) -> term ) (s : form_implicative ) : subst_form tauterm (subst_form_implicative sigmaterm s) = subst_form_implicative ((funcomp) (subst_term tauterm) sigmaterm) s .
Proof. exact (compSubstSubst_form_implicative sigmaterm tauterm (_) (fun n => eq_refl) s). Qed.

Lemma compComp'_form_implicative    (sigmaterm : ( fin ) -> term ) (tauterm : ( fin ) -> term ) : (funcomp) (subst_form tauterm) (subst_form_implicative sigmaterm) = subst_form_implicative ((funcomp) (subst_term tauterm) sigmaterm) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => compComp_form_implicative sigmaterm tauterm n)). Qed.

Definition isIn_form_form_implicative (s : form) (t : form_implicative) : Prop :=
  match t with
  | Fal   => False
  | Impl t0 t1  => or (s = t0) (s = t1)
  end.

End form_implicative.

Notation "p ~> q" := (inj (Impl _ p q)) (at level 60).
Notation "⊥" := (inj (Fal _)).
Notation "¬ p" := (p ~> ⊥) (at level 60).
