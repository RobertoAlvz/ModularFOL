Require Export unscoped header_extensible.
Require Export termsyntax.

Section form_conjunctive.
Variable form : Type.

Variable subst_form : forall   (sigmaterm : ( fin ) -> term ) (s : form ), form .

Variable idSubst_form : forall  (sigmaterm : ( fin ) -> term ) (Eqterm : forall x, sigmaterm x = (var_term ) x) (s : form ), subst_form sigmaterm s = s.

Variable ext_form : forall   (sigmaterm : ( fin ) -> term ) (tauterm : ( fin ) -> term ) (Eqterm : forall x, sigmaterm x = tauterm x) (s : form ), subst_form sigmaterm s = subst_form tauterm s.

Variable compSubstSubst_form : forall    (sigmaterm : ( fin ) -> term ) (tauterm : ( fin ) -> term ) (thetaterm : ( fin ) -> term ) (Eqterm : forall x, ((funcomp) (subst_term tauterm) sigmaterm) x = thetaterm x) (s : form ), subst_form tauterm (subst_form sigmaterm s) = subst_form thetaterm s.

Inductive form_conjunctive  : Type :=
  | Conj : ( form   ) -> ( form   ) -> form_conjunctive .

Variable retract_form_conjunctive : retract form_conjunctive form.

Definition Conj_  (s0 : form  ) (s1 : form  ) : _ :=
  inj (Conj s0 s1).

Lemma congr_Conj_  { s0 : form   } { s1 : form   } { t0 : form   } { t1 : form   } (H1 : s0 = t0) (H2 : s1 = t1) : Conj_  s0 s1 = Conj_  t0 t1 .
Proof. congruence. Qed.

(* Variable retract_ren_form : forall   (xiterm : ( fin ) -> fin) s, ren_form xiterm (inj s) = ren_form_conjunctive xiterm s. *)

Definition subst_form_conjunctive   (sigmaterm : ( fin ) -> term ) (s : form_conjunctive ) : form  :=
    match s return form  with
    | Conj  s0 s1 => Conj_  ((subst_form sigmaterm) s0) ((subst_form sigmaterm) s1)
    end.

Variable retract_subst_form : forall   (sigmaterm : ( fin ) -> term ) s, subst_form sigmaterm (inj s) = subst_form_conjunctive sigmaterm s.

Definition idSubst_form_conjunctive  (sigmaterm : ( fin ) -> term ) (Eqterm : forall x, sigmaterm x = (var_term ) x) (s : form_conjunctive ) : subst_form_conjunctive sigmaterm s = inj s :=
    match s return subst_form_conjunctive sigmaterm s = inj s with
    | Conj  s0 s1 => congr_Conj_ ((idSubst_form sigmaterm Eqterm) s0) ((idSubst_form sigmaterm Eqterm) s1)
    end.

Definition ext_form_conjunctive   (sigmaterm : ( fin ) -> term ) (tauterm : ( fin ) -> term ) (Eqterm : forall x, sigmaterm x = tauterm x) (s : form_conjunctive ) : subst_form_conjunctive sigmaterm s = subst_form_conjunctive tauterm s :=
    match s return subst_form_conjunctive sigmaterm s = subst_form_conjunctive tauterm s with
    | Conj  s0 s1 => congr_Conj_ ((ext_form sigmaterm tauterm Eqterm) s0) ((ext_form sigmaterm tauterm Eqterm) s1)
    end.

Definition compSubstSubst_form_conjunctive    (sigmaterm : ( fin ) -> term ) (tauterm : ( fin ) -> term ) (thetaterm : ( fin ) -> term ) (Eqterm : forall x, ((funcomp) (subst_term tauterm) sigmaterm) x = thetaterm x) (s : form_conjunctive ) : subst_form tauterm (subst_form_conjunctive sigmaterm s) = subst_form_conjunctive thetaterm s :=
    match s return subst_form tauterm (subst_form_conjunctive sigmaterm s) = subst_form_conjunctive thetaterm s with
    | Conj  s0 s1 => (eq_trans) (retract_subst_form (_) (Conj (_) (_))) (congr_Conj_ ((compSubstSubst_form sigmaterm tauterm thetaterm Eqterm) s0) ((compSubstSubst_form sigmaterm tauterm thetaterm Eqterm) s1))
    end.

Lemma instId_form_conjunctive  : subst_form_conjunctive (var_term ) = inj .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => idSubst_form_conjunctive (var_term ) (fun n => eq_refl) ((id) x))). Qed.

Lemma compComp_form_conjunctive    (sigmaterm : ( fin ) -> term ) (tauterm : ( fin ) -> term ) (s : form_conjunctive ) : subst_form tauterm (subst_form_conjunctive sigmaterm s) = subst_form_conjunctive ((funcomp) (subst_term tauterm) sigmaterm) s .
Proof. exact (compSubstSubst_form_conjunctive sigmaterm tauterm (_) (fun n => eq_refl) s). Qed.

Lemma compComp'_form_conjunctive    (sigmaterm : ( fin ) -> term ) (tauterm : ( fin ) -> term ) : (funcomp) (subst_form tauterm) (subst_form_conjunctive sigmaterm) = subst_form_conjunctive ((funcomp) (subst_term tauterm) sigmaterm) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => compComp_form_conjunctive sigmaterm tauterm n)). Qed.

Definition isIn_form_form_conjunctive (s : form) (t : form_conjunctive) : Prop :=
  match t with
  | Conj t0 t1  => or (s = t0) (s = t1)
  end.

End form_conjunctive.
