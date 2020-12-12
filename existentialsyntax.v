Require Export unscoped header_extensible.
Require Export termsyntax.

Section form_existential.
Context {Sigma : Signature}.

Variable form : Type.

Variable subst_form : forall   (sigmaterm : ( fin ) -> term ) (s : form ), form .

Variable idSubst_form : forall  (sigmaterm : ( fin ) -> term ) (Eqterm : forall x, sigmaterm x = (var_term ) x) (s : form ), subst_form sigmaterm s = s.

Variable ext_form : forall   (sigmaterm : ( fin ) -> term ) (tauterm : ( fin ) -> term ) (Eqterm : forall x, sigmaterm x = tauterm x) (s : form ), subst_form sigmaterm s = subst_form tauterm s.

Variable compSubstSubst_form : forall    (sigmaterm : ( fin ) -> term ) (tauterm : ( fin ) -> term ) (thetaterm : ( fin ) -> term ) (Eqterm : forall x, ((funcomp) (subst_term tauterm) sigmaterm) x = thetaterm x) (s : form ), subst_form tauterm (subst_form sigmaterm s) = subst_form thetaterm s.

Inductive form_existential  : Type :=
  | Exist : ( form   ) -> form_existential .

Variable retract_form_existential : retract form_existential form.

Definition Exist_  (s0 : form  ) : _ :=
  inj (Exist s0).

Lemma congr_Exist_  { s0 : form   } { t0 : form   } (H1 : s0 = t0) : Exist_  s0 = Exist_  t0 .
Proof. congruence. Qed.

(* Variable retract_ren_form : forall   (xiterm : ( fin ) -> fin) s, ren_form xiterm (inj s) = ren_form_existential xiterm s. *)

Definition subst_form_existential   (sigmaterm : ( fin ) -> term ) (s : form_existential ) : form  :=
    match s return form  with
    | Exist  s0 => Exist_  ((subst_form (up_term_term sigmaterm)) s0)
    end.

Variable retract_subst_form : forall   (sigmaterm : ( fin ) -> term ) s, subst_form sigmaterm (inj s) = subst_form_existential sigmaterm s.
(* 
Definition idSubst_form_existential  (sigmaterm : ( fin ) -> term ) (Eqterm : forall x, sigmaterm x = (var_term ) x) (s : form_existential ) : subst_form_existential sigmaterm s = inj s :=
    match s return subst_form_existential sigmaterm s = inj s with
    | Exist  s0 => congr_Exist_ ((idSubst_form (up_term_term sigmaterm) (upId_term_term (_) Eqterm)) s0)
    end.

Definition ext_form_existential   (sigmaterm : ( fin ) -> term ) (tauterm : ( fin ) -> term ) (Eqterm : forall x, sigmaterm x = tauterm x) (s : form_existential ) : subst_form_existential sigmaterm s = subst_form_existential tauterm s :=
    match s return subst_form_existential sigmaterm s = subst_form_existential tauterm s with
    | Exist  s0 => congr_Exist_ ((ext_form (up_term_term sigmaterm) (up_term_term tauterm) (upExt_term_term (_) (_) Eqterm)) s0)
    end.

Definition compSubstSubst_form_existential    (sigmaterm : ( fin ) -> term ) (tauterm : ( fin ) -> term ) (thetaterm : ( fin ) -> term ) (Eqterm : forall x, ((funcomp) (subst_term tauterm) sigmaterm) x = thetaterm x) (s : form_existential ) : subst_form tauterm (subst_form_existential sigmaterm s) = subst_form_existential thetaterm s :=
    match s return subst_form tauterm (subst_form_existential sigmaterm s) = subst_form_existential thetaterm s with
    | Exist  s0 => (eq_trans) (retract_subst_form (_) (Exist (_))) (congr_Exist_ ((compSubstSubst_form (up_term_term sigmaterm) (up_term_term tauterm) (up_term_term thetaterm) (up_subst_subst_term_term (_) (_) (_) Eqterm)) s0))
    end.

Lemma instId_form_existential  : subst_form_existential (var_term ) = inj .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => idSubst_form_existential (var_term ) (fun n => eq_refl) ((id) x))). Qed.

Lemma compComp_form_existential    (sigmaterm : ( fin ) -> term ) (tauterm : ( fin ) -> term ) (s : form_existential ) : subst_form tauterm (subst_form_existential sigmaterm s) = subst_form_existential ((funcomp) (subst_term tauterm) sigmaterm) s .
Proof. exact (compSubstSubst_form_existential sigmaterm tauterm (_) (fun n => eq_refl) s). Qed.

Lemma compComp'_form_existential    (sigmaterm : ( fin ) -> term ) (tauterm : ( fin ) -> term ) : (funcomp) (subst_form tauterm) (subst_form_existential sigmaterm) = subst_form_existential ((funcomp) (subst_term tauterm) sigmaterm) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => compComp_form_existential sigmaterm tauterm n)). Qed.

Definition isIn_form_form_existential (s : form) (t : form_existential) : Prop :=
  match t with
  | Exist t0  => s = t0
  end.
 *)

End form_existential.
