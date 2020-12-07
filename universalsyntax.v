Require Export unscoped header_extensible.
Require Export termsyntax.

Section form_universal.
Variable form : Type.

Variable subst_form : forall   (sigmaterm : ( fin ) -> term ) (s : form ), form .

Variable idSubst_form : forall  (sigmaterm : ( fin ) -> term ) (Eqterm : forall x, sigmaterm x = (var_term ) x) (s : form ), subst_form sigmaterm s = s.

Variable ext_form : forall   (sigmaterm : ( fin ) -> term ) (tauterm : ( fin ) -> term ) (Eqterm : forall x, sigmaterm x = tauterm x) (s : form ), subst_form sigmaterm s = subst_form tauterm s.

Variable compSubstSubst_form : forall    (sigmaterm : ( fin ) -> term ) (tauterm : ( fin ) -> term ) (thetaterm : ( fin ) -> term ) (Eqterm : forall x, ((funcomp) (subst_term tauterm) sigmaterm) x = thetaterm x) (s : form ), subst_form tauterm (subst_form sigmaterm s) = subst_form thetaterm s.

Inductive form_universal  : Type :=
  | All : ( form   ) -> form_universal .

Variable retract_form_universal : retract form_universal form.

Definition All_  (s0 : form  ) : _ :=
  inj (All s0).

Lemma congr_All_  { s0 : form   } { t0 : form   } (H1 : s0 = t0) : All_  s0 = All_  t0 .
Proof. congruence. Qed.

(* Variable retract_ren_form : forall   (xiterm : ( fin ) -> fin) s, ren_form xiterm (inj s) = ren_form_universal xiterm s. *)

Definition subst_form_universal   (sigmaterm : ( fin ) -> term ) (s : form_universal ) : form  :=
    match s return form  with
    | All  s0 => All_  ((subst_form (up_term_term sigmaterm)) s0)
    end.

Variable retract_subst_form : forall   (sigmaterm : ( fin ) -> term ) s, subst_form sigmaterm (inj s) = subst_form_universal sigmaterm s.
(* 
Definition idSubst_form_universal  (sigmaterm : ( fin ) -> term ) (Eqterm : forall x, sigmaterm x = (var_term ) x) (s : form_universal ) : subst_form_universal sigmaterm s = inj s :=
    match s return subst_form_universal sigmaterm s = inj s with
    | All  s0 => congr_All_ ((idSubst_form (up_term_term sigmaterm) (upId_term_term (_) Eqterm)) s0)
    end.

Definition ext_form_universal   (sigmaterm : ( fin ) -> term ) (tauterm : ( fin ) -> term ) (Eqterm : forall x, sigmaterm x = tauterm x) (s : form_universal ) : subst_form_universal sigmaterm s = subst_form_universal tauterm s :=
    match s return subst_form_universal sigmaterm s = subst_form_universal tauterm s with
    | All  s0 => congr_All_ ((ext_form (up_term_term sigmaterm) (up_term_term tauterm) (upExt_term_term (_) (_) Eqterm)) s0)
    end.
Definition compSubstSubst_form_universal    (sigmaterm : ( fin ) -> term ) (tauterm : ( fin ) -> term ) (thetaterm : ( fin ) -> term ) (Eqterm : forall x, ((funcomp) (subst_term tauterm) sigmaterm) x = thetaterm x) (s : form_universal ) : subst_form tauterm (subst_form_universal sigmaterm s) = subst_form_universal thetaterm s :=
    match s return subst_form tauterm (subst_form_universal sigmaterm s) = subst_form_universal thetaterm s with
    | All  s0 => (eq_trans) (retract_subst_form (_) (All (_))) (congr_All_ ((compSubstSubst_form (up_term_term sigmaterm) (up_term_term tauterm) (up_term_term thetaterm) (up_subst_subst_term_term (_) (_) (_) Eqterm)) s0))
    end.

Lemma instId_form_universal  : subst_form_universal (var_term ) = inj .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => idSubst_form_universal (var_term ) (fun n => eq_refl) ((id) x))). Qed.

Lemma compComp_form_universal    (sigmaterm : ( fin ) -> term ) (tauterm : ( fin ) -> term ) (s : form_universal ) : subst_form tauterm (subst_form_universal sigmaterm s) = subst_form_universal ((funcomp) (subst_term tauterm) sigmaterm) s .
Proof. exact (compSubstSubst_form_universal sigmaterm tauterm (_) (fun n => eq_refl) s). Qed.

Lemma compComp'_form_universal    (sigmaterm : ( fin ) -> term ) (tauterm : ( fin ) -> term ) : (funcomp) (subst_form tauterm) (subst_form_universal sigmaterm) = subst_form_universal ((funcomp) (subst_term tauterm) sigmaterm) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => compComp_form_universal sigmaterm tauterm n)). Qed.

Definition isIn_form_form_universal (s : form) (t : form_universal) : Prop :=
  match t with
  | All t0  => s = t0
  end.
*)

End form_universal.

Notation "∀ p ":= (All_ _ _ p) (at level 60).
