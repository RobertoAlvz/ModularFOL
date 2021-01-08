Require Export unscoped header_extensible.
Require Export termsyntax.

Section form_atomic.
Context {Sigma : Signature}.

Variable form : Type.

Variable subst_form : forall   (sigmaterm : ( fin ) -> term ) (s : form ), form .

Variable idSubst_form : forall  (sigmaterm : ( fin ) -> term ) (Eqterm : forall x, sigmaterm x = (var_term ) x) (s : form ), subst_form sigmaterm s = s.

Variable ext_form : forall   (sigmaterm : ( fin ) -> term ) (tauterm : ( fin ) -> term ) (Eqterm : forall x, sigmaterm x = tauterm x) (s : form ), subst_form sigmaterm s = subst_form tauterm s.

Variable compSubstSubst_form : forall    (sigmaterm : ( fin ) -> term ) (tauterm : ( fin ) -> term ) (thetaterm : ( fin ) -> term ) (Eqterm : forall x, ((funcomp) (subst_term tauterm) sigmaterm) x = thetaterm x) (s : form ), subst_form tauterm (subst_form sigmaterm s) = subst_form thetaterm s.

Inductive form_atomic  : Type :=
  | Pred : forall (p : Preds), ( vect term (pred_ar p) ) -> form_atomic .

Variable retract_form_atomic : retract form_atomic form.

Definition Pred_ (p : Preds) (s0 : vect term (pred_ar p)) : _ :=
  inj (Pred p s0).

Lemma congr_Pred_ { p : Preds }  { s0 : vect term (pred_ar p) } { t0 : vect term (pred_ar p) } (H1 : s0 = t0) : Pred_  p s0 = Pred_  p t0 .
Proof. congruence. Qed.

(* Variable retract_ren_form : forall   (xiterm : ( fin ) -> fin) s, ren_form xiterm (inj s) = ren_form_atomic xiterm s. *)

Definition subst_form_atomic   (sigmaterm : ( fin ) -> term ) (s : form_atomic ) : form  :=
    match s return form  with
    | Pred  p s0 => Pred_  p ((vect_map (subst_term sigmaterm)) s0)
    end.

Variable retract_subst_form : forall   (sigmaterm : ( fin ) -> term ) s, subst_form sigmaterm (inj s) = subst_form_atomic sigmaterm s.

Definition idSubst_form_atomic  (sigmaterm : ( fin ) -> term ) (Eqterm : forall x, sigmaterm x = (var_term ) x) (s : form_atomic ) : subst_form_atomic sigmaterm s = inj s :=
    match s return subst_form_atomic sigmaterm s = inj s with
    | Pred  p s0 => congr_Pred_ ((vect_id (idSubst_term sigmaterm Eqterm)) s0)
    end.

(* 
Definition ext_form_atomic   (sigmaterm : ( fin ) -> term ) (tauterm : ( fin ) -> term ) (Eqterm : forall x, sigmaterm x = tauterm x) (s : form_atomic ) : subst_form_atomic sigmaterm s = subst_form_atomic tauterm s :=
    match s return subst_form_atomic sigmaterm s = subst_form_atomic tauterm s with
    | Pred  p s0 => congr_Pred_ ((vect_ext (ext_term sigmaterm tauterm Eqterm)) s0)
    end.
*)
Definition compSubstSubst_form_atomic    (sigmaterm : ( fin ) -> term ) (tauterm : ( fin ) -> term ) (thetaterm : ( fin ) -> term ) (Eqterm : forall x, ((funcomp) (subst_term tauterm) sigmaterm) x = thetaterm x) (s : form_atomic ) : subst_form tauterm (subst_form_atomic sigmaterm s) = subst_form_atomic thetaterm s :=
    match s return subst_form tauterm (subst_form_atomic sigmaterm s) = subst_form_atomic thetaterm s with
    | Pred  p s0 => (eq_trans) (retract_subst_form (_) (Pred p (_))) (congr_Pred_ ((vect_comp (compSubstSubst_term sigmaterm tauterm thetaterm Eqterm)) s0))
    end.
(*
Lemma instId_form_atomic  : subst_form_atomic (var_term ) = inj .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => idSubst_form_atomic (var_term ) (fun n => eq_refl) ((id) x))). Qed.

Lemma compComp_form_atomic    (sigmaterm : ( fin ) -> term ) (tauterm : ( fin ) -> term ) (s : form_atomic ) : subst_form tauterm (subst_form_atomic sigmaterm s) = subst_form_atomic ((funcomp) (subst_term tauterm) sigmaterm) s .
Proof. exact (compSubstSubst_form_atomic sigmaterm tauterm (_) (fun n => eq_refl) s). Qed.

Lemma compComp'_form_atomic    (sigmaterm : ( fin ) -> term ) (tauterm : ( fin ) -> term ) : (funcomp) (subst_form tauterm) (subst_form_atomic sigmaterm) = subst_form_atomic ((funcomp) (subst_term tauterm) sigmaterm) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => compComp_form_atomic sigmaterm tauterm n)). Qed.

Definition isIn_form_form_atomic (s : form) (t : form_atomic) : Prop :=
  match t with
  | Pred t0  => False
  end.
 *)

End form_atomic.
