
Require Export atomicsyntax implicativesyntax universalsyntax conjunctivesyntax disjunctivesyntax existentialsyntax termsyntax.

Section form.
Context {Sigma : Signature}.
Inductive form  : Type :=
  | In_form_atomic : ( form_atomic   ) -> form 
  | In_form_implicative : ( form_implicative form  ) -> form 
  | In_form_universal : ( form_universal form  ) -> form 
  | In_form_conjunctive : ( form_conjunctive form  ) -> form 
  | In_form_disjunctive : ( form_disjunctive form  ) -> form 
  | In_form_existential : ( form_existential form  ) -> form .

Lemma congr_In_form_atomic  { s0 : form_atomic   } { t0 : form_atomic   } (H1 : s0 = t0) : In_form_atomic  s0 = In_form_atomic  t0 .
Proof. congruence. Qed.

Lemma congr_In_form_implicative  { s0 : form_implicative form  } { t0 : form_implicative form  } (H1 : s0 = t0) : In_form_implicative  s0 = In_form_implicative  t0 .
Proof. congruence. Qed.

Lemma congr_In_form_universal  { s0 : form_universal form  } { t0 : form_universal form  } (H1 : s0 = t0) : In_form_universal  s0 = In_form_universal  t0 .
Proof. congruence. Qed.

Lemma congr_In_form_conjunctive  { s0 : form_conjunctive form  } { t0 : form_conjunctive form  } (H1 : s0 = t0) : In_form_conjunctive  s0 = In_form_conjunctive  t0 .
Proof. congruence. Qed.

Lemma congr_In_form_disjunctive  { s0 : form_disjunctive form  } { t0 : form_disjunctive form  } (H1 : s0 = t0) : In_form_disjunctive  s0 = In_form_disjunctive  t0 .
Proof. congruence. Qed.

Lemma congr_In_form_existential  { s0 : form_existential form  } { t0 : form_existential form  } (H1 : s0 = t0) : In_form_existential  s0 = In_form_existential  t0 .
Proof. congruence. Qed.

Global Instance retract_form_universal_form  : retract (form_universal form) form := Build_retract In_form_universal (fun x => match x with
| In_form_universal s  => Datatypes.Some s
| _ => Datatypes.None
end) (fun s => eq_refl) (fun s t => match t with
| In_form_universal t'  => fun H => congr_In_form_universal ((eq_sym) (Some_inj H))
| _ => some_none_explosion
end) .

Global Instance retract_form_implicative_form  : retract (form_implicative form) form := Build_retract In_form_implicative (fun x => match x with
| In_form_implicative s  => Datatypes.Some s
| _ => Datatypes.None
end) (fun s => eq_refl) (fun s t => match t with
| In_form_implicative t'  => fun H => congr_In_form_implicative ((eq_sym) (Some_inj H))
| _ => some_none_explosion
end) .

Global Instance retract_form_existential_form  : retract (form_existential form) form := Build_retract In_form_existential (fun x => match x with
| In_form_existential s  => Datatypes.Some s
| _ => Datatypes.None
end) (fun s => eq_refl) (fun s t => match t with
| In_form_existential t'  => fun H => congr_In_form_existential ((eq_sym) (Some_inj H))
| _ => some_none_explosion
end) .

Global Instance retract_form_disjunctive_form  : retract (form_disjunctive form) form := Build_retract In_form_disjunctive (fun x => match x with
| In_form_disjunctive s  => Datatypes.Some s
| _ => Datatypes.None
end) (fun s => eq_refl) (fun s t => match t with
| In_form_disjunctive t'  => fun H => congr_In_form_disjunctive ((eq_sym) (Some_inj H))
| _ => some_none_explosion
end) .

Global Instance retract_form_conjunctive_form  : retract (form_conjunctive form) form := Build_retract In_form_conjunctive (fun x => match x with
| In_form_conjunctive s  => Datatypes.Some s
| _ => Datatypes.None
end) (fun s => eq_refl) (fun s t => match t with
| In_form_conjunctive t'  => fun H => congr_In_form_conjunctive ((eq_sym) (Some_inj H))
| _ => some_none_explosion
end) .

Global Instance retract_form_atomic_form  : retract (form_atomic ) form := Build_retract In_form_atomic (fun x => match x with
| In_form_atomic s  => Datatypes.Some s
| _ => Datatypes.None
end) (fun s => eq_refl) (fun s t => match t with
| In_form_atomic t'  => fun H => congr_In_form_atomic ((eq_sym) (Some_inj H))
| _ => some_none_explosion
end) .

Fixpoint subst_form   (sigmaterm : ( fin ) -> term ) (s : form ) : form  :=
    match s return form  with
    | In_form_atomic  s0 =>   subst_form_atomic form _ sigmaterm s0
    | In_form_implicative  s0 =>   subst_form_implicative form subst_form _ sigmaterm s0
    | In_form_universal  s0 =>   subst_form_universal form subst_form _ sigmaterm s0
    | In_form_conjunctive  s0 =>   subst_form_conjunctive form subst_form _ sigmaterm s0
    | In_form_disjunctive  s0 =>   subst_form_disjunctive form subst_form _ sigmaterm s0
    | In_form_existential  s0 =>   subst_form_existential form subst_form _ sigmaterm s0
    end.

Fixpoint idSubst_form  (sigmaterm : ( fin ) -> term ) (Eqterm : forall x, sigmaterm x = (var_term ) x) (s : form ) : subst_form sigmaterm s = s.
Proof. destruct s; 
  [ eapply idSubst_form_atomic
  | eapply idSubst_form_implicative
  | eapply idSubst_form_universal
  | eapply idSubst_form_conjunctive
  | eapply idSubst_form_disjunctive
  | eapply idSubst_form_existential
  ]; eauto.
Defined.
(*
Fixpoint ext_form   (sigmaterm : ( fin ) -> term ) (tauterm : ( fin ) -> term ) (Eqterm : forall x, sigmaterm x = tauterm x) (s : form ) : subst_form sigmaterm s = subst_form tauterm s :=
    match s return subst_form sigmaterm s = subst_form tauterm s with
    | In_form_atomic  s0 =>  ((ext_form_atomic form sigmaterm tauterm Eqterm) s0)
    | In_form_implicative  s0 =>  ((ext_form_implicative form sigmaterm tauterm Eqterm) s0)
    | In_form_universal  s0 =>  ((ext_form_universal form up_term_form upExt_term_form sigmaterm tauterm Eqterm) s0)
    | In_form_conjunctive  s0 =>  ((ext_form_conjunctive form sigmaterm tauterm Eqterm) s0)
    | In_form_disjunctive  s0 =>  ((ext_form_disjunctive form sigmaterm tauterm Eqterm) s0)
    | In_form_existential  s0 =>  ((ext_form_existential form up_term_form upExt_term_form sigmaterm tauterm Eqterm) s0)
    end.
*)
Fixpoint compSubstSubst_form    (sigmaterm : ( fin ) -> term ) (tauterm : ( fin ) -> term ) (thetaterm : ( fin ) -> term ) (Eqterm : forall x, ((funcomp) (subst_term tauterm) sigmaterm) x = thetaterm x) (s : form ) : subst_form tauterm (subst_form sigmaterm s) = subst_form thetaterm s.
Proof. destruct s;
  [ eapply compSubstSubst_form_atomic
  | eapply compSubstSubst_form_implicative
  | eapply compSubstSubst_form_universal
  | eapply compSubstSubst_form_conjunctive
  | eapply compSubstSubst_form_disjunctive
  | eapply compSubstSubst_form_existential
  ]; eauto.
Defined.

Lemma instId_form  : subst_form (var_term ) = id .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => idSubst_form (var_term ) (fun n => eq_refl) ((id) x))). Qed.

Lemma compComp_form    (sigmaterm : ( fin ) -> term ) (tauterm : ( fin ) -> term ) (s : form ) : subst_form tauterm (subst_form sigmaterm s) = subst_form ((funcomp) (subst_term tauterm) sigmaterm) s .
Proof. exact (compSubstSubst_form sigmaterm tauterm (_) (fun n => eq_refl) s). Qed.

Lemma compComp'_form    (sigmaterm : ( fin ) -> term ) (tauterm : ( fin ) -> term ) : (funcomp) (subst_form tauterm) (subst_form sigmaterm) = subst_form ((funcomp) (subst_term tauterm) sigmaterm) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => compComp_form sigmaterm tauterm n)). Qed.
































(*
Global Instance Subst_term   : Subst1 (( fin ) -> term ) (term ) (term ) := @subst_term   .

Global Instance Subst_form   : Subst1 (( fin ) -> term ) (form ) (form ) := @subst_form   .

Global Instance VarInstance_term  : Var (fin) (term ) := @var_term  .

Notation "x '__term'" := (var_term x) (at level 5, format "x __term") : subst_scope.

Notation "x '__term'" := (@ids (_) (_) VarInstance_term x) (at level 5, only printing, format "x __term") : subst_scope.

Notation "'var'" := (var_term) (only printing, at level 1) : subst_scope.

Class Up_term X Y := up_term : ( X ) -> Y.

Notation "↑__term" := (up_term) (only printing) : subst_scope.

Notation "↑__term" := (up_term_term) (only printing) : subst_scope.

Global Instance Up_term_term   : Up_term (_) (_) := @up_term_term   .

Notation "s [ sigmaterm ]" := (subst_term sigmaterm s) (at level 7, left associativity, only printing) : subst_scope.

Notation "[ sigmaterm ]" := (subst_term sigmaterm) (at level 1, left associativity, only printing) : fscope.

Notation "s [ sigmaterm ]" := (subst_form_universal sigmaterm s) (at level 7, left associativity, only printing) : subst_scope.

Notation "[ sigmaterm ]" := (subst_form_universal sigmaterm) (at level 1, left associativity, only printing) : fscope.

Notation "s [ sigmaterm ]" := (subst_form_implicative sigmaterm s) (at level 7, left associativity, only printing) : subst_scope.

Notation "[ sigmaterm ]" := (subst_form_implicative sigmaterm) (at level 1, left associativity, only printing) : fscope.

Notation "s [ sigmaterm ]" := (subst_form_existential sigmaterm s) (at level 7, left associativity, only printing) : subst_scope.

Notation "[ sigmaterm ]" := (subst_form_existential sigmaterm) (at level 1, left associativity, only printing) : fscope.

Notation "s [ sigmaterm ]" := (subst_form_disjunctive sigmaterm s) (at level 7, left associativity, only printing) : subst_scope.

Notation "[ sigmaterm ]" := (subst_form_disjunctive sigmaterm) (at level 1, left associativity, only printing) : fscope.

Notation "s [ sigmaterm ]" := (subst_form_conjunctive sigmaterm s) (at level 7, left associativity, only printing) : subst_scope.

Notation "[ sigmaterm ]" := (subst_form_conjunctive sigmaterm) (at level 1, left associativity, only printing) : fscope.

Notation "s [ sigmaterm ]" := (subst_form_atomic sigmaterm s) (at level 7, left associativity, only printing) : subst_scope.

Notation "[ sigmaterm ]" := (subst_form_atomic sigmaterm) (at level 1, left associativity, only printing) : fscope.

Notation "s [ sigmaterm ]" := (subst_form sigmaterm s) (at level 7, left associativity, only printing) : subst_scope.

Notation "[ sigmaterm ]" := (subst_form sigmaterm) (at level 1, left associativity, only printing) : fscope.

Ltac auto_unfold := repeat unfold subst1,  subst2,  Subst1,  Subst2,  ids,  ren1,  ren2,  Ren1,  Ren2,  Subst_term,  Subst_form,  VarInstance_term.

Tactic Notation "auto_unfold" "in" "*" := repeat unfold subst1,  subst2,  Subst1,  Subst2,  ids,  ren1,  ren2,  Ren1,  Ren2,  Subst_term,  Subst_form,  VarInstance_term in *.
 *)

End form.

(* Ltac asimpl' := repeat first [progress rewrite ?instId_term| progress rewrite ?compComp_term| progress rewrite ?compComp'_term| progress rewrite ?instId_form_universal| progress rewrite ?compComp_form_universal| progress rewrite ?compComp'_form_universal| progress rewrite ?instId_form_implicative| progress rewrite ?compComp_form_implicative| progress rewrite ?compComp'_form_implicative| progress rewrite ?instId_form_existential| progress rewrite ?compComp_form_existential| progress rewrite ?compComp'_form_existential| progress rewrite ?instId_form_disjunctive| progress rewrite ?compComp_form_disjunctive| progress rewrite ?compComp'_form_disjunctive| progress rewrite ?instId_form_conjunctive| progress rewrite ?compComp_form_conjunctive| progress rewrite ?compComp'_form_conjunctive| progress rewrite ?instId_form_atomic| progress rewrite ?compComp_form_atomic| progress rewrite ?compComp'_form_atomic| progress rewrite ?instId_form| progress rewrite ?compComp_form| progress rewrite ?compComp'_form| progress rewrite ?varL_term| progress (unfold up_ren, up_term_term)| progress (cbn [subst_term subst_form_universal subst_form_implicative subst_form_existential subst_form_disjunctive subst_form_conjunctive subst_form_atomic subst_form])| fsimpl].

Ltac asimpl := repeat try unfold_funcomp; auto_unfold in *; asimpl'; repeat try unfold_funcomp.

Tactic Notation "asimpl" "in" hyp(J) := revert J; asimpl; intros J.

Tactic Notation "auto_case" := auto_case (asimpl; cbn; eauto).

Tactic Notation "asimpl" "in" "*" := auto_unfold in *; repeat first [progress rewrite ?instId_term in *| progress rewrite ?compComp_term in *| progress rewrite ?compComp'_term in *| progress rewrite ?instId_form_universal in *| progress rewrite ?compComp_form_universal in *| progress rewrite ?compComp'_form_universal in *| progress rewrite ?instId_form_implicative in *| progress rewrite ?compComp_form_implicative in *| progress rewrite ?compComp'_form_implicative in *| progress rewrite ?instId_form_existential in *| progress rewrite ?compComp_form_existential in *| progress rewrite ?compComp'_form_existential in *| progress rewrite ?instId_form_disjunctive in *| progress rewrite ?compComp_form_disjunctive in *| progress rewrite ?compComp'_form_disjunctive in *| progress rewrite ?instId_form_conjunctive in *| progress rewrite ?compComp_form_conjunctive in *| progress rewrite ?compComp'_form_conjunctive in *| progress rewrite ?instId_form_atomic in *| progress rewrite ?compComp_form_atomic in *| progress rewrite ?compComp'_form_atomic in *| progress rewrite ?instId_form in *| progress rewrite ?compComp_form in *| progress rewrite ?compComp'_form in *| progress rewrite ?varL_term in *| progress (unfold up_ren, up_term_term in * )| progress (cbn [subst_term subst_form_universal subst_form_implicative subst_form_existential subst_form_disjunctive subst_form_conjunctive subst_form_atomic subst_form] in * )| fsimpl in *].
 *)

Ltac substify := auto_unfold.

Ltac renamify := auto_unfold.
