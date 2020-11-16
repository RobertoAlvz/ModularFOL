Require Import Coq.Vectors.Vector.

Class Signature := B_S { Funcs : Type; fun_ar : Funcs -> nat ; Preds : Type; pred_ar : Preds -> nat }.
Context {Sigma : Signature}.

Notation fin := nat.
Definition shift := S.
Definition var_zero := 0.

Definition V n t := Vector.t t n.
Definition V_map {term : Type} (f : term -> term ) {n:nat} (v : Vector.t term n) := Vector.map f v.

Definition scons {term: Type} (x : term) (xi : fin -> term) (n : fin) : term := match n with
    |0 => x
    |S n => xi n
end.

Definition funcomp {X Y Z} (g : Y -> Z) (f : X -> Y) :=
  fun x => g (f x).