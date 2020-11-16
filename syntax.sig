term  : Type
form  : Type
Funcs : Type
Preds : Type
V : Functor

Func (f : Funcs) : "V (fun_ar f)" (term) -> term
Pred (p : Preds) : "V (pred_ar p)" (term) -> form

begin imp
    Fal : form
    Impl : form -> form -> form
end imp

begin univ
    All  : (term -> form) -> form
end univ

compose implicative := imp
compose full := imp :+: univ