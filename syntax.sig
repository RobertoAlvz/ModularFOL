term  : Type
form  : Type
Funcs : Type
Preds : Type
vect : Functor

Func (f : Funcs) : "vect (fun_ar f)" (term) -> term

begin implicative
    Fal : form
    Impl : form -> form -> form
end implicative

begin univ
    Pred (p : Preds) : "vect (pred_ar p)" (term) -> form
    All  : (term -> form) -> form
end univ

full := imp :+: univ
