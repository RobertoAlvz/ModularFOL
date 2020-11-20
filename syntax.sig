term  : Type
form  : Type
Funcs : Type
Preds : Type

Func (f : Funcs) : "V f" (term) -> term
Pred (p : Preds) : "V p" (term) -> form

begin imp
    Fal : form
    Impl : form -> form -> form
end imp

begin univ
    All  : (term -> form) -> form
end univ

compose implicative := imp
compose full := imp :+: univ