term  : Type
form  : Type
Funcs : Type
Preds : Type
vect : Functor

Func (f : Funcs) : "vect (fun_ar f)" (term) -> term

begin atomic
    Pred (p : Preds) : "vect (pred_ar p)" (term) -> form
end atomic

begin implicative
    Fal : form
    Impl : form -> form -> form
end implicative

begin universal
    All  : (term -> form) -> form
end universal

begin conjunctive
    Conj : form -> form -> form
end conjunctive

begin disjunctive
    Disj : form -> form -> form
end disjunctive

begin existential
    Exist : (term -> form) -> form
end existential

core := implicative :+: universal
full := atomic :+: implicative :+: universal :+: conjunctive :+: disjunctive :+: existential
