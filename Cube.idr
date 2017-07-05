module Cube

Id : Type
Id = String

-- Kinds
data Kind = Star
          | Box

-- Expressions
data Expr = Var Id
          | App Expr Expr
          | Lambda Id Expr Expr
          | Pi Id Expr Expr
          | Knd Kind

%name Expr e, e'

-- Free Variables
freeVars : Expr -> List Id
freeVars (Var id) = [id]
freeVars (App fun arg) =  freeVars fun `union` freeVars arg
freeVars (Lambda id ty expr) = freeVars ty `union` (freeVars expr \\ [id])
freeVars (Pi id kind ty) = freeVars kind `union` (freeVars ty \\ [id])

-- Substitution
subst : Id -> Expr -> Expr -> Expr
subst id expr = sub
  where free : List Id
        free = freeVars expr

        freshId : Expr -> Id -> Id
        freshId e i = loop i
          where vars : List Id
                vars = free ++ freeVars e

                loop : Id -> Id
                loop i = if elem i vars then loop (i ++ "'") else i

        mutual
          sub : Expr -> Expr
          sub this@(Var id') = if id == id' then expr else this
          sub (App fun arg) = App (sub fun) (sub arg)
          sub (Lambda id' ty body) = abstr Lambda id' ty body
          sub (Pi id' kind ty) = abstr Pi id' kind ty
          sub this@(Knd _) = this

          abstr : (cons : Id -> Expr -> Expr -> Expr) -> (id : Id) -> (ty : Expr) -> (body : Expr) -> Expr
          abstr cons id' ty body =
            if id == id' then
              cons id' (sub ty) body
            else if elem id' free then
              let fresh = freshId body id'
                  body' = subst id (Var id') body
              in cons fresh (sub ty) (sub body')
            else
              cons id' (sub ty) (sub body)

-- Normal Form
nf : Expr -> Expr
nf expr = spine expr []
  where app : Expr -> List Expr -> Expr
        app e xs = foldl App e $ map nf xs

        spine : Expr -> List Expr -> Expr
        spine (App fun arg) xs = spine fun $ arg :: xs
        spine (Lambda id t e) [] = Lambda id (nf t) (nf e)
        spine (Lambda id _ e) (x :: xs) = spine (subst id x e) xs
        spine (Pi id knd ty) xs = app (Pi id (nf knd) (nf ty)) xs
        spine e xs = app e xs

-- Alpha Equivalence
alphaEq : Expr -> Expr -> Bool
alphaEq (Var x) (Var x') = x == x'
alphaEq (App e x) (App e' x') = alphaEq e e' && alphaEq x x'
alphaEq (Lambda x t e) (Lambda x' t' e') = alphaEq t t' && alphaEq e (subst x' (Var x) e')
alphaEq (Pi x k t) (Pi x' k' t') = alphaEq k k' && alphaEq t (subst x' (Var x) t')
alphaEq (Knd Star) (Knd Star) = True
alphaEq (Knd Box) (Knd Box) = True
alphaEq _ _ = False

-- Beta Equivalence
betaEq : Expr -> Expr -> Bool
betaEq e1 e2 = alphaEq (nf e1) (nf e2)
