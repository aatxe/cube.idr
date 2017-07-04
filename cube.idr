Id : Type
Id = String

-- Expressions
data Expr = Var Id
          | App Expr Expr
          | Lambda Id Expr

%name Expr e, e'

-- Free Variables
freeVars : Expr -> List Id
freeVars (Var x) = [x]
freeVars (App f e) =  freeVars f `union` freeVars e
freeVars (Lambda x e) = freeVars e \\ [x]

-- Substitution
-- sub id with x in e
subst : Id -> Expr -> Expr -> Expr
subst id x e@(Var y) = if id == y then x else e
subst id x (App e e') = App (subst id x e) (subst id x e')
subst id x (Lambda y e) =
      if id == y then
          Lambda y e
      else if elem y free then
           let y' = freshId e y
               e' = subst id (Var y') e
           in Lambda y' $ subst id x e'
      else
          Lambda y $ subst id x e
    where free : List Id
          free = freeVars x
          freshId : Expr -> Id -> Id
          freshId e i = loop i
          where vars : List Id
                vars = free ++ freeVars e
                loop : Id -> Id
                loop i = if elem i vars then loop (i ++ "'") else i

-- Weak Head Normal Form
whnf : Expr -> Expr
whnf e = spine e []
     where spine : Expr -> List Expr -> Expr
           spine (App f x) xs = spine f (x :: xs)
           spine (Lambda id e) (x :: xs) = spine (subst id x e) xs
           spine e xs = foldl App e xs

-- Alpha Equivalence
alphaEq : Expr -> Expr -> Bool
alphaEq (Var x) (Var x') = x == x'
alphaEq (App e x) (App e' x') = alphaEq e e' && alphaEq x x'
alphaEq (Lambda x e) (Lambda x' e') = alphaEq e $ subst x' (Var x) e'
alphaEq _ _ = False

-- Normal Form
nf : Expr -> Expr
nf e = spine e []
    where spine : Expr -> List Expr -> Expr
          spine (App f x) xs = spine f $ x :: xs
          spine (Lambda x e) [] = Lambda x $ nf e
          spine (Lambda x e) (y :: ys) = spine (subst x y e) ys
          spine f xs = foldl App f $ map nf xs

-- Beta Equivalence
betaEq : Expr -> Expr -> Bool
betaEq e1 e2 = alphaEq (nf e1) (nf e2)

-- Expressions in Lambda Calculus

z : Expr
z = Var "z"

s : Expr
s = Var "s"

m : Expr
m = Var "m"

n : Expr
n = Var "n"

app2 : Expr -> Expr -> Expr -> Expr
app2 f x y = App (App f x) y

zero : Expr
zero  = Lambda "s" $ Lambda "z" z

one : Expr
one   = Lambda "s" $ Lambda "z" $ App s z

two : Expr
two   = Lambda "s" $ Lambda "z" $ App s $ App s z

three : Expr
three = Lambda "s" $ Lambda "z" $ App s $ App s $ App s z

plus : Expr
plus  = Lambda "m" $ Lambda "n" $ Lambda "s" $ Lambda "z" $ app2 m s (app2 n s z)
