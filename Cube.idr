module Cube

-- Error Handling
import Debug.Error
%language ElabReflection

-- Identifiers
Id : Type
Id = String

%name Id id, id'

-- Kinds
data Kind = Star
          | Box


%name Kind k, k'

DecEq Kind where
  decEq Star Star = Yes Refl
  decEq Box Box = Yes Refl
  decEq Box Star = No (\(Refl) impossible)
  decEq Star Box = No (\(Refl) impossible)

-- Expressions
mutual
  data Expr = Var Id
            | App Expr Expr
            | Lambda Id Ty Expr
            | Pi Id Ty Ty
            | Knd Kind

  Ty : Type
  Ty = Expr

%name Expr e, e'
%name Ty ty, ty'

DecEq Expr where
  decEq (Var x) (Var y) with (decEq x y)
    decEq (Var y) (Var y) | (Yes Refl) = Yes Refl
    decEq (Var x) (Var y) | (No contra) = No (\(Refl) => contra Refl)
  decEq (App f1 a1) (App f2 a2) with (decEq f1 f2)
    decEq (App f2 a1) (App f2 a2) | (Yes Refl) with (decEq a1 a2)
      decEq (App f2 a2) (App f2 a2) | (Yes Refl) | (Yes Refl) = Yes Refl
      decEq (App f2 a1) (App f2 a2) | (Yes Refl) | (No contra) = No (\(Refl) => contra Refl)
    decEq (App f1 a1) (App f2 a2) | (No contra) = No (\(Refl) => contra Refl)
  decEq (Lambda i1 t1 e1) (Lambda i2 t2 e2) with (decEq i1 i2)
    decEq (Lambda i2 t1 e1) (Lambda i2 t2 e2) | (Yes Refl) with (decEq t1 t2)
      decEq (Lambda i2 t2 e1) (Lambda i2 t2 e2) | (Yes Refl) | (Yes Refl) with (decEq e1 e2)
        decEq (Lambda i2 t2 e2) (Lambda i2 t2 e2) | (Yes Refl) | (Yes Refl) | (Yes Refl) = Yes Refl
        decEq (Lambda i2 t2 e1) (Lambda i2 t2 e2) | (Yes Refl) | (Yes Refl) | (No contra) = No (\(Refl) => contra Refl)
      decEq (Lambda i2 t1 e1) (Lambda i2 t2 e2) | (Yes Refl) | (No contra) = No (\(Refl) => contra Refl)
    decEq (Lambda i1 t1 e1) (Lambda i2 t2 e2) | (No contra) = No (\(Refl) => contra Refl)
  decEq (Pi i1 k1 t1) (Pi i2 k2 t2) with (decEq i1 i2)
    decEq (Pi i2 k1 t1) (Pi i2 k2 t2) | (Yes Refl) with (decEq k1 k2)
      decEq (Pi i2 k2 t1) (Pi i2 k2 t2) | (Yes Refl) | (Yes Refl) with (decEq t1 t2)
        decEq (Pi i2 k2 t2) (Pi i2 k2 t2) | (Yes Refl) | (Yes Refl) | (Yes Refl) = Yes Refl
        decEq (Pi i2 k2 t1) (Pi i2 k2 t2) | (Yes Refl) | (Yes Refl) | (No contra) = No (\(Refl) => contra Refl)
      decEq (Pi i2 k1 t1) (Pi i2 k2 t2) | (Yes Refl) | (No contra) = No (\(Refl) => contra Refl)
    decEq (Pi i1 k1 t1) (Pi i2 k2 t2) | (No contra) = No (\(Refl) => contra Refl)
  decEq (Knd k1) (Knd k2) with (decEq k1 k2)
    decEq (Knd k2) (Knd k2) | (Yes Refl) = Yes Refl
    decEq (Knd k1) (Knd k2) | (No contra) = No (\(Refl) => contra Refl)
  decEq e1 e2 = No ?hole

Eq Expr where
  e1 == e2 with (decEq e1 e2)
    e1 == e2 | (Yes prf) = True
    e1 == e2 | (No contra) = False


-- The set of allowed kind pairs.
-- Changing this changes our position on the lambda cube.
allowedKinds : List (Ty, Ty)
allowedKinds = [(Knd Star, Knd Star)]

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

          abstr : (cons : Id -> Ty -> Expr -> Expr) -> (id : Id) -> (ty : Ty) -> (body : Expr) -> Expr
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

-- Type Checking Result
TC : Type -> Type
TC x = Either String x

-- Type Environments
Env : Type
Env = List (Id, Ty)

%name Env env, env'

initialEnv : Env
initialEnv = []

extend : Id -> Ty -> Env -> Env
extend id ty env = (id, ty) :: env

find : Id -> Env -> TC Ty
find id env with (lookup id env)
  find id _ | Nothing = Left $ "Unbound variable: " ++ id
  find _  _ | (Just ty) = Right ty

-- Type Checking
tcImpl : Env -> Expr -> TC Ty
tcImpl env (Var id) = find id env
tcImpl env (App fun arg) with (tcImpl env fun)
  tcImpl env (App _ arg) | Right (Pi id argTy retTy) with (tcImpl env arg)
    tcImpl env (App fun arg) | Right (Pi id argTy retTy) | Right tyArg =
      if betaEq argTy tyArg then
        Right $ subst id arg retTy
      else
        Left "Argument type mismatch in function application."
    tcImpl _ _ | Right _ | Left err = Left err
  tcImpl _ _ | Right ty = Left "Attempted to something with a non-Pi type."
  tcImpl _ _ | Left err = Left err
tcImpl env (Lambda id ty body) = do
  tcImpl env ty
  let env' = extend id ty env
  tyBody <- tcImpl env' body
  let piTy = Pi id ty tyBody
  tcImpl env piTy
  pure piTy
tcImpl env (Pi id argTy retTy) = do
  argKnd <- tcImpl env argTy
  let env' = extend id argTy env
  retKnd <- tcImpl env' retTy
  if (argKnd, retKnd) `elem` allowedKinds then
    Right retKnd
  else
    Left "Encountered a bad abstraction."
tcImpl env (Knd Star) = pure $ Knd Box
tcImpl env (Knd Box) = Left "Unexpected kind: \box"

typeCheck : Expr -> Ty
typeCheck e with (tcImpl initialEnv e)
  typeCheck _ | (Left err) = error err
  typeCheck _ | (Right ty) = ty
