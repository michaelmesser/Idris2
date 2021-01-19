import Language.Reflection

%language ElabReflection

data NatExpr : Nat -> Type where
     Plus : NatExpr x -> NatExpr y -> NatExpr (plus x y)
     Mult : NatExpr x -> NatExpr y -> NatExpr (mult x y)
     Dbl : NatExpr x -> NatExpr (mult 2 x)
     Val : (val : Nat) -> NatExpr val

getNatExpr : TTImp -> TTImp -- Also doesn't need elab
getNatExpr `(Prelude.Types.plus ~(x) ~(y))
   = `(Plus ~(getNatExpr x) ~(getNatExpr y))
getNatExpr `(Prelude.Types.mult (Prelude.Types.S (Prelude.Types.S Prelude.Types.Z)) ~(y))
   = `(Dbl ~(getNatExpr y))
getNatExpr `(Prelude.Types.mult ~(x) ~(y))
   = `(Mult ~(getNatExpr x) ~(getNatExpr y))
getNatExpr x = `(Val ~x)

%macro
mkNatExpr : Elab TTImp
mkNatExpr
    = do Just `(Main.NatExpr ~(expr)) <- goal
              | _ => fail "Goal is not a NatExpr"
         pure (getNatExpr expr)

test1 : (x : Nat) -> (y : Nat) -> NatExpr (plus x (plus y x))
test1 x y = mkNatExpr -- yes, auto implicits can do this too :)

test2 : (x : Nat) -> (y : Nat) -> NatExpr (plus x (mult y x))
test2 x y = mkNatExpr

test3 : (x : Nat) -> (y : Nat) -> NatExpr (plus x (mult 2 x))
test3 x y = mkNatExpr -- auto implicit search gets something different
