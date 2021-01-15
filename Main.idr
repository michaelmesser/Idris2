module Main

import Language.Reflection
import Data.Vect

%language ElabReflection

data Checked : Type -> Type -- Term
check : TTImp -> Elab (Checked a)
eval : Checked a -> Elab a
applyCheck : Checked (a -> b) -> Checked a -> Checked b

q : Elab (Checked Nat)
q = do
    four <- check {a=Nat} `(4)
    twoPlus <- check {a=Nat->Nat} `((+) 2)
    pure $ applyCheck {a=Nat} twoPlus four

data NatExpr : Nat -> Type where
     Plus : NatExpr x -> NatExpr y -> NatExpr (plus x y)
     Mult : NatExpr x -> NatExpr y -> NatExpr (mult x y)
     Dbl : NatExpr x -> NatExpr (mult 2 x)
     Val : (val : Nat) -> NatExpr val

getNatExpr : TTImp -> Elab TTImp
getNatExpr `(Prelude.Types.plus ~x ~y)
   = pure `(Plus ~!(getNatExpr x) ~!(getNatExpr y))
getNatExpr `(Prelude.Types.mult (Prelude.Types.S (Prelude.Types.S Prelude.Types.Z)) ~y)
   = pure `(Dbl ~!(getNatExpr y))
getNatExpr `(Prelude.Types.mult ~x ~y)
   = pure `(Mult ~!(getNatExpr x) ~!(getNatExpr y))
getNatExpr x = pure `(Val ~x)

%macro
mkNatExpr : Elab TTImp
mkNatExpr 
    = do putStrLn "hi"
         Just `(Main.NatExpr ~(expr)) <- goal
              | _ => fail "Goal is not a NatExpr"
         getNatExpr expr

test1 : (x : Nat) -> (y : Nat) -> NatExpr (plus x (plus y x))
test1 x y = mkNatExpr -- yes, auto implicits can do this too :)

test2 : (x : Nat) -> (y : Nat) -> NatExpr (plus x (mult y x))
test2 x y = mkNatExpr

test3 : (x : Nat) -> (y : Nat) -> NatExpr (plus x (mult 2 x))
test3 x y = mkNatExpr -- auto implicit search gets something different

x : String
x = "hi"

main : IO ()
main = putStrLn {io=IO} (%runElab (pure `(x)))


test : Elab ()
test = do
    let name = UN "name"
    declare `[
        ~name : String
        ~name = "hello"
    ]
