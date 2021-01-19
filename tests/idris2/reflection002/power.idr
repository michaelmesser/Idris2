import Language.Reflection

%language ElabReflection

powerFn : Nat -> TTImp
powerFn Z = `(const 1)
powerFn (S k) = `(\x => mult x (~(powerFn k) x))

powerFn' : Nat -> Nat -> Nat -- This doesn't need elab at all, right?
powerFn' Z = const 1
powerFn' (S k) = (\x => mult (powerFn' k x) x)

%macro
power : Nat -> Elab TTImp
power n = pure (powerFn n)

power' : Nat -> Nat -> Nat
power' n = powerFn' n

cube : Nat -> Nat
cube = power 3

cube' : Nat -> Nat
cube' = power' 3
