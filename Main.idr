module Main

import Language.Reflection

%language ElabReflection

x : String
x = "hi"

%runElab (putStrLn x)

main : IO ()
main = putStrLn {io=IO} (%runElab (pure `(x)))
