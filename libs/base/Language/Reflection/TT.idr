module Language.Reflection.TT

import public Data.List
import Data.Strings
import Data.IORef

public export
FilePos : Type
FilePos = (Int, Int)

public export
FileName : Type
FileName = String

||| A file context is a filename together with starting and ending positions
public export
data FC = MkFC FileName FilePos FilePos
        | EmptyFC

public export
emptyFC : FC
emptyFC = EmptyFC

public export
data NameType : Type where
     Bound   : NameType
     Func    : NameType
     DataCon : (tag : Int) -> (arity : Nat) -> NameType
     TyCon   : (tag : Int) -> (arity : Nat) -> NameType

public export
data Constant
    = I Int
    | BI Integer
    | B8 Int
    | B16 Int
    | B32 Int
    | B64 Integer
    | Str String
    | Ch Char
    | Db Double
    | WorldVal

    | IntType
    | IntegerType
    | Bits8Type
    | Bits16Type
    | Bits32Type
    | Bits64Type
    | StringType
    | CharType
    | DoubleType
    | WorldType

export
Show Constant where
  show (I x) = show x
  show (BI x) = show x
  show (B8 x) = show x
  show (B16 x) = show x
  show (B32 x) = show x
  show (B64 x) = show x
  show (Str x) = show x
  show (Ch x) = show x
  show (Db x) = show x
  show WorldVal = "%MkWorld"
  show IntType = "Int"
  show IntegerType = "Integer"
  show Bits8Type = "Bits8"
  show Bits16Type = "Bits16"
  show Bits32Type = "Bits32"
  show Bits64Type = "Bits64"
  show StringType = "String"
  show CharType = "Char"
  show DoubleType = "Double"
  show WorldType = "%World"

public export
data Namespace = MkNS (List String) -- namespace, stored in reverse order

export
showSep : String -> List String -> String
showSep sep [] = ""
showSep sep [x] = x
showSep sep (x :: xs) = x ++ sep ++ showSep sep xs

export
Show Namespace where
  show (MkNS ns) = showSep "." (reverse ns)

public export
data UseSide = UseLeft | UseRight

public export
data DotReason = NonLinearVar
               | VarApplied
               | NotConstructor
               | ErasedArg
               | UserDotted
               | UnknownDot

export
data LogLevel : Type where
  MkLogLevel : List String -> Nat -> LogLevel

export
Show LogLevel where

  show (MkLogLevel ps n) = case ps of
    [] => show n
    _  => fastConcat (intersperse "." ps) ++ ":" ++ show n

public export
data Name : Type where
     NS : Namespace -> Name -> Name -- in a namespace
     UN : String -> Name -- user defined name
     MN : String -> Int -> Name -- machine generated name
     PV : Name -> Int -> Name -- pattern variable name; int is the resolved function id
     DN : String -> Name -> Name -- a name and how to display it
     RF : String -> Name  -- record field name
     Nested : (Int, Int) -> Name -> Name -- nested function name
     CaseBlock : String -> Int -> Name -- case block nested in (resolved) name
     WithBlock : String -> Int -> Name -- with block nested in (resolved) name
     Resolved : Int -> Name -- resolved, index into context

export
Show Name where
  show (NS ns n@(RF _)) = show ns ++ ".(" ++ show n ++ ")"
  show (NS ns n) = show ns ++ "." ++ show n
  show (UN x) = x
  show (MN x y) = "{" ++ x ++ ":" ++ show y ++ "}"
  show (PV n d) = "{P:" ++ show n ++ ":" ++ show d ++ "}"
  show (DN str n) = str
  show (RF n) = "." ++ n
  show (Nested (outer, idx) inner)
      = show outer ++ ":" ++ show idx ++ ":" ++ show inner
  show (CaseBlock outer i) = "case block in " ++ outer
  show (WithBlock outer i) = "with block in " ++ outer
  show (Resolved x) = "$resolved" ++ show x

export
data ZeroOneOmega = Rig0 | Rig1 | RigW

public export
M0 : ZeroOneOmega
M0 = Rig0

public export
M1 : ZeroOneOmega
M1 = Rig1

public export
MW : ZeroOneOmega
MW = RigW

export
Show ZeroOneOmega where
  show Rig0 = "Rig0"
  show Rig1 = "Rig1"
  show RigW = "RigW"

public export
RigCount : Type
RigCount = ZeroOneOmega
 
public export
data PiInfo t = Implicit | Explicit | AutoImplicit | DefImplicit t

public export
ImplicitArg : PiInfo t
ImplicitArg = Implicit

public export
ExplicitArg : PiInfo t
ExplicitArg = Explicit

export
Show t => Show (PiInfo t) where
  show Implicit = "Implicit"
  show Explicit = "Explicit"
  show AutoImplicit = "AutoImplicit"
  show (DefImplicit t) = "DefImplicit " ++ show t

public export
data IsVar : Name -> Nat -> List Name -> Type where
     First : IsVar n Z (n :: ns)
     Later : IsVar n i ns -> IsVar n (S i) (m :: ns)

public export
data LazyReason = LInf | LLazy | LUnknown

export
data TT : Type where [external]

{-
-- Type checked terms in the core TT
public export
data TT : List Name -> Type where
     Local : FC -> (idx : Nat) -> (0 prf : IsVar name idx vars) -> TT vars
     Ref : FC -> NameType -> Name -> TT vars
     Pi : FC -> Count -> PiInfo (TT vars) ->
          (x : Name) -> (argTy : TT vars) -> (retTy : TT (x :: vars)) ->
          TT vars
     Lam : FC -> Count -> PiInfo (TT vars) ->
           (x : Name) -> (argTy : TT vars) -> (scope : TT (x :: vars)) ->
           TT vars
     App : FC -> TT vars -> TT vars -> TT vars
     TDelayed : FC -> LazyReason -> TT vars -> TT vars
     TDelay : FC -> LazyReason -> (ty : TT vars) -> (arg : TT vars) -> TT vars
     TForce : FC -> LazyReason -> TT vars -> TT vars
     PrimVal : FC -> Constant -> TT vars
     Erased : FC -> TT vars
     TType : FC -> TT vars
     -}

public export
data TotalReq = Total | CoveringOnly | PartialOK

public export
data Visibility = Private | Export | Public

export
Show Visibility where
  show Private = "private"
  show Export = "export"
  show Public = "public export"
