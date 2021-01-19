module Language.Reflection.TTImp

import public Language.Reflection.TT

-- Unchecked terms and declarations in the intermediate language
-- Information about names in nested blocks

-- Unchecked terms, with implicit arguments
-- This is the raw, elaboratable form.
-- Higher level expressions (e.g. case, pattern matching let, where blocks,
-- do notation, etc, should elaborate via this, perhaps in some local
-- context).
public export
data BindMode = PI RigCount | PATTERN | NONE

mutual
  public export
  data RawImp : Type where
       IVar : FC -> Name -> RawImp
       IPi : FC -> RigCount -> PiInfo RawImp -> Maybe Name ->
             (argTy : RawImp) -> (retTy : RawImp) -> RawImp
       ILam : FC -> RigCount -> PiInfo RawImp -> Maybe Name ->
              (argTy : RawImp) -> (lamTy : RawImp) -> RawImp
       ILet : FC -> RigCount -> Name ->
              (nTy : RawImp) -> (nVal : RawImp) ->
              (scope : RawImp) -> RawImp
       ICase : FC -> RawImp -> (ty : RawImp) ->
               List ImpClause -> RawImp
       ILocal : FC -> List ImpDecl -> RawImp -> RawImp
       -- Local definitions made elsewhere, but that we're pushing
       -- into a case branch as nested names.
       -- An appearance of 'uname' maps to an application of
       -- 'internalName' to 'args'.
       ICaseLocal : FC -> (uname : Name) ->
                    (internalName : Name) ->
                    (args : List Name) -> RawImp -> RawImp

       IUpdate : FC -> List IFieldUpdate -> RawImp -> RawImp

       IApp : FC -> RawImp -> RawImp -> RawImp
       IAutoApp : FC -> RawImp -> RawImp -> RawImp
       INamedApp : FC -> RawImp -> Name -> RawImp -> RawImp
       IWithApp : FC -> RawImp -> RawImp -> RawImp

       ISearch : FC -> (depth : Nat) -> RawImp
       IAlternative : FC -> AltType -> List RawImp -> RawImp
       IRewrite : FC -> RawImp -> RawImp -> RawImp
       ICoerced : FC -> RawImp -> RawImp

       -- Any implicit bindings in the scope should be bound here, using
       -- the given binder
       IBindHere : FC -> BindMode -> RawImp -> RawImp
       -- A name which should be implicitly bound
       IBindVar : FC -> String -> RawImp
       -- An 'as' pattern, valid on the LHS of a clause only
       IAs : FC -> UseSide -> Name -> RawImp -> RawImp
       -- A 'dot' pattern, i.e. one which must also have the given value
       -- by unification
       IMustUnify : FC -> DotReason -> RawImp -> RawImp

       -- Laziness annotations
       IDelayed : FC -> LazyReason -> RawImp -> RawImp -- the type
       IDelay : FC -> RawImp -> RawImp -- delay constructor
       IForce : FC -> RawImp -> RawImp

       -- Quasiquoting
       IQuote : FC -> RawImp -> RawImp
       IQuoteName : FC -> Name -> RawImp
       IQuoteDecl : FC -> List ImpDecl -> RawImp
       IUnquote : FC -> RawImp -> RawImp
       IRunElab : FC -> RawImp -> RawImp

       IPrimVal : FC -> (c : Constant) -> RawImp
       IType : FC -> RawImp
       IHole : FC -> String -> RawImp

       IUnifyLog : FC -> LogLevel -> RawImp -> RawImp
       -- An implicit value, solved by unification, but which will also be
       -- bound (either as a pattern variable or a type variable) if unsolved
       -- at the end of elaborator
       Implicit : FC -> (bindIfUnsolved : Bool) -> RawImp

       -- with-disambiguation
       IWithUnambigNames : FC -> List Name -> RawImp -> RawImp

  public export
  TTImp : Type
  TTImp = RawImp

  public export
  data IFieldUpdate : Type where
       ISetField : (path : List String) -> RawImp -> IFieldUpdate
       ISetFieldApp : (path : List String) -> RawImp -> IFieldUpdate

  public export
  data AltType : Type where
       FirstSuccess : AltType
       Unique : AltType
       UniqueDefault : RawImp -> AltType

  export
    Show RawImp where
      show (IVar fc n) = show n
      show (IPi fc c p n arg ret)
         = "(%pi " ++ show c ++ " " ++ show p ++ " " ++
           showPrec App n ++ " " ++ show arg ++ " " ++ show ret ++ ")"
      show (ILam fc c p n arg sc)
         = "(%lam " ++ show c ++ " " ++ show p ++ " " ++
           showPrec App n ++ " " ++ show arg ++ " " ++ show sc ++ ")"
      show (ILet fc c n ty val sc)
         = "(%let " ++ show c ++ " " ++ " " ++ show n ++ " " ++ show ty ++
           " " ++ show val ++ " " ++ show sc ++ ")"
      show (ICase _ scr scrty alts)
         = "(%case (" ++ show scr ++ " : " ++ show scrty ++ ") " ++ show alts ++ ")"
      show (ILocal _ def scope)
         = "(%local (" ++ show def ++ ") " ++ show scope ++ ")"
      show (ICaseLocal _ uname iname args sc)
         = "(%caselocal (" ++ show uname ++ " " ++ show iname
               ++ " " ++ show args ++ ") " ++ show sc ++ ")"
      show (IUpdate _ flds rec)
         = "(%record " ++ showSep ", " (map show flds) ++ " " ++ show rec ++ ")"
      show (IApp fc f a)
         = "(" ++ show f ++ " " ++ show a ++ ")"
      show (INamedApp fc f n a)
         = "(" ++ show f ++ " [" ++ show n ++ " = " ++ show a ++ "])"
      show (IAutoApp fc f a)
         = "(" ++ show f ++ " [" ++ show a ++ "])"
      show (IWithApp fc f a)
         = "(" ++ show f ++ " | " ++ show a ++ ")"
      show (ISearch fc d)
         = "%search"
      show (IAlternative fc ty alts)
         = "(|" ++ showSep "," (map show alts) ++ "|)"
      show (IRewrite _ rule tm)
         = "(%rewrite (" ++ show rule ++ ") (" ++ show tm ++ "))"
      show (ICoerced _ tm) = "(%coerced " ++ show tm ++ ")"

      show (IBindHere fc b sc)
         = "(%bindhere " ++ show sc ++ ")"
      show (IBindVar fc n) = "$" ++ n
      show (IAs fc _ n tm) = show n ++ "@(" ++ show tm ++ ")"
      show (IMustUnify fc r tm) = ".(" ++ show tm ++ ")"
      show (IDelayed fc r tm) = "(%delayed " ++ show tm ++ ")"
      show (IDelay fc tm) = "(%delay " ++ show tm ++ ")"
      show (IForce fc tm) = "(%force " ++ show tm ++ ")"
      show (IQuote fc tm) = "(%quote " ++ show tm ++ ")"
      show (IQuoteName fc tm) = "(%quotename " ++ show tm ++ ")"
      show (IQuoteDecl fc tm) = "(%quotedecl " ++ show tm ++ ")"
      show (IUnquote fc tm) = "(%unquote " ++ show tm ++ ")"
      show (IRunElab fc tm) = "(%runelab " ++ show tm ++ ")"
      show (IPrimVal fc c) = show c
      show (IHole _ x) = "?" ++ x
      show (IUnifyLog _ lvl x) = "(%logging " ++ show lvl ++ " " ++ show x ++ ")"
      show (IType fc) = "%type"
      show (Implicit fc True) = "_"
      show (Implicit fc False) = "?"
      show (IWithUnambigNames fc ns rhs) = "(%with " ++ show ns ++ " " ++ show rhs ++ ")"

  export
  Show IFieldUpdate where
    show (ISetField p val) = showSep "->" p ++ " = " ++ show val
    show (ISetFieldApp p val) = showSep "->" p ++ " $= " ++ show val

  public export
  data FnOpt : Type where
       Inline : FnOpt
       TCInline : FnOpt
       -- Flag means the hint is a direct hint, not a function which might
       -- find the result (e.g. chasing parent interface dictionaries)
       Hint : Bool -> FnOpt
       -- Flag means to use as a default if all else fails
       GlobalHint : Bool -> FnOpt
       ExternFn : FnOpt
       -- Defined externally, list calling conventions
       ForeignFn : List RawImp -> FnOpt
       -- assume safe to cancel arguments in unification
       Invertible : FnOpt
       Totality : TotalReq -> FnOpt
       Macro : FnOpt
       SpecArgs : List Name -> FnOpt

  export
  Show FnOpt where
    show Inline = "%inline"
    show TCInline = "%tcinline"
    show (Hint t) = "%hint " ++ show t
    show (GlobalHint t) = "%globalhint " ++ show t
    show ExternFn = "%extern"
    show (ForeignFn cs) = "%foreign " ++ showSep " " (map show cs)
    show Invertible = "%invertible"
    show (Totality Total) = "total"
    show (Totality CoveringOnly) = "covering"
    show (Totality PartialOK) = "partial"
    show Macro = "%macro"
    show (SpecArgs ns) = "%spec " ++ showSep " " (map show ns)

  public export
  data ImpTy : Type where
       MkImpTy : FC -> (n : Name) -> (ty : RawImp) -> ImpTy

  public export
  MkTy : FC -> (n : Name) -> (ty : RawImp) -> ImpTy
  MkTy = MkImpTy

  export
  Show ImpTy where
    show (MkImpTy fc n ty) = "(%claim " ++ show n ++ " " ++ show ty ++ ")"

  public export
  data DataOpt : Type where
       SearchBy : List Name -> DataOpt -- determining arguments
       NoHints : DataOpt -- Don't generate search hints for constructors
       UniqueSearch : DataOpt -- auto implicit search must check result is unique
       External : DataOpt -- implemented externally
       NoNewtype : DataOpt -- don't apply newtype optimisation

  public export
  data ImpData : Type where
       MkImpData : FC -> (n : Name) -> (tycon : RawImp) ->
                   (opts : List DataOpt) ->
                   (datacons : List ImpTy) -> ImpData
       MkImpLater : FC -> (n : Name) -> (tycon : RawImp) -> ImpData

  export
  Show ImpData where
    show (MkImpData fc n tycon _ cons)
        = "(%data " ++ show n ++ " " ++ show tycon ++ " " ++
           show cons ++ ")"
    show (MkImpLater fc n tycon)
        = "(%datadecl " ++ show n ++ " " ++ show tycon ++ ")"

  public export
  data IField : Type where
       MkIField : FC -> RigCount -> PiInfo RawImp -> Name -> RawImp ->
                  IField

  public export
  data ImpRecord : Type where
       MkImpRecord : FC -> (n : Name) ->
                     (params : List (Name, RigCount, PiInfo RawImp, RawImp)) ->
                     (conName : Name) ->
                     (fields : List IField) ->
                     ImpRecord

  public export
  MkRecord : FC -> (n : Name) ->
                     (params : List (Name, RigCount, PiInfo RawImp, RawImp)) ->
                     (conName : Name) ->
                     (fields : List IField) ->
                     ImpRecord
  MkRecord = MkImpRecord

  export
  Show IField where
    show (MkIField _ c Explicit n ty) = show n ++ " : " ++ show ty
    show (MkIField _ c _ n ty) = "{" ++ show n ++ " : " ++ show ty ++ "}"

  export
  Show ImpRecord where
    show (MkImpRecord _ n params con fields)
        = "record " ++ show n ++ " " ++ show params ++
          " " ++ show con ++ "\n\t" ++
          showSep "\n\t" (map show fields) ++ "\n"

  public export
  data WithFlag
         = Syntactic -- abstract syntactically, rather than by value

  public export
  data ImpClause : Type where
       PatClause : FC -> (lhs : RawImp) -> (rhs : RawImp) -> ImpClause
       WithClause : FC -> (lhs : RawImp) -> (wval : RawImp) ->
                    (flags : List WithFlag) ->
                    List ImpClause -> ImpClause
       ImpossibleClause : FC -> (lhs : RawImp) -> ImpClause

  export
  Show ImpClause where
    show (PatClause fc lhs rhs)
       = show lhs ++ " = " ++ show rhs
    show (WithClause fc lhs wval flags block)
       = show lhs ++ " with " ++ show wval ++ "\n\t" ++ show block
    show (ImpossibleClause fc lhs)
       = show lhs ++ " impossible"

  data NestedNames : List Name -> Type where [external]
  data Term : List Name -> Type where [external]
  data Env : (List Name -> Type) -> List Name -> Type where [external]
  data Core : Type -> Type where [external]

  public export
  data ImpDecl : Type where
       IClaim : FC -> RigCount -> Visibility -> List FnOpt ->
                ImpTy -> ImpDecl
       IData : FC -> Visibility -> ImpData -> ImpDecl
       IDef : FC -> Name -> List ImpClause -> ImpDecl
       IParameters : FC -> List (Name, RawImp) ->
                     List ImpDecl -> ImpDecl
       IRecord : FC ->
                 Maybe String -> -- nested namespace
                 Visibility -> ImpRecord -> ImpDecl
       INamespace : FC -> Namespace -> List ImpDecl -> ImpDecl
       ITransform : FC -> Name -> RawImp -> RawImp -> ImpDecl
       IRunElabDecl : FC -> RawImp -> ImpDecl
       IPragma : List Name -> -- pragmas might define names that wouldn't
                       -- otherwise be spotted in 'definedInBlock' so they
                       -- can be flagged here.
                 ({vars : _} ->
                  NestedNames vars -> Env Term vars -> Core ()) ->
                 ImpDecl
       ILog : Maybe (List String, Nat) -> ImpDecl

  public export
  Decl : Type
  Decl = ImpDecl

  export
  Show ImpDecl where
    show (IClaim _ _ _ opts ty) = show opts ++ " " ++ show ty
    show (IData _ _ d) = show d
    show (IDef _ n cs) = "(%def " ++ show n ++ " " ++ show cs ++ ")"
    show (IParameters _ ps ds)
        = "parameters " ++ show ps ++ "\n\t" ++
          showSep "\n\t" (assert_total $ map show ds)
    show (IRecord _ _ _ d) = show d
    show (INamespace _ ns decls)
        = "namespace " ++ show ns ++
          showSep "\n" (assert_total $ map show decls)
    show (ITransform _ n lhs rhs)
        = "%transform " ++ show n ++ " " ++ show lhs ++ " ==> " ++ show rhs
    show (IRunElabDecl _ tm)
        = "%runElab " ++ show tm
    show (IPragma _ _) = "[externally defined pragma]"
    show (ILog Nothing) = "%logging off"
    show (ILog (Just (topic, lvl))) = "%logging " ++ case topic of
      [] => show lvl
      _  => concat (intersperse "." topic) ++ " " ++ show lvl
