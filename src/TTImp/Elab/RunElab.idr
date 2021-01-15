module TTImp.Elab.RunElab

import Core.Context
import Core.Context.Log
import Core.Core
import Core.Env
import Core.GetType
import Core.Metadata
import Core.Normalise
import Core.Options
import Core.Reflect
import Core.Unify
import Core.TT
import Core.Value

import TTImp.Elab.Check
import TTImp.Elab.Delayed
import TTImp.Reflect
import TTImp.TTImp
import TTImp.Unelab
import TTImp.Utils
import Compiler.Scheme.Chez
import Compiler.Inline

export
data Elab : Type -> Type where
     Pure : a -> Elab a
     RunIO : (1 _ : IO a) -> Elab a
     Bind : Elab a -> (a -> Elab b) -> Elab b
     Fail : String -> Elab a

     LogMsg : String -> Nat -> String -> Elab ()
     LogTerm : String -> Nat -> String -> RawImp -> Elab ()

     -- Elaborate a RawImp term to a concrete value
     -- Check : {expected : Type} -> RawImp -> Elab expected
     -- Quote a concrete expression back to a RawImp
     -- Quote : val -> Elab RawImp

     -- Elaborate under a lambda
     --Lambda : (0 x : Type) ->
     --         {0 ty : x -> Type} ->
     --         ((val : x) -> Elab (ty val)) -> Elab ((val : x) -> (ty val))

     -- Get the current goal type, if known
     -- (it might need to be inferred from the solution)
     Goal : Elab (Maybe RawImp)
     -- Get the names of local variables in scope
     LocalVars : Elab (List Name)
     -- Generate a new unique name, based on the given string
     GenSym : String -> Elab Name
     -- Put a name in the current namespace
     InCurrentNS : Name -> Elab Name
     -- Get the types of every name which matches.
     -- There may be ambiguities - returns a list of fully explicit names
     -- and their types. If there's no results, the name is undefined.
     GetType : Name -> Elab (List (Name, RawImp))
     -- Get the type of a local variable
     GetLocalType : Name -> Elab RawImp
     -- Get the constructors of a data type. The name must be fully resolved.
     GetCons : Name -> Elab (List Name)
     -- Check a group of top level declarations
     Declare : List ImpDecl -> Elab ()

export
runElab : {vars : _} ->
          {auto c : Ref Ctxt Defs} ->
          {auto m : Ref MD Metadata} ->
          {auto u : Ref UST UState} ->
          FC ->
          Env Term vars ->
          Maybe (Glued vars) ->
          Elab a ->
          Core a
runElab _ _ _ (Pure val) = pure val
runElab _ _ _ (RunIO act) = coreLift act
runElab fc env exp (Bind x f) = runElab fc env exp x >>= (runElab fc env exp . f)
runElab fc _ _ (Fail msg) = throw (GenericMsg fc ("Error during reflection: " ++ msg))
runElab _ _ _ (LogMsg topic verb str) = logC topic verb (pure str)
runElab _ _ _ (LogTerm topic verb str tm) = logC topic verb $ pure $ str ++ ": " ++ show tm
--runElab fc _ _ (Check _) = throw (GenericMsg fc "Check not available")
--runElab fc _ _ (Quote _) = throw (GenericMsg fc "Quote not available")
--runElab fc _ _ (Lambda _ _) = throw (GenericMsg fc "Lambda not available")
runElab _ env exp Goal = do
    let Just gty = exp | Nothing => pure Nothing
    ty <- getTerm gty
    pure $ Just $ !(unelabUniqueBinders env ty)
runElab _ _ _ LocalVars = pure vars
runElab _ _ _ (GenSym str) = genVarName str
runElab _ _ _ (InCurrentNS n) = inCurrentNS n
runElab _ _ _ (GetType n) = do
    defs <- get Ctxt
    res <- lookupTyName n (gamma defs)
    traverse unelabType res
    where
        unelabType : (Name, Int, ClosedTerm) -> Core (Name, RawImp)
        unelabType (n, _, ty) = pure (n, !(unelabUniqueBinders [] ty))
runElab fc env _ (GetLocalType n) = do
    case defined n env of
        Just (MkIsDefined rigb lv) => do
            let binder = getBinder lv env
            let bty = binderType binder
            unelabUniqueBinders env bty
        _ => throw (GenericMsg fc (show n ++ " is not a local variable"))
runElab fc _ _ (GetCons cn) = do
    defs <- get Ctxt
    Just (TCon _ _ _ _ _ _ cons _) <- lookupDefExact cn (gamma defs)
        | _ => throw (GenericMsg fc (show cn ++ " is not a type"))
    pure cons
runElab _ _ _ (Declare decls) = traverse_ (processDecl [] (MkNested []) []) decls

{-
export
elabScript : {vars : _} ->
             {auto c : Ref Ctxt Defs} ->
             {auto m : Ref MD Metadata} ->
             {auto u : Ref UST UState} ->
             FC -> NestedNames vars ->
             Env Term vars -> NF vars -> Maybe (Glued vars) ->
             Core (NF vars)
elabScript fc nest env (NDCon nfc nm t ar args) exp
    = do defs <- get Ctxt
         fnm <- toFullNames nm
         case fnm of
              NS ns (UN n)
                 => if ns == reflectionNS then elabCon defs n args else failWith defs
              _ => failWith defs
  where
    failWith : Defs -> Core a
    failWith defs
      = do defs <- get Ctxt
           empty <- clearDefs defs
           throw (BadRunElab fc env !(quote empty env (NDCon nfc nm t ar args)))

    scriptRet : Reflect a => a -> Core (NF vars)
    scriptRet tm
        = do defs <- get Ctxt
             nfOpts withAll defs env !(reflect fc defs False env tm)

    elabCon : Defs -> String -> List (Closure vars) -> Core (NF vars)
    elabCon defs "Pure" [_,val]
        = do empty <- clearDefs defs
             evalClosure empty val
    elabCon defs "Bind" [_,_,act,k]
        = do act' <- elabScript fc nest env
                                !(evalClosure defs act) exp
             case !(evalClosure defs k) of
                  NBind _ x (Lam _ _ _ _) sc =>
                      elabScript fc nest env
                              !(sc defs (toClosure withAll env
                                              !(quote defs env act'))) exp
                  _ => failWith defs
    elabCon defs "Fail" [_,msg]
        = do msg' <- evalClosure defs msg
             throw (GenericMsg fc ("Error during reflection: " ++
                                      !(reify defs msg')))
    elabCon defs "LogMsg" [topic, verb, str]
        = do topic' <- evalClosure defs topic
             verb' <- evalClosure defs verb
             logC !(reify defs topic') !(reify defs verb') $
                  do str' <- evalClosure defs str
                     reify defs str'
             scriptRet ()
    elabCon defs "LogTerm" [topic, verb, str, tm]
        = do topic' <- evalClosure defs topic
             verb' <- evalClosure defs verb
             logC !(reify defs topic') !(reify defs verb') $
                  do str' <- evalClosure defs str
                     tm' <- evalClosure defs tm
                     pure $ !(reify defs str') ++ ": " ++
                             show (the RawImp !(reify defs tm'))
             scriptRet ()
    elabCon defs "Check" [exp, ttimp]
        = do exp' <- evalClosure defs exp
             ttimp' <- evalClosure defs ttimp
             tidx <- resolveName (UN "[elaborator script]")
             e <- newRef EST (initEState tidx env)
             (checktm, _) <- runDelays 0 $
                     check top (initElabInfo InExpr) nest env !(reify defs ttimp')
                           (Just (glueBack defs env exp'))
             empty <- clearDefs defs
             nf empty env checktm
    elabCon defs "Quote" [exp, tm]
        = do tm' <- evalClosure defs tm
             defs <- get Ctxt
             empty <- clearDefs defs
             scriptRet !(unelabUniqueBinders env !(quote empty env tm'))
    elabCon defs "Lambda" [x, _, scope]
        = do empty <- clearDefs defs
             NBind bfc x (Lam fc' c p ty) sc <- evalClosure defs scope
                   | _ => throw (GenericMsg fc "Not a lambda")
             n <- genVarName "x"
             sc' <- sc defs (toClosure withAll env (Ref bfc Bound n))
             qsc <- quote empty env sc'
             let lamsc = refToLocal n x qsc
             qp <- quotePi p
             qty <- quote empty env ty
             let env' = Lam fc' c qp qty :: env

             runsc <- elabScript fc (weaken nest) env'
                                 !(nf defs env' lamsc) Nothing -- (map weaken exp)
             nf empty env (Bind bfc x (Lam fc' c qp qty) !(quote empty env' runsc))
       where
         quotePi : PiInfo (NF vars) -> Core (PiInfo (Term vars))
         quotePi Explicit = pure Explicit
         quotePi Implicit = pure Implicit
         quotePi AutoImplicit = pure AutoImplicit
         quotePi (DefImplicit t) = throw (GenericMsg fc "Can't add default lambda")
    elabCon defs "Goal" []
        = do let Just gty = exp
                 | Nothing => nfOpts withAll defs env
                                     !(reflect fc defs False env (the (Maybe RawImp) Nothing))
             ty <- getTerm gty
             scriptRet (Just !(unelabUniqueBinders env ty))
    elabCon defs "LocalVars" []
        = scriptRet vars
    elabCon defs "GenSym" [str]
        = do str' <- evalClosure defs str
             n <- genVarName !(reify defs str')
             scriptRet n
    elabCon defs "InCurrentNS" [n]
        = do n' <- evalClosure defs n
             nsn <- inCurrentNS !(reify defs n')
             scriptRet nsn
    elabCon defs "GetType" [n]
        = do n' <- evalClosure defs n
             res <- lookupTyName !(reify defs n') (gamma defs)
             scriptRet !(traverse unelabType res)
      where
        unelabType : (Name, Int, ClosedTerm) -> Core (Name, RawImp)
        unelabType (n, _, ty)
            = pure (n, !(unelabUniqueBinders [] ty))
    elabCon defs "GetLocalType" [n]
        = do n' <- evalClosure defs n
             n <- reify defs n'
             case defined n env of
                  Just (MkIsDefined rigb lv) =>
                       do let binder = getBinder lv env
                          let bty = binderType binder
                          scriptRet !(unelabUniqueBinders env bty)
                  _ => throw (GenericMsg fc (show n ++ " is not a local variable"))
    elabCon defs "GetCons" [n]
        = do n' <- evalClosure defs n
             cn <- reify defs n'
             Just (TCon _ _ _ _ _ _ cons _) <-
                     lookupDefExact cn (gamma defs)
                 | _ => throw (GenericMsg fc (show cn ++ " is not a type"))
             scriptRet cons
    elabCon defs "Declare" [d]
        = do d' <- evalClosure defs d
             decls <- reify defs d'
             traverse_ (processDecl [] (MkNested []) []) decls
             scriptRet ()
    elabCon defs n args = failWith defs
elabScript fc nest env script exp
    = do defs <- get Ctxt
         empty <- clearDefs defs
         throw (BadRunElab fc env !(quote empty env script))
-}

export
checkTermL : {vars : _} ->
            {auto c : Ref Ctxt Defs} ->
            {auto m : Ref MD Metadata} ->
            {auto u : Ref UST UState} ->
            Int -> ElabMode -> List ElabOpt ->
            NestedNames vars -> Env Term vars ->
            RawImp -> Glued vars ->
            Core (Term vars)

export
checkRunElab : {vars : _} ->
               {auto c : Ref Ctxt Defs} ->
               {auto m : Ref MD Metadata} ->
               {auto u : Ref UST UState} ->
               {auto e : Ref EST (EState vars)} ->
               RigCount -> ElabInfo ->
               NestedNames vars -> Env Term vars ->
               FC -> RawImp -> Maybe (Glued vars) ->
               Core (Term vars, Glued vars)
checkRunElab rig elabinfo nest env fc script exp
    = do expected <- mkExpected exp
         defs <- get Ctxt
         unless (isExtension ElabReflection defs) $
             throw (GenericMsg fc "%language ElabReflection not enabled")
         let n = NS reflectionNS (UN "Elab")
         ttn <- getCon {vars=[]} fc defs (NS reflectionTTImpNS (UN "TTImp"))
         elabtt <- appCon {vars=[]} fc defs n [ttn]
         --(stm, sty) <- runDelays 0 $
         --                  check rig elabinfo nest env script (Just (gnf env elabtt))
         tidx <- resolveName (UN "[elaborator script]")
         stm <- checkTermL {vars=[]} tidx InExpr [] (MkNested []) [] script (gnf {vars=[]} [] elabtt)
         defs <- get Ctxt -- checking might have resolved some holes
         compileAndInlineAll
         elab <- myEval stm (Elab RawImp) -- abstract env
         ttimp <- runElab fc env (Just (gnf env expected)) elab
         check rig elabinfo nest env ttimp (Just (gnf env expected))
         --ntm <- elabScript fc nest env
         --                  !(nfOpts withAll defs env stm) (Just (gnf env expected))
         --defs <- get Ctxt -- might have updated as part of the script
         --empty <- clearDefs defs
         --pure (!(quote empty env ntm), gnf env expected)
  where
    mkExpected : Maybe (Glued vars) -> Core (Term vars)
    mkExpected (Just ty) = pure !(getTerm ty)
    mkExpected Nothing
        = do nm <- genName "scriptTy"
             metaVar fc erased env nm (TType fc)
