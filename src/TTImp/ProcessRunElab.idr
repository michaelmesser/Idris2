module TTImp.ProcessRunElab

import Core.Context
import Core.Core
import Core.Env
import Core.Metadata
import Core.Options
import Core.Normalise
import Core.Reflect
import Core.UnifyState
import Core.Value

import TTImp.Elab
import TTImp.Elab.Check
import TTImp.Elab.RunElab
import TTImp.TTImp
import Compiler.Scheme.Chez
import Compiler.Inline

%default covering

export
processRunElab : {vars : _} ->
                 {auto c : Ref Ctxt Defs} ->
                 {auto m : Ref MD Metadata} ->
                 {auto u : Ref UST UState} ->
                 List ElabOpt -> NestedNames vars -> Env Term vars -> FC ->
                 RawImp -> Core ()
processRunElab eopts nest env fc tm
    = do defs <- get Ctxt
         unless (isExtension ElabReflection defs) $
             throw (GenericMsg fc "%language ElabReflection not enabled")
         tidx <- resolveName (UN "[elaborator script]")
         let n = NS reflectionNS (UN "Elab")
         unit <- getCon fc defs (builtin "Unit")
         exp <- appCon fc defs n [unit]
         stm <- checkTerm tidx InExpr eopts nest env tm (gnf env exp)
         compileAndInlineAll
         elab <- myEval (abstractEnv fc env stm) (Elab ())
         runElab fc env Nothing elab
         --elabScript fc nest env !(nfOpts withAll defs env stm) Nothing
         pure ()
