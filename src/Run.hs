{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE StrictData          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections       #-}
{-# LANGUAGE PatternGuards       #-}

module Run where

import           Control.Exception  ( Exception , throwIO  , try        )
import           Control.Monad      ((>=>)      , forM_                 )
import           Data.Bool          ( bool                              )
                                                                    
import           System.Environment ( getArgs                           )
import           System.IO          ( isEOF                             )
                                                 
import           Data.IORef         ( newIORef   , readIORef, writeIORef)
import qualified Data.Map       as    Map
import qualified Data.Text      as    T
import qualified Data.Text.IO   as    TIO

import           Syntax
import           Pretty             ( ppView     , ppConstE             )
import           Utils              

--------------------------------------------------------------------------------

newtype RuntimeError
  = RuntimeError String
  deriving Show

instance Exception RuntimeError

throwRuntimeErr :: String -> IO a
throwRuntimeErr = throwIO . RuntimeError

--------------------------------------------------------------------------------

erase :: Exp -> Erased
erase = \case
  EVar     i           -> XVar     i
  EGlobal  gnm         -> XGlobal  gnm
                        
  EConst   c           -> XConst   c
  EInt     n           -> XInt     n
  EDouble  d           -> XDouble  d
  EString  s           -> XString  s
                        
  EAnn     e _         -> erase    e
                        
  ELam     _ _   eBody -> XLam           (erase eBody)
  ETLam    _ _   eBody -> erase    eBody
                        
  EApp     e e'        -> XApp           (erase e) (erase e')
  ETApp    e _         -> erase    e     
                                         
  ELet     _ _ e eBody -> XLet           (erase e) (erase eBody)
                                         
  ERecord  flds        -> XRecord        (Map.map erase flds)
  EVariant lbl e       -> XVariant lbl   (erase e)
                                         
  EProj    e lbl       -> XProj          (erase e) lbl
  EMatch   e brs       -> XMatch         (erase e) (Map.map (erase . snd) brs)
                                         
  EPack    _ e         -> erase    e
  ERoll    _ e         -> erase    e     
  EUnpack  e _ _ eBody -> XLet           (erase e) (erase eBody)
  EUnroll  e           -> erase    e
                                         
  EFix     e           -> XFix           (erase e)
                                         
  EReturn  e           -> XReturn        (erase e)
  EBind    e e'        -> XBind          (erase e) (erase e')
                        
  EHole    _ _         -> internalErr "erase: Hole in executable term"
  ELoc     _ e         -> erase    e

--------------------------------------------------------------------------------

mkThunk  :: Erased -> Env -> IO Thunk
mkThunkV :: ValE          -> IO Thunk

mkThunk  e env = Thunk <$> newIORef (Unevaluated e env)
mkThunkV v     = Thunk <$> newIORef (Evaluated   v    )

--------------------------------------------------------------------------------

-- Consider: fix (λx. x)
-- erased:   XFix (XLam (XVar 0))

-- step glbT [] (XFix (XLam (XVar 0)))
-- Recurses on the inner function body, e ≔ XLam (XVar 0)

-- step glbT [] (XLam (XVar 0))
-- Returns a closure: v ≔ VClosureE (XVar 0) []

-- Back to XFix branch:
-- A new IORef is allocated to represent the function itself (recur)
-- ref = IORef Evaluating

--   apply glbT (VClosureE (XVar 0) []) (Thunk ref)
-- ⇒ step glbT [Thunk ref] (XVar 0)

-- Looks up index 0 in the environment, which is (Thunk ref)
-- Calls: force glbT (Thunk ref)

--   force glbT (Thunk ref)
-- ⇒ readIORef ref
-- ⇒ Evaluating
-- ⇒ throws RuntimeError "Simple infinite loop detected"

--------------------------------------------------------------------------------

-- Consider: fix (\x : Int. x + 1)
-- erased:   XFix (XLam (XApp (XApp (XConst EAdd) (XVar 0)) (XInt 1)))

-- step glbT [] (XFix (XLam …))
-- Recurses on the inner function body, e ≔ XLam (XApp (XApp (XConst EAdd) (XVar 0)) (XInt 1))

-- step glbT [] (XLam …)
-- Returns a closure: v ≔ VClosureE (XApp (XApp (XConst EAdd) (XVar 0)) (XInt 1)) []

-- Back to XFix branch:
-- A new IORef is allocated to represent the function itself:
-- ref = IORef Evaluating

--   apply glbT (VClosureE … []) (Thunk ref)
-- ⇒ step glbT [Thunk ref] (XApp (XApp (XConst EAdd) (XVar 0)) (XInt 1))

-- Evaluating the application chain resolves the primitive EAdd and its arguments.
-- The curried applications eventually trigger applyConst for EAdd:

-- applyConst glbT EAdd [Thunk ref, th]

-- where th is an unevaluated thunk for XInt 1

-- Inside applyConst for EAdd:

-- It must evaluate its arguments strictly to perform primitive math:

-- ⇒ binInt (+) (Thunk ref) th
-- ⇒ forceInt glbT (Thunk ref)
-- ⇒ force glbT (Thunk ref)
-- ⇒ readIORef ref
-- ⇒ Evaluating
-- ⇒ throws RuntimeError "Simple infinite loop detected"

--------------------------------------------------------------------------------

-- Productive case

-- Consider: (fix (λf. λn. f n)) 0
-- erased:   XApp (XFix (XLam (XLam (XApp (XVar 1) (XVar 0))))) (XInt 0)

-- step glbT [] (XApp …)
-- Evaluates the function: step glbT [] (XFix …)

-- step glbT [] (XFix (XLam (XLam …)))
-- Evaluates the inner function body.

-- step glbT [] (XLam (XLam …))
-- Returns: VClosureE (XLam (XApp (XVar 1) (XVar 0))) []

-- Back to XFix branch:
-- A new IORef is allocated
-- ref ≔ IORef Evaluating

--   apply glbT (VClosureE (XLam …) []) (Thunk ref)
-- ⇒ step glbT [Thunk ref] (XLam (XApp (XVar 1) (XVar 0)))
-- ⇒ VClosureE (XApp (XVar 1) (XVar 0)) [Thunk ref]

-- Back to XFix branch:
-- writeIORef ref (Evaluated (VClosureE (XApp …) [Thunk ref]))
-- ref is the whole evaluated closure here

-- Back to XApp:
-- The argument (XInt 0) is wrapped using mkThunk:
-- arg ≔ Thunk <$> newIORef (Unevaluated (XInt 0) [])

--   apply glbT (VClosureE (XApp (XVar 1) (XVar 0)) [Thunk ref]) arg
-- ⇒ step glbT [arg, Thunk ref] (XApp (XVar 1) (XVar 0))

-- Evaluation of the function applied: (XVar 1)

-- force glbT (env !! 1)
-- ⇒ readIORef ref
-- ⇒ Evaluated (VClosureE (XApp (XVar 1) (XVar 0)) [Thunk ref])

-- The function (XVar 1) successfully yields the closure itself.

-- The argument (XVar 0) is wrapped into a new thunk ref'.

--   apply glbT (VClosureE (XApp (XVar 1) (XVar 0)) [Thunk ref]) (Thunk ref')
-- ⇒ step glbT [Thunk ref', Thunk ref] (XApp (XVar 1) (XVar 0))

-- TODO: write an example with y combinator (without built-in fix)

force       :: GErased -> Thunk -> IO ValE
forceInt    :: GErased -> Thunk -> IO Integer
forceDouble :: GErased -> Thunk -> IO Double
forceString :: GErased -> Thunk -> IO T.Text

force glbT (Thunk ref) = readIORef ref >>= \case
  Evaluated   v     -> return          v
  Evaluating        -> throwRuntimeErr "Simple infinite loop detected" -- aka Haskell's <<loop>>
  Unevaluated e env -> do
      -- If it attempts to force the same thunk again during the execution of a step, it will read the Evaluating state.
      writeIORef ref  Evaluating   -- ref inside of thunk is mutable, and we ref := Evaluating
      v <- step glbT  env e        -- e here is Thunk ref (and ref is set above)
      writeIORef ref (Evaluated v)
      return v

forceInt    glbT e = force glbT e >>= \case { VInt    n -> return n; _ -> internalErr "forceInt: Expected Int"       }
forceDouble glbT e = force glbT e >>= \case { VDouble d -> return d; _ -> internalErr "forceDouble: Expected Double" }
forceString glbT e = force glbT e >>= \case { VString s -> return s; _ -> internalErr "forceString: Expected String" }

step :: GErased -> Env -> Erased -> IO ValE
step glbT env = \case
  XVar     i         -> force glbT (env      !!                                    unIx    i  )
  XGlobal  gnm       -> force glbT (lookupOrErr gnm glbT $ "Global not found: " ++ unGName gnm)
  
  XConst   EGetLine  -> return $ VIOAct    (IOStandalone IGetLine)
  XConst   EArgCount -> return $ VIOAct    (IOStandalone IArgCount)
  XConst   c         -> return $ VPartial   c            []
                                            
  XInt     n         -> return $ VInt       n
  XDouble  d         -> return $ VDouble    d
  XString  s         -> return $ VString    s
  
  XLam     eBody     -> return $ VClosureE  eBody env
  
  XApp     e e'      -> step glbT env e >>= \v  -> mkThunk e' env >>= apply glbT v
  XLet     e eBody   -> mkThunk e env   >>= \th -> step glbT (th : env) eBody
  
  XRecord  flds      -> VRecord      <$> traverse (`mkThunk` env) flds
  XProj    e lbl     -> step glbT env e >>= \case
                          VRecord   ths   -> maybe (internalErr $ "Projection of missing label " ++ unLabel lbl) (force glbT) (Map.lookup lbl ths)
                          _               -> internalErr "XProj: Expected record"
                          
  XVariant lbl e     -> VVariant lbl <$> mkThunk e env
  XMatch   e brs     -> step glbT env e >>= \case
                           VVariant lbl th -> maybe (internalErr $ "Missing branch for label " ++ unLabel lbl) (step glbT (th : env)) (Map.lookup lbl brs)
                           _               -> internalErr "XMatch: Expected variant"
                           
  XFix     e         -> step glbT env e >>= \v -> do
                          ref <- newIORef   Evaluating
                          res <- apply glbT v  (Thunk ref)
                          writeIORef   ref (Evaluated res)
                          return res
                          
  XReturn  e         -> VIOAct  . IOReturn <$> mkThunk e env
  XBind    e e'      -> VIOAct <$> (IOBind <$> mkThunk e env <*> mkThunk e' env)

apply :: GErased -> ValE -> Thunk -> IO ValE
apply glbT v thArg = case v of
  VClosureE eBody env -> step glbT (thArg : env) eBody
  VPartial  c     ths -> let ths' = ths  ++ [thArg] in
                         if length  ths' == arity c
                         then applyConst   glbT c ths'
                         else return $ VPartial c ths'
  _                   -> internalErr "apply: Expected function"
  where arity = \case
          { EPutStr     -> 1; EReadFile   -> 1; EWriteFile -> 2;
            EArgAt      -> 1;
            EAdd        -> 2; ESub        -> 2; EMul       -> 2;
            EAddD       -> 2; ESubD       -> 2; EMulD      -> 2; EDivD -> 2; ETrunc -> 1;
            EIntEq      -> 2; EStringEq   -> 2; EDoubleEq  -> 2;
            EConcat     -> 2; ESubstring  -> 3; ELength    -> 1;
            EShowInt    -> 1; EShowDouble -> 1;
            _           -> internalErr "arity: unreachable primitive" }

applyConst :: GErased -> ConstE -> EArgs -> IO ValE
applyConst glbT c args = case (c, args) of
  (EAdd,        [e, e'     ]) -> binInt    (+) e e'
  (ESub,        [e, e'     ]) -> binInt    (-) e e'
  (EMul,        [e, e'     ]) -> binInt    (*) e e'
  
  (EAddD,       [e, e'     ]) -> binDouble (+) e e'
  (ESubD,       [e, e'     ]) -> binDouble (-) e e'
  (EMulD,       [e, e'     ]) -> binDouble (*) e e'
  (EDivD,       [e, e'     ]) -> forceDouble glbT e >>= \d -> forceDouble glbT e' >>= \d' -> let res = d / d' in
                                 if isNaN res || isInfinite res
                                   then VVariant (Label "None") <$> mkThunkV (VRecord Map.empty)
                                   else VVariant (Label "Some") <$> mkThunkV (VDouble res)      
  (ETrunc,      [e         ]) -> forceDouble glbT e >>= \d -> return $ VInt $ if isNaN d || isInfinite d then 0 else truncate d
  
  (EIntEq,      [e, e'     ]) -> cmpInt    (==) e e'
  (EStringEq,   [e, e'     ]) -> cmpString (==) e e'
  (EDoubleEq,   [e, e'     ]) -> cmpDouble (==) e e'
  
  (EConcat,     [e, e'     ]) -> forceString glbT e >>= \s  -> forceString glbT e' >>= \s' -> return $ VString (T.append s s')
  (ESubstring,  [e, e', e'']) -> forceInt    glbT e >>= \st -> forceInt    glbT e' >>= \ln -> forceString glbT e'' >>= \s ->
                                 let n   = fromIntegral (T.length s) -- st = start, ln = length
                                     st' = max 0        (min   st n)
                                     ed  = min (st' + max 0 ln)   n
                                 in return $ VString (T.take (fromIntegral (ed - st')) (T.drop (fromIntegral st') s))
  (ELength,     [e         ]) -> VInt    . fromIntegral . T.length      <$> forceString glbT e
  (EShowInt,    [e         ]) -> VString .                T.pack . show <$> forceInt    glbT e
  (EShowDouble, [e         ]) -> VString .                T.pack . show <$> forceDouble glbT e
  
  (EPutStr,     [e         ]) -> return $ VIOAct (IOStandalone (IPutStr    e   ))
  (EReadFile,   [e         ]) -> return $ VIOAct (IOStandalone (IReadFile  e   ))
  (EWriteFile,  [e, e'     ]) -> return $ VIOAct (IOStandalone (IWriteFile e e'))
  (EArgAt,      [e         ]) -> return $ VIOAct (IOStandalone (IArgAt     e   ))
  
  _                             -> internalErr ("applyConst: unexpected arguments for " ++ ppConstE c)
  where binInt    op e e' = forceInt    glbT e >>= \v -> forceInt    glbT e' >>= \v' -> return $ VInt    (v `op` v') 
        binDouble op e e' = forceDouble glbT e >>= \v -> forceDouble glbT e' >>= \v' -> return $ VDouble (v `op` v')
        cmpInt    op e e' = forceInt    glbT e >>= \v -> forceInt    glbT e' >>= \v' -> mkBool           (v `op` v')
        cmpString op e e' = forceString glbT e >>= \v -> forceString glbT e' >>= \v' -> mkBool           (v `op` v')
        cmpDouble op e e' = forceDouble glbT e >>= \v -> forceDouble glbT e' >>= \v' -> mkBool           (v `op` v')
        mkBool       b    = VVariant (Label $ if b then "True" else "False") <$> mkThunkV (VRecord Map.empty)

--------------------------------------------------------------------------------

-- Consider: (A >>= B) >>= C
-- erased:   XBind (XBind A B) C
-- val:      VIOAct (IOBind (Thunk (Unevaluated (XBind A B) [])) (Thunk (Unevaluated C [])))

-- thL ≔ Thunk (Unevaluated (XBind A B) [])
-- thK ≔ Thunk (Unevaluated C [])

-- runIO glbT (VIOAct (IOBind thL thK))

-- Initial continuation stack ks ≔ []

--   stepIO [] (VIOAct (IOBind thL thK))
-- ⇒ through (IOBind thL thK) []
-- ⇒ force glbT thL

-- The inner bind is evaluated: VIOAct (IOBind thA thB)

-- Now stepIO processes this with ks ≔ [thK]

--   stepIO [thK] (VIOAct (IOBind thA thB))
-- ⇒ through (IOBind thA thB) [thK]

-- Pushes thB onto ks, and forces thA.

-- The stack ks is now [thB, thK] (i.e., [B, C]).

--   stepIO [thB, thK] (VIOAct actA)
-- ⇒ through actA [thB, thK]

-- If actA is a primitive (e. g. IOStandalone), it executes and produces a result.
-- The result is wrapped in a thunk res.

runIO :: GErased -> ValE -> IO ()
runIO glbT = stepIO []
  where stepIO ks = \case
          VIOAct next -> through next ks -- Is really an IO action
          _           -> internalErr "runIO: Expected IO action"

        through act ks = case act of
          IOReturn     th      -> continue th -- forwarding the value to be applied in next bind (if any)
          IOStandalone prim    -> executePrim glbT prim >>= \res -> case ks of
                                   [] -> return ()
                                   _  -> mkThunkV res >>= continue
          IOBind       thL thK -> force glbT thL >>= stepIO (thK : ks)
          where continue th = case ks of
                  []        -> return ()
                  (k : ks') -> force glbT k >>= \vk -> apply glbT vk th >>= stepIO ks'

executePrim :: GErased -> IOPrim -> IO ValE
executePrim glbT = \case
  IPutStr    th     -> forceString glbT th >>= TIO.putStr >> return (VRecord Map.empty)
  
  IGetLine          -> isEOF >>= bool 
                         (TIO.getLine >>= \s -> VVariant (Label "Some") <$> mkThunkV (VString s))
                         (VVariant (Label "None") <$> mkThunkV (VRecord Map.empty))

  IReadFile  th     -> forceString glbT th >>= \path ->                                      try (TIO.readFile (T.unpack path))          >>= \case
                         Left  (e :: IOError) -> VVariant (Label "Error") <$> mkThunkV (VString (T.pack (show e)))
                         Right s              -> VVariant (Label "Ok"   ) <$> mkThunkV (VString s)
  IWriteFile th th' -> forceString glbT th >>= \path -> forceString glbT th' >>= \content -> try (TIO.writeFile (T.unpack path) content) >>= \case
                         Left  (e :: IOError) -> VVariant (Label "Error") <$> mkThunkV (VString (T.pack (show e)))
                         Right ()             -> VVariant (Label "Ok"   ) <$> mkThunkV (VRecord Map.empty)
                         
  IArgCount         -> VInt . fromIntegral . length <$> getArgs
  IArgAt     th     -> forceInt glbT th >>= \n -> getArgs >>= \args ->
                         if n >= 0 && n < fromIntegral (length args) 
                           then VVariant (Label "Some") <$> mkThunkV (VString (T.pack (args !! fromIntegral n)))
                           else VVariant (Label "None") <$> mkThunkV (VRecord  Map.empty)

--------------------------------------------------------------------------------

takeView :: (Thunk -> IO ValE) -> Depth -> ValE -> IO View
takeView forceM d = \case
  _ | d <= 0                 -> return  VwOmitted
  VInt      n                -> return (VwInt    n)
  VDouble   x                -> return (VwDouble x)
  VString   s                -> return (VwString s)
  
  VClosureE e   env          -> VwClosure e   <$> mapM (viewTh d) env
  VPartial  c   as           -> VwPartial c   <$> mapM (viewTh d) as
  
  VRecord   flds             -> VwRecord      <$> mapM (\(lbl, th) -> (lbl,) <$> viewF d th) (Map.toList flds)
  VVariant  lbl th           -> VwVariant lbl <$> viewF d th
     
  VIOAct    io               -> case io of
      IOReturn      th       -> VwIOReturn    <$> viewF d th
      IOBind        thL thK  -> VwIOBind      <$> viewF d thL <*> viewF d thK
      IOStandalone  prim     -> case prim of
         IPutStr    th       -> VwIPutStr     <$> viewF d th
         IGetLine            -> return VwIGetLine
         IReadFile  th       -> VwIReadFile   <$> viewF d th
         IWriteFile th  thK  -> VwIWriteFile  <$> viewF d th  <*> viewF d thK
         IArgCount           -> return VwIArgCount
         IArgAt     th       -> VwIArgAt      <$> viewF d th
  where viewF  depth = forceM >=> takeView forceM (depth - 1)
        viewTh depth (Thunk ref)
           | depth <= 0 = return VwOmitted
           | otherwise  = readIORef ref >>= \case
               Evaluated   v            -> takeView forceM depth v
               Evaluating               -> return VwEvaluating
               Unevaluated e env
                 | XVar (Ix i) <- e, i >= 0 && i < length env -> viewTh (depth - 1) (env !! i)
                 | otherwise                                  -> return $ VwUneval e

--------------------------------------------------------------------------------

buildGlobals :: Program -> IO GErased
buildGlobals (Program decls) = 
  Map.fromList <$> mapM (\(gnm, e) ->     -- ref :: IORef ThunkState
    newIORef (Unevaluated (erase e) []) >>= \ref -> return (gnm, Thunk ref) -- Thunk wrapping
  ) (concatMap getFun decls) -- No need in type annotations
  where getFun = \case
          DLoc        _ d ->   getFun d
          DeclFun gnm _ e -> [(gnm,   e)]
          _               -> []
  
runProgram :: GErased -> GName -> IO ()
runProgram glbT mainNm = 
  maybe (throwRuntimeErr $ "Entry point '" ++ unGName mainNm ++ "' not found.")
        (force glbT >=> runIO glbT) -- forcing the found main function
        (Map.lookup mainNm glbT)

runExcs :: GErased -> ExcDecls -> IO ()
runExcs glbT excDecls =                         
  forM_ excDecls $ \e -> mkThunk (erase e) [] >>= force glbT >>= takeView (force glbT) 30 >>= putStrLn . (">> " ++) . ppView
