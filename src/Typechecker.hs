{-# LANGUAGE LambdaCase                 #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedRecordDot        #-}
{-# LANGUAGE FlexibleContexts           #-}

module Typechecker where

import           Control.Monad.Except
import           Control.Monad.Reader
import           Control.Monad.Writer
import           Control.Monad        ( when, unless, foldM )

import           Data.Functor         ((<&>), ($>)          )
import           Data.Bool            ( bool                )
import           Data.Foldable        ( forM_               )
import           Data.Map             ( Map                 ) 
import qualified Data.Map          as   Map

import           Syntax
import           Eval
import           Equiv
import           Pretty
import           Utils

--------------------------------------------------------------------------------

data Ctx
  = Ctx { ctxGlbT  :: GTypes    ,     
          ctxGlbK  :: GKinds    ,     
          ctxGlbET :: GTypes    ,     
          ctxKs    :: Kinds     ,      
          ctxTEnv  :: EnvT      , -- type environment       
          ctxETs   :: EnvT      , -- types of introduced variables
          ctxENms  :: Names     , 
          ctxTNms  :: Names     ,      
          ctxTLv   :: Lv        ,         
          ctxPos   :: Maybe Pos } 

type Report     = [String]
type TCResult a = (Either String a, Report)

newtype TC a = TC { unTC :: ReaderT Ctx (ExceptT String (Writer Report)) a }
  deriving (Functor, Applicative, Monad, MonadError String, MonadReader Ctx, MonadWriter Report)

instance MonadFail TC where
  fail msg = throwError $ "[Internal Error] Pattern match failure in TC do-block: " ++ msg

runTC :: Ctx -> TC a -> TCResult a
runTC ctx m = runWriter (runExceptT (runReaderT (unTC m) ctx))

emptyCtx :: Ctx
emptyCtx = Ctx Map.empty Map.empty Map.empty [] [] [] [] [] 0 Nothing

--------------------------------------------------------------------------------

throwErr :: String -> TC a
throwErr msg = asks ctxPos >>= maybe (throwError msg) (\(Pos f l c) -> throwError $ "\"" ++ f ++ "\" (line " ++ show l ++ ", column " ++ show c ++ "):\n" ++ msg)

withBind  :: LName -> ValT -> TC a -> TC a
withBindT :: LName -> Kind -> TC a -> TC a
-- on term level binders
withBind lnm v = local $ \ctx ->
  ctx { ctxETs  = v   : ctx.ctxETs,
        ctxENms = lnm : ctx.ctxENms }
-- on type level binders and Λ (which is not, eh, a type-level binder)
withBindT lnm k = local $ \ctx ->
  let   l        = ctx.ctxTLv in
  ctx { ctxKs    = k       : ctx.ctxKs,
        ctxTEnv  = fresh l : ctx.ctxTEnv,
        ctxTNms  = lnm     : ctx.ctxTNms,
        ctxTLv   = l + 1 }

lookupIdx    :: (Ctx ->           [a]) -> Ix    -> String -> TC a
lookupGlobal :: (Ctx -> Map GName  a ) -> GName -> String -> TC a

lookupIdx    sel (Ix   i) errMsg = asks sel >>= \env  -> if i >= 0 && i < length env then        return (env !! i) else       throwErr   errMsg
lookupGlobal sel     gnm  errMsg = asks sel >>= \dict -> case Map.lookup gnm dict of { Just v -> return  v;        Nothing -> throwErr $ errMsg ++ unGName gnm }

evalT' :: Type -> TC ValT
evalT' ty = asks $ \ctx -> evalT ctx.ctxGlbT ctx.ctxTEnv ty

isEquiv :: ValT -> ValT -> TC Bool
isEquiv v v' = asks $ \ctx -> equivT ctx.ctxGlbT ctx.ctxTLv v v'

headT :: ValT -> TC (Maybe (ConstT, [ValT]))
headT v = asks $ \ctx -> decomposeT ctx.ctxGlbT ctx.ctxTLv v

assertEquiv :: ValT -> ValT -> (Ctx -> String) -> TC ()
assertEquiv v v' mkErr = isEquiv v v' >>= \eqv -> unless eqv $ ask >>= throwErr . mkErr

requireAnn :: Maybe a -> String -> TC a
requireAnn ann errMsg = maybe (throwErr errMsg) return ann

mismatch :: ValT -> String -> String -> TC a
mismatch v sh msg = ask >>= \ctx -> throwErr $ "Expected " ++ sh ++ " type " ++ msg ++ ", got: " ++ ppClosed ctx v

expectForall  :: ValT -> String -> TC  (Kind,  ValT)
expectExists  :: ValT -> String -> TC  (Kind,  ValT)
expectArr     :: ValT -> String -> TC  (ValT,  ValT)
expectIO      :: ValT -> String -> TC   ValT
expectRecord  :: ValT -> String -> TC [(Label, ValT)]
expectVariant :: ValT -> String -> TC [(Label, ValT)]

expectArr     v msg = headT v >>= \case { Just (TArr,    [dom, cod]) -> return (dom, cod    ); _ -> mismatch v "arrow"       msg }
expectForall  v msg = headT v >>= \case { Just (TForall   k,  [f  ]) -> return (k,   f      ); _ -> mismatch v "forall"      msg }
expectExists  v msg = headT v >>= \case { Just (TExists   k,  [f  ]) -> return (k,   f      ); _ -> mismatch v "existential" msg }
expectIO      v msg = headT v >>= \case { Just (TIO,          [a  ]) -> return  a            ; _ -> mismatch v "IO"          msg }
expectRecord  v msg = headT v >>= \case { Just (TRecordC  ls,  args) -> return (zip  ls args); _ -> mismatch v "record"      msg }
expectVariant v msg = headT v >>= \case { Just (TVariantC ls,  args) -> return (zip  ls args); _ -> mismatch v "variant"     msg }

ppClosed :: Ctx -> ValT -> String
ppClosed ctx v =
  let d  =       ctx.ctxTLv
      nf = rbT   ctx.ctxGlbT d d v
  in       ppNfT ctx.ctxTNms 0 nf

reportHole :: HName -> Maybe Exp -> Maybe ValT -> TC ()
reportHole hnm me mvexp = ask >>= \ctx ->
  maybe (pure (Nothing, Nothing, False)) evalE me >>= \(mV, mErr, isOk) ->
        
  let ctxList = reverse (zipWith (\n k -> (unLName n, "∷", ppKind   0   k)) ctx.ctxTNms ctx.ctxKs ) ++
                reverse (zipWith (\n e -> (unLName n, ":", ppClosed ctx e)) ctx.ctxENms ctx.ctxETs)
      maxLen  = maximum (0 : map (\(n, _, _) -> length n) ctxList)
      ctxLns  = map (\(n, s, t) -> n ++ replicate (maxLen - length n + 1) ' ' ++ s ++ " " ++ t) ctxList
      
      gStr    = maybe "Given: _" (\v -> "Given: " ++ ppClosed ctx v) mV
      gLen    = length gStr
      mGiven  = me $> (gStr ++ bool "" " ✓" isOk)
      
      goalStr = maybe     "Goal: " (const "Goal:  ") mGiven ++ maybe "_" (ppClosed ctx) mvexp
      sepLine = replicate (maximum (length goalStr : maybe 0 (const gLen) mGiven : map length ctxLns)) '─' ++ "\n"
      
      ctxBlk  = bool     ("\nContext:\n\n" ++ unlines ctxLns ++ sepLine) ("\n" ++ sepLine) (null ctxList)
      givStr  = maybe "" (++        "\n"     ) mGiven
      errStr  = maybe "" ("\n\nError:\n"   ++) mErr
      
  in tell ["\nHole: ?" ++ unHName hnm ++ "\n" ++ ctxBlk ++ givStr ++ goalStr ++ errStr ++ "\n"]
  where isolate m      = asks  (`runTC` m)
        evalE   e      = maybe (inferE  e) (checkE e) mvexp
        inferE  e      = isolate (infer e) >>= \(res, r) ->
                           either (\err -> pure      (Nothing , Just err, False))
                                  (\vty -> tell r $> (Just vty, Nothing , False))
                                  res
        checkE e vtyGl = isolate (check e vtyGl) >>= \(res, r) ->
                           either (\errC -> isolate (infer e) >>= \(res', r') ->
                                      either (\_   -> pure       (Nothing , Just errC, False))
                                             (\vty -> isEquiv vty vtyGl >>= \ok ->
                                                      tell r' $> (Just vty, Just errC, ok   ))
                                             res')
                                  (\()   -> tell r $> (Just vtyGl, Nothing, True))
                                  res

--------------------------------------------------------------------------------

inferK :: Type -> TC Kind
inferK = \case
  TVar    i   -> lookupIdx    ctxKs   i   errUnboundTVar
  TGlobal gnm -> lookupGlobal ctxGlbK gnm errUnknownGlobalT
  
  TConst c -> return $ constKind c
  
  TLam lnm mk tyBody -> do
    k     <- requireAnn     mk   errUnannTLamKind
    bodyK <- withBindT  lnm  k $ inferK tyBody
    return (KArr k bodyK)
    
  TApp ty ty' -> do
    k <- inferK ty
    case k of { KArr kArg kRes -> checkK ty' kArg >> return kRes; _ -> throwErr errTAppMismatch }
      
  TMu  ty -> checkK ty (KArr KStar KStar) >> return KStar
  TMu' ty -> inferK ty >>= \case { KArr kArg kRes | kArg == kRes -> return kArg; _ -> throwErr errTMuIsoMismatch }
  
  TLoc p ty -> local (\ctx -> ctx { ctxPos = Just p }) (inferK ty)  
  where errUnboundTVar    = "Unbound type variable."
        errUnknownGlobalT = "Unknown global type: "
        errUnannTLamKind  = "Cannot infer kind for unannotated type-level lambda."
        errTAppMismatch   = "Type application evaluates onto a non-constructor."
        errTMuIsoMismatch = "Type application of μ′ requires a type of kind k → k."
        constKind         = \case
           TInt    -> KStar
           TDouble -> KStar
           TString -> KStar
           TArr    -> KArr KStar (KArr KStar KStar)
           
           TRecordC  lbls -> foldr KArr KStar (replicate (length lbls) KStar)
           TVariantC lbls -> foldr KArr KStar (replicate (length lbls) KStar)
           
           TForall k -> KArr (KArr k KStar) KStar
           TExists k -> KArr (KArr k KStar) KStar
           
           TIO -> KArr KStar KStar

checkK :: Type -> Kind -> TC ()
checkK ty kexp = case (ty, kexp) of
  (TLoc     p  ty'   ,               _) -> local (\ctx -> ctx { ctxPos = Just p }) (checkK ty' kexp)
  (TLam lnm mk tyBody,  KArr kDom kCod) -> do
    forM_         mk   $ \kAnn -> when (kAnn /= kDom) $ throwErr (errKAnn kAnn kDom)
    withBindT lnm kDom $ checkK tyBody kCod
  (TLam{},                           _) -> throwErr (errKLam kexp)
  _                                     -> inferK ty >>= \k -> when (k /= kexp) $ throwErr (errKMismatch k kexp)
  where errKAnn      kAnn kDom = "Kind mismatch in type lambda. " ++ ppKind 0 kAnn ++ " does not match expected kind " ++ ppKind 0 kDom
        errKLam      k         = "Expected kind "                 ++ ppKind 0 k    ++ " for type-level lambda, but type-level lambda requires an arrow kind."
        errKMismatch k    kex  = "Kind mismatch. Expected "       ++ ppKind 0 kex  ++ " but got "                      ++ ppKind 0 k

--------------------------------------------------------------------------------

infer :: Exp -> TC ValT
infer = \case
  EVar    i   -> lookupIdx    ctxETs   i   errUnboundVar
  EGlobal gnm -> lookupGlobal ctxGlbET gnm errUnknownGlobal
  EConst  c   -> evalT'      (constT       c)

  EInt    _ -> return vInt
  EDouble _ -> return vDouble
  EString _ -> return vString

  EAnn e ty -> do
    checkK ty KStar
    
    v <- evalT' ty
    
    check e v
    
    return v

  ELam lnm mTy eBody -> do
    ty <- requireAnn mTy errUnannLam
    
    checkK ty KStar
    
    vty   <- evalT' ty    
    vBody <- withBind lnm vty $ infer eBody
    
    return (vArr vty vBody)

  EApp e e' -> do
    vty              <- infer e
    (vtyDom, vtyCod) <- expectArr vty "in application"
    
    check e' vtyDom

    return vtyCod

  ETLam lnm mk eBody -> do
    k     <- requireAnn    mk  (errUnannTLam lnm)
    vBody <- withBindT lnm  k $ infer eBody
    
    asks $ \ctx ->
      let d      =       ctx.ctxTLv + 1
          nfBody = rbT   ctx.ctxGlbT d d vBody
          tyBody = nfToT               d nfBody
      in VNeu $ NeuApp (NeuConst (TForall k)) (VClosure lnm (Just k) tyBody ctx.ctxTEnv)

  ETApp e ty -> do
    v         <- infer e 
    (kexp, f) <- expectForall v "in type application"
    
    checkK ty kexp
    
    vt <- evalT' ty

    asks $ \ctx -> appT ctx.ctxGlbT f vt

  ELet lnm mTy eE eBody -> letI lnm mTy eE (infer eBody)

  ERecord flds -> do
    let lbls = Map.keys  flds                  -- lbl₁, lbl₂, …
        exps = Map.elems flds                  -- e₁,   e₂,   …
        rcrd = VNeu (NeuConst (TRecordC lbls)) -- *₁ →  *₂ →  …

    tys <- mapM infer exps                     -- τ₁,   τ₂,   …
    
    asks $ \ctx -> foldl (appT ctx.ctxGlbT) rcrd tys -- { lbl₁ : τ₁, … }

  EProj e lbl -> do
    v    <- infer e
    rcrd <- expectRecord v "for projection"
    
    case lookup lbl rcrd of
      Just    vt -> return    vt -- projected type from label
      Nothing    -> throwErr (errMissingLabel lbl)

  EMatch e brs -> do
    v    <- infer e
    vars <- expectVariant v "in pattern match"
    
    let brLbls = Map.keys  brs  -- Labels of pattern matching
        brExps = Map.elems brs  -- eᵢs of e ? (_ ↦ e₁, … )
        vrLbls = map fst   vars -- Labels of inferred variant
        vrTys  = map snd   vars -- τᵢs of < lbl₁ : τ₁, … >        
    
    when (brLbls /= vrLbls) $ throwErr errMatchLabels

    case zip vrTys brExps of
      []                           -> throwErr errEmptyMatch -- v ? ⟨⟩ is absurd and we are in inference mode
      ((vHd, (lnm, eBody)) : vtys) -> do                     -- Getting the first branch: lnm : τ ↦ eBody
        vBody <- withBind lnm vHd $ infer eBody -- eBody : σ
                                                -- other branches should have bodies of the same type σ
        forM_ vtys $ \(vI, (lnmI, eBodyI)) -> withBind lnmI vI $ check eBodyI vBody
        
        return vBody

  EFix e -> do
    v      <- infer     e
    (a, b) <- expectArr v "in fix"
    
    assertEquiv a b $ \ctx -> errFix ctx a b
    
    return a

  EReturn e -> infer e <&> vIO

  EBind e e' -> do
    vtyIO            <- infer     e                                            -- e  : IO vty
    vty              <- expectIO  vtyIO   "on left-hand side of bind"          --         vty
    vtyF             <- infer     e'                                           -- e' : vFDom -> IO vFCod
    (vFDom, vFCodIO) <- expectArr vtyF    "for right-hand side of bind"        --      vFDom    IO vFCod ≕ vFCodIO
    _                <- expectIO  vFCodIO "for right-hand side result of bind" -- Just checking that ^^^ is wrapped in IO
    
    assertEquiv vty vFDom (const errBind)
    
    return vFCodIO

  ERoll ty e -> do                                               
    checkK ty KStar                                                   -- ty ∷ *
    vty  <- evalT' ty                                                 
    vUnf <- asks (\ctx -> unrollIsoT ctx.ctxGlbT ctx.ctxTLv vty)      -- unrolls if vty is μ′ (Nothing overwise)
                                                                            
    maybe (throwErr errRoll) (\unf -> check e unf >> return vty) vUnf -- e : f (μ′ f) ⇒ roll [ty] e : μ′ f

  EUnroll e -> do                                                
    vty  <- infer e                                              -- e : vty
    vUnf <- asks (\ctx -> unrollIsoT ctx.ctxGlbT ctx.ctxTLv vty) -- unrolls if vty is μ′
    
    maybe (throwErr errUnroll) return vUnf                       -- unroll e : f (μ′ f)

  EHole hnm me -> do
    reportHole hnm me Nothing
    throwErr (errHoleInfer hnm)

  EPack{}    -> throwErr errPack
  EUnpack{}  -> throwErr errUnpack
  EVariant{} -> throwErr errVariant -- Like, if there is an expression ⟨A = 5⟩, the typechecker knows A is Int, but it has no idea what other labels belong to this variant
  
  ELoc p e -> local (\ctx -> ctx { ctxPos = Just p }) (infer e)
  where errUnboundVar            = "Unbound term variable."
        errUnknownGlobal         = "Unknown global term: "
        errUnannLam              = "Cannot infer the type for unannotated lambda."
        errUnannTLam    lnm      = "Cannot infer the type for unannotated type abstraction Λ" ++ unLName lnm
        errMissingLabel lbl      = "Record does not have label "                              ++ unLabel lbl 
        errMatchLabels           = "Pattern match branches do not match variant labels."
        errEmptyMatch            = "Cannot infer result type of empty match."
        errFix          ctx  a b = "Domain and codomain of fix must match, got " ++ ppClosed ctx a ++ " → " ++ ppClosed ctx b
        errBind                  = "Type mismatch in bind: left-hand side result does not match right-hand side argument."
        errHoleInfer    hnm      = "Hole ?" ++ unHName hnm ++ " in inference mode cannot proceed without an annotation."
        errPack                  = "Cannot infer the type for pack."
        errUnpack                = "Cannot infer the type for unpack."
        errVariant               = "Cannot infer the type for variant injection."
        errRoll                  = "Target type of roll must be an applied μ′ type."
        errUnroll                = "Argument of unroll must have an applied μ′ type."
        constT = \case
           EPutStr     -> tString                       ~> tIO     tUnit
           EGetLine    ->                                  tIO    (tOption tString)
           EReadFile   -> tString                       ~> tIO    (tResult tString)
           EWriteFile  -> tString ~> tString            ~> tIO    (tResult tUnit)
           EArgCount   ->                                  tIO     tInt
           EArgAt      -> tInt                          ~> tIO    (tOption tString)
           EAdd        -> tInt    ~> tInt               ~> tInt
           ESub        -> tInt    ~> tInt               ~> tInt
           EMul        -> tInt    ~> tInt               ~> tInt
           EAddD       -> tDouble ~> tDouble            ~> tDouble
           ESubD       -> tDouble ~> tDouble            ~> tDouble
           EMulD       -> tDouble ~> tDouble            ~> tDouble
           EDivD       -> tDouble ~> tDouble            ~> tOption tDouble
           ETrunc      -> tDouble                       ~> tInt
           EIntEq      -> tInt    ~> tInt               ~> tBool
           EStringEq   -> tString ~> tString            ~> tBool
           EDoubleEq   -> tDouble ~> tDouble            ~> tBool
           EConcat     -> tString ~> tString            ~> tString
           ESubstring  -> tInt    ~> tInt    ~> tString ~> tString
           ELength     -> tString                       ~> tInt
           EShowInt    -> tInt                          ~> tString
           EShowDouble -> tDouble                       ~> tString
           where tString   = TConst  TString
                 tInt      = TConst  TInt
                 tDouble   = TConst  TDouble
                 tUnit     = TConst (TRecordC [])
                 tBool     = TApp (TApp  (TConst (TVariantC [Label "False", Label "True"])) tUnit  ) tUnit
                 tOption   = TApp (TApp  (TConst (TVariantC [Label "None",  Label "Some"])) tUnit  )
                 tResult   = TApp (TApp  (TConst (TVariantC [Label "Error", Label "Ok"  ])) tString) -- Something Either-like
                 tIO       = TApp (TConst TIO)
                 a ~> b    = TApp (TApp  (TConst  TArr) a) b
                 infixr 4 ~>

check :: Exp -> ValT -> TC ()
check e vtyExp = case e of
  ELoc p e' -> local (\ctx -> ctx { ctxPos = Just p }) (check e' vtyExp)

  ELam lnm mTy eBody -> do
    (vtyDom, vtyCod) <- expectArr vtyExp "for lambda"
    
    forM_ mTy $ \tyAnn -> do
      checkK tyAnn KStar
      
      vtyAnn <- evalT' tyAnn
      
      assertEquiv vtyAnn vtyDom $ \ctx -> errLamAnn ctx vtyAnn vtyDom
      
    withBind lnm vtyDom $ check eBody vtyCod

  ETLam lnm mk eBody -> do
    (k, vtyF) <- expectForall vtyExp "in type abstraction"

    forM_ mk $ \kAnn -> when (kAnn /= k) $ throwErr (errTyLamAnn kAnn k)
      
    ctx <- ask
    withBindT lnm k $ check eBody (appT ctx.ctxGlbT vtyF (fresh ctx.ctxTLv))

  ELet lnm mTy eE eBody -> letI lnm mTy eE (check eBody vtyExp)

  ERecord flds -> do
    vtyRcrd <- expectRecord vtyExp "for record"
    
    let fldsLbls = Map.keys  flds
        fldsExps = Map.elems flds
        rcrdLbls = map fst   vtyRcrd
        rcrdTys  = map snd   vtyRcrd
    
    when (fldsLbls /= rcrdLbls) $ throwErr errRecordLabelsMismatch
    
    forM_ (zip fldsExps rcrdTys) $ uncurry check -- e₁ : τ₁, …

  EVariant lbl eBody -> do
    vtyVars <- expectVariant vtyExp "for variant injection"
    
    case lookup lbl vtyVars of
      Just vty -> check eBody vty
      Nothing  -> throwErr (errVariantLabelMissing lbl)

  EMatch e' brs -> do
    vty     <- infer e'
    vtyVars <- expectVariant vty "in pattern match"
    
    let brLbls = Map.keys  brs     -- Labels of pattern matching
        brExps = Map.elems brs     -- eᵢs of e' ? (_ ↦ e₁, … )
        vrLbls = map fst   vtyVars -- Labels of inferred variant
        vrTys  = map snd   vtyVars -- τᵢs of < lbl₁ : τ₁, … >

    when (brLbls /= vrLbls) $ throwErr errMatchLabels -- for pattern matching branches = labels, obviously
                                                      -- Checking the p. matching expression against vtyExp
    forM_ (zip vrTys brExps) $ \(vI, (lnmI, eBody)) -> withBind lnmI vI $ check eBody vtyExp 

  EPack ty eBody -> do
    (k, vtyF) <- expectExists vtyExp "in pack"
    
    checkK ty k
    vty <- evalT' ty
    
    ctx <- ask
    check eBody (appT ctx.ctxGlbT vtyF vty)

  EUnpack e' lnmT lnmE eBody -> do
    vty       <- infer e'
    (k, vtyF) <- expectExists vty "in unpack"
    
    ctx <- ask
    
    withBindT lnmT k $ withBind lnmE (appT ctx.ctxGlbT vtyF (fresh ctx.ctxTLv)) $ check eBody vtyExp

  EFix e' -> check e' $ vArr vtyExp vtyExp

  EReturn e' -> expectIO vtyExp "in return" >>= check e'

  EBind e' e'' -> do
    _     <- expectIO vtyExp "in bind"      
    vty'  <- infer e'                       
    v''   <- expectIO vty' "on left-hand side of bind"
    
    check e'' (vArr v'' vtyExp)

  EHole hnm me -> reportHole hnm me (Just vtyExp)

  e' -> infer e' >>= \v -> assertEquiv v vtyExp (`errMismatch` v)
  where errLamAnn                  ctx  v tdom = "Type annotation on lambda (" ++ ppClosed ctx v ++ ") does not match expected domain type (" ++ ppClosed ctx tdom ++ ")"
        errTyLamAnn                kAnn k      = "Kind mismatch in type abstraction: annotated kind " ++ ppKind 0 kAnn ++ " does not match expected kind " ++ ppKind 0 k
        errRecordLabelsMismatch                = "Record fields do not match vtyExp type labels."
        errVariantLabelMissing     lbl         = "Variant label " ++ unLabel lbl ++ " not found in vtyExp type."
        errMatchLabels                         = "Pattern match branches do not match variant labels."
        errMismatch                ctx  v      = "Type mismatch: expected " ++ ppClosed ctx vtyExp ++ " but got " ++ ppClosed ctx v

vArr :: ValT -> ValT -> ValT
vIO  :: ValT         -> ValT

vArr a b = VNeu (NeuApp (NeuApp (NeuConst TArr) a) b)
vIO  a   = VNeu (NeuApp         (NeuConst TIO)  a)

vInt, vDouble, vString :: ValT

vInt    = VNeu (NeuConst TInt)
vDouble = VNeu (NeuConst TDouble)
vString = VNeu (NeuConst TString)

letI :: LName -> Maybe Type -> Exp -> TC a -> TC a
letI lnm mTy e cont = maybe (infer e) checkAnn mTy >>= \v -> withBind lnm v cont
  where checkAnn ty = checkK ty KStar >> evalT' ty >>= \v -> check e v >> return v

--------------------------------------------------------------------------------

checkDecl :: Ctx -> Decl -> TCResult Ctx
checkDecl ctx decl = runTC ctx (checkD decl)
  where checkD = \case
          DLoc         p d  -> local (\c -> c { ctxPos = Just p }) (checkD d)
          DeclType gnm k ty -> do
            guardFresh gnm ctxGlbK "type"
            checkK ty k
            
            v <- evalT' ty
            
            asks $ \c -> c { ctxGlbT = Map.insert gnm v c.ctxGlbT,
                             ctxGlbK = Map.insert gnm k c.ctxGlbK,
                             ctxPos  = Nothing }
                             
          DeclFun gnm ty e -> do
            guardFresh gnm ctxGlbET "function"
            checkK ty KStar
            
            v <- evalT' ty
            
            check e v
            
            asks $ \c -> c { ctxGlbET = Map.insert gnm v c.ctxGlbET,
                             ctxPos   = Nothing }
            
          DeclExc e -> infer e >> asks (\c -> c { ctxPos = Nothing })
          
        guardFresh gnm sel kind = asks sel >>= \dict ->
          when (Map.member gnm dict) $ throwErr $ "Duplicate " ++ kind ++ " definition: " ++ unGName gnm
     
checkProgram :: Program -> TCResult Ctx
checkProgram (Program decls) =
  runWriter $ runExceptT $ foldM step emptyCtx decls 
  where step       ctx d     = let (res, r) = checkDecl ctx d in tell r *> either (throwError . declErrMsg d) return res
        declErrMsg     d err = "Error in declaration " ++ declName d ++ ":\n" ++ err
          where declName     = \case { DLoc _ d' -> declName d'; DeclType (GName n) _ _ -> n; DeclFun (GName n) _ _ -> n; DeclExc _ -> ">> evaluation" }
