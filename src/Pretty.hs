{-# LANGUAGE LambdaCase      #-}
{-# LANGUAGE PatternGuards   #-}
{-# LANGUAGE RecordWildCards #-}

module Pretty where

import           Control.Monad.Reader
import           Data.Bool            ( bool        )
import           Data.List            ( intercalate )
import qualified Data.Map          as   Map
import qualified Data.Text         as   T

import           Syntax
import           Utils  

--------------------------------------------------------------------------------

type Prec = Int

precApp, precArr, precTApp, precAppExp, precBind :: Prec

precTApp   = 11
precApp    = 10
precAppExp = 10
precArr    = 4
precBind   = 1

parensIf :: Bool -> String -> String
parensIf cond s = bool s ("(" ++ s ++ ")") cond

cDepth :: Int -> String -> String
cDepth d s = "\ESC[" ++ show (31 + (d `mod` 5)) ++ "m" ++ s ++ "\ESC[0m"

nameSuffixes :: [String]
nameSuffixes = "" : "′" : "″" : "‴" : map show [(1 :: Int)..]

freshNm :: String -> Names -> String 
freshNm base nms = findFresh nameSuffixes
  where findFresh = \case
          s : ss -> let lnm = base ++ s in bool (findFresh ss) lnm (LName lnm `notElem` nms)
          []     -> base

checkBounds :: String -> Names -> String -> Int -> Int -> String
checkBounds err nms kind orig i =
  bool (internalErr $ "Out of bounds " ++ err ++ " " ++ kind ++ ": " ++ show orig)
       (unLName (nms !! i))
       (i >= 0 && i < length nms)

idxNameErr :: String -> Names -> Ix -> String
lvlNameErr :: String -> Names -> Lv -> String

idxNameErr err nms (Ix i) = checkBounds err nms "index" i  i
lvlNameErr err nms (Lv l) = checkBounds err nms "level" l (length nms - 1 - l)

idxNmT :: Names -> Ix -> String
lvlNmT :: Names -> Lv -> String

idxNmT = idxNameErr "type"
lvlNmT = lvlNameErr "free neutral type"

--------------------------------------------------------------------------------

data PPEnv = PPEnv
  { envTNms  :: Names,
    envPrec  :: Prec ,
    envDepth :: Int  }

type PP = Reader PPEnv

runPP :: PPEnv -> PP a -> a
runPP = flip runReader

withPrec :: Prec -> PP a -> PP a
withPrec p = local (\e -> e { envPrec = p })

withDepthUp :: PP a -> PP a
withDepthUp = local (\e -> e { envDepth = envDepth e + 1 })

withNm :: (PPEnv -> Names) -> (Names -> PPEnv -> PPEnv) -> String -> (String -> PP a) -> PP a
withNm getN setN base f = asks getN >>= \nms -> let l = freshNm base nms in local (setN (LName l : nms)) (f l)

withTNm :: String -> (String -> PP a) -> PP a
withTNm = withNm envTNms (\ns e -> e { envTNms = ns })

withBinder :: (String -> (String -> PP String) -> PP String) -> String -> (String -> PP String) -> PP String -> PP String
withBinder withNmF base mkPrefixM bodyM = 
  ask >>= \PPEnv{..} -> withNmF base $ \nm' -> 
    (\pref body -> parensIf (envPrec > 0) (pref ++ body)) <$> mkPrefixM nm' <*> withPrec 0 bodyM

--------------------------------------------------------------------------------

type BindsT       = [( String , Kind)]
type QuantGroups  = [([String], Kind)]

type Collected  a =       (BindsT, Names,        a)
type Quantifier a = Maybe (Quant , Kind , LName, a)

data Quant
  = QForall
  | QExists
  deriving Eq

unLoc :: Type -> Type
unLoc = \case { TLoc _ t -> unLoc t; t -> t }

isQuant   :: Type -> Quantifier Type
isQuantNf :: NfT  -> Quantifier NfT

isQuant t = case unLoc t of
  TApp op arg -> case (unLoc op, unLoc arg) of
    (TConst (TForall k), TLam lnm _ body) -> Just (QForall, k, lnm, body)
    (TConst (TExists k), TLam lnm _ body) -> Just (QExists, k, lnm, body)
    _                                     -> Nothing
  _                                       -> Nothing

isQuantNf = \case
  NfNeu (NfNeuApp op arg) -> case (op, arg) of
    (NfNeuConst (TForall k), NfLam lnm _ body) -> Just (QForall, k, lnm, body)
    (NfNeuConst (TExists k), NfLam lnm _ body) -> Just (QExists, k, lnm, body)
    _                                          -> Nothing
  _                                            -> Nothing

collectQGen :: (a -> Quantifier a) -> Quant -> Names -> a -> Collected a
collectQGen isQ q tNms t = case isQ t of
  Just (q', k, LName l, body) | q == q' ->
    let lnm'                  = freshNm l tNms
        (binds, tNms', inner) = collectQGen isQ q (LName lnm' : tNms) body
    in  ((lnm', k) : binds, tNms', inner)
  _                                     -> ([], tNms, t)

collectQ   :: Quant -> Names -> Type -> Collected Type
collectQNf :: Quant -> Names -> NfT  -> Collected NfT

collectQ   = collectQGen isQuant
collectQNf = collectQGen isQuantNf

groupBinds :: BindsT -> QuantGroups
groupBinds = foldr groupStep []
  where groupStep (n, k) = \case
          []                          -> [([n]    , k)]
          (ns, k') : rest | k == k'   -> (  n : ns, k)            : rest
                          | otherwise -> ( [n]    , k) : (ns, k') : rest

--------------------------------------------------------------------------------

fmtPrefixM, fmtPostfixM, fmtAppM :: Prec -> PP String -> PP String -> PP String
fmtBinOpM                        :: Prec -> String    -> PP String -> PP String -> PP String

fmtPrefixM  appP mPre m    = ask >>= \PPEnv{..} -> parensIf (envPrec > appP) <$> ((++)                                     <$> mPre <*> m   )
fmtPostfixM appP mSuf m    = ask >>= \PPEnv{..} -> parensIf (envPrec > appP) <$> ((++)                                     <$> m    <*> mSuf)
fmtAppM     appP      m m' = ask >>= \PPEnv{..} -> parensIf (envPrec > appP) <$> ((\s s' -> s ++ " "                ++ s') <$> m    <*> m'  )
fmtBinOpM   opP  sym  m m' = ask >>= \PPEnv{..} -> parensIf (envPrec > opP ) <$> ((\s s' -> s ++ " "  ++ sym ++ " " ++ s') <$> m    <*> m'  )

fmtBindM :: String -> PP String -> String -> PP String
fmtBindM pre mSuf n = (\suf -> pre ++ n ++ suf) <$> mSuf

fmtLetBindM :: PP String -> PP String -> String -> PP String
fmtLetBindM mTyAnn mBnd n = (\tyA bnd -> "let " ++ n ++ tyA ++ " = " ++ bnd ++ " in ") <$> mTyAnn <*> mBnd

fmtXLetM :: PP String -> PP String -> PP String
fmtXLetM mBnd mBdy = ask >>= \PPEnv{..} -> (\bnd bdy -> parensIf (envPrec > 0) $ cDepth envDepth "let " ++ bnd ++ cDepth envDepth " in " ++ bdy) <$> mBnd <*> mBdy

fmtKindAnnM :: Maybe Kind -> PP String
fmtKindAnnM = maybe (pure "") (\k -> (" ∷ " ++) <$> withPrec 0 (ppKindM k))

fmtQuantGroupsM :: QuantGroups -> PP String
fmtQuantGroupsM = \case
  [g] -> fmtGroupM g
  gs  -> unwords . map (\x -> "(" ++ x ++ ")")         <$> traverse fmtGroupM gs
  where fmtGroupM (ns, k) = ((unwords ns ++ " ∷ ") ++) <$> withPrec 0 (ppKindM k)

fmtQuantM :: Quant -> BindsT -> PP String -> PP String
fmtQuantM q binds innerM = do
  p         <- asks envPrec
  groupsStr <- fmtQuantGroupsM (groupBinds binds)
  parensIf (p > 0) . (\inr -> sym q ++ groupsStr ++ ". " ++ inr) <$> innerM
  where sym = \case { QForall -> "∀ "; QExists -> "∃ " }

fmtFieldsM :: Labels -> [PP String] -> PP String
fmtFieldsM ls argsM = sequence argsM >>= \args -> pure $ intercalate ", " $ zipWith (\l a -> unLabel l ++ " : " ++ a) ls args

collectArgs :: Type -> (Type, [Type])
collectArgs = collect []
  where collect args = \case
          TLoc _  t  -> collect       args  t
          TApp t  t' -> collect (t' : args) t
          t          ->         (t  , args)

collectArgsNeuNf :: NeuNfT -> (NeuNfT, [NfT])
collectArgsNeuNf = collect []
  where collect args = \case
          NfNeuApp nf nf' -> collect (nf' : args) nf
          nf              ->         (nf  , args)

--------------------------------------------------------------------------------

ppKind :: Prec -> Kind -> String
ppKind p k = runPP (PPEnv [] p 0) (ppKindM k)

ppKindM :: Kind -> PP String
ppKindM = \case
  KStar        -> pure "*"
  KArr dom cod -> fmtBinOpM precArr "→" (withPrec (precArr + 1) (ppKindM dom)) (withPrec precArr (ppKindM cod))

--------------------------------------------------------------------------------

ppConstTM :: ConstT -> PP String
ppConstTM = \case
  TInt         -> pure "Int"
  TDouble      -> pure "Double"
  TString      -> pure "String"
  TArr         -> pure "(→)"
  TIO          -> pure "IO"
  
  TForall   k  -> ("∀[" ++) . (++ "]") <$> withPrec 0 (ppKindM k)
  TExists   k  -> ("∃[" ++) . (++ "]") <$> withPrec 0 (ppKindM k)
  
  TRecordC  ls -> pure $ "{" ++ intercalate ", " (map unLabel ls) ++ "}"
  TVariantC ls -> pure $ "⟨" ++ intercalate ", " (map unLabel ls) ++ "⟩"

binOpInfoT :: ConstT -> Maybe (Prec, Prec, Prec, String)
binOpInfoT = \case { TArr -> Just (precArr, precArr + 1, precArr, "→"); _ -> Nothing }

isBinOp      :: Type   -> Maybe (Prec, Prec, Prec, String)
isBinOpNeuNf :: NeuNfT -> Maybe (Prec, Prec, Prec, String)

isBinOp      t =  case unLoc t of { TConst     c -> binOpInfoT c; _ -> Nothing }
isBinOpNeuNf   = \case            { NfNeuConst c -> binOpInfoT c; _ -> Nothing }

ppType :: Names -> Prec -> Type -> String
ppType tNms p t = runPP (PPEnv tNms p 0) (ppTypeM t)

ppTypeM :: Type -> PP String
ppTypeM t = ask >>= \PPEnv{..} -> case collectArgs t of
  (TConst (TRecordC  ls), args) | length ls == length args -> ("{" ++) . (++ "}") <$> fmtFieldsM ls (map (withPrec 0 . ppTypeM) args)
  (TConst (TVariantC ls), args) | length ls == length args -> ("⟨" ++) . (++ "⟩") <$> fmtFieldsM ls (map (withPrec 0 . ppTypeM) args)
  _                                                        -> case t of
    TLoc    _    t'           -> ppTypeM t'
    
    _ | Just (q, _, _, _) <- isQuant t ->
        let (binds, tNms', inner) = collectQ q envTNms t in
        fmtQuantM q binds (local (\e -> e { envTNms = tNms', envPrec = 0 }) (ppTypeM inner))

    TVar    i                    -> pure     (idxNmT envTNms i)
    TGlobal gnm                  -> pure     (unGName gnm)
    TConst  c                    -> ppConstTM c
    
    TLam    (LName l) mk    tBdy -> withBinder withTNm l (fmtBindM "λ " ((++ ". ") <$> fmtKindAnnM mk)) (ppTypeM tBdy)
    TLet    (LName l) mk ty tBdy -> withBinder withTNm l (fmtLetBindM (fmtKindAnnM mk) (withPrec 0 (ppTypeM ty))) (ppTypeM tBdy)
    TMu     t'                   -> fmtPrefixM precApp   (pure     "μ "              ) (withPrec   (precApp  + 1) (ppTypeM t' ))
    TMu'    t'                   -> fmtPrefixM precApp   (pure     "μ′ "             ) (withPrec   (precApp  + 1) (ppTypeM t' ))
    
    TApp    (TApp op ty) ty' | Just (opP, p', p'', sym) <- isBinOp op
                                 -> fmtBinOpM opP sym (withPrec p'      (ppTypeM ty)) (withPrec  p''          (ppTypeM ty'))
        
    TApp    t'            t''    -> fmtAppM precApp   (withPrec precApp (ppTypeM t')) (withPrec (precApp + 1) (ppTypeM t''))

--------------------------------------------------------------------------------

ppNfT :: Names -> Prec -> NfT -> String
ppNfT tNms p nf = runPP (PPEnv tNms p 0) (ppNfTM nf)

ppNfTM :: NfT -> PP String
ppNfTM nf = ask >>= \PPEnv{..} -> case nf of
  _ | Just (q, _, _, _) <- isQuantNf nf -> 
        let (binds, tNms', inner) = collectQNf q envTNms nf in
        fmtQuantM q binds (local (\e -> e { envTNms = tNms', envPrec = 0 }) (ppNfTM inner))
        
  NfNeu               ne                -> ppNeuNfTM ne
  NfLam  (LName l) mk body              -> withBinder withTNm l (fmtBindM "λ " ((++ ". ") <$> fmtKindAnnM mk)) (ppNfTM body)

ppNeuNfT :: Names -> Prec -> NeuNfT -> String
ppNeuNfT tNms p nf = runPP (PPEnv tNms p 0) (ppNeuNfTM nf)

ppNeuNfTM :: NeuNfT -> PP String
ppNeuNfTM ne = ask >>= \PPEnv{..} -> case collectArgsNeuNf ne of
  (NfNeuConst (TRecordC  ls), args) | length ls == length args -> ("{" ++) . (++ "}") <$> fmtFieldsM ls (map (withPrec 0 . ppNfTM) args)
  (NfNeuConst (TVariantC ls), args) | length ls == length args -> ("⟨" ++) . (++ "⟩") <$> fmtFieldsM ls (map (withPrec 0 . ppNfTM) args)
  _                                                            -> case ne of
    NfNeuBVar   i             -> pure     (idxNmT envTNms i)
    NfNeuFVar   l             -> pure     (lvlNmT envTNms l)
    NfNeuGlobal gnm           -> pure     (unGName gnm)
    NfNeuConst  c             -> ppConstTM c
    
    NfNeuMu     nfBody        -> fmtPrefixM precApp (pure "μ " )  (withPrec (precApp + 1) (ppNfTM nfBody))
    NfNeuMu'    nfBody        -> fmtPrefixM precApp (pure "μ′ ")  (withPrec (precApp + 1) (ppNfTM nfBody))
    
    NfNeuApp    (NfNeuApp op nf') nf'' | Just (opP, p', p'', sym) <- isBinOpNeuNf op
                              -> fmtBinOpM opP sym (withPrec p'      (ppNfTM    nf')) (withPrec  p''          (ppNfTM nf''))
        
    NfNeuApp    nf' nf''      -> fmtAppM precApp   (withPrec precApp (ppNeuNfTM nf')) (withPrec (precApp + 1) (ppNfTM nf''))

--------------------------------------------------------------------------------

ppConstE :: ConstE -> String
ppConstE = \case
  EPutStr      -> "putStr"
  EGetLine     -> "getLine"
  EReadFile    -> "readFile"
  EWriteFile   -> "writeFile"
  
  EArgCount    -> "argCount"
  EArgAt       -> "argAt"
  
  EAdd         -> "(+)"
  ESub         -> "(-)"
  EMul         -> "(*)"
  EAddD        -> "(+.)"
  ESubD        -> "(-.)"
  EMulD        -> "(*.)"
  EDivD        -> "(/.)"
  ETrunc       -> "trunc"
  
  EIntEq       -> "=="
  EStringEq    -> "=^"
  EDoubleEq    -> "=."
  EConcat      -> "(^)"
  ESubstring   -> "substring"
  ELength      -> "length"
  EShowInt     -> "showInt"
  EShowDouble  -> "showDouble"

binOpInfo :: ConstE -> Maybe (Prec, Prec, Prec, String)
binOpInfo = \case
  EConcat   -> Just (5, 6, 5, "^" )
  EIntEq    -> Just (5, 6, 6, "==")
  EStringEq -> Just (5, 6, 6, "=^")
  EDoubleEq -> Just (5, 6, 6, "=.")
  EMul      -> Just (7, 7, 8, "*" )
  EMulD     -> Just (7, 7, 8, "*.")
  EDivD     -> Just (7, 7, 8, "/.")
  EAdd      -> Just (6, 6, 7, "+" )
  ESub      -> Just (6, 6, 7, "-" )
  EAddD     -> Just (6, 6, 7, "+.")
  ESubD     -> Just (6, 6, 7, "-.")
  _         -> Nothing

--------------------------------------------------------------------------------

ppErased :: Prec -> Int -> Erased -> String
ppErased p d e = runPP (PPEnv [] p d) (ppErasedM e)

ppErasedM :: Erased -> PP String
ppErasedM er = ask >>= \PPEnv{..} -> case er of
  XVar     i                      -> pure $ bool ("\ESC[36m#" ++ show (unIx i) ++ "\ESC[0m") (cDepth (envDepth - 1 - unIx i) ("#" ++ show (unIx i))) (unIx i < envDepth)
  XGlobal  gnm                    -> pure (unGName gnm)
  XConst   c                      -> pure (ppConstE c)
  
  XInt     n                      -> pure (show n)
  XDouble  d                      -> pure (show d)
  XString  s                      -> pure (show (T.unpack s))
  
  XLam     e                      -> fmtPrefixM  0 (pure (cDepth envDepth "λ. ")) (withPrec 0 (withDepthUp (ppErasedM e)))

  XApp     (XApp (XConst c) e) e' | Just (opP, p', p'', sym) <- binOpInfo c
                                  -> fmtBinOpM opP sym (withPrec p' (ppErasedM e)) (withPrec p'' (ppErasedM e'))
  
  XApp     e   e'                 -> fmtAppM     precAppExp     (withPrec precAppExp (ppErasedM e   )) (withPrec   (precAppExp + 1) (ppErasedM e'   ))
  XLet     eBnd eBdy              -> fmtXLetM                   (withPrec 0          (ppErasedM eBnd)) (withPrec 0 (withDepthUp     (ppErasedM eBdy)))
  
  XRecord  flds                   -> ("{" ++) . (++ "}") . intercalate ", " <$> mapM (uncurry (\lbl -> fmap ((++) (unLabel lbl ++ " = ")) . withPrec 0 . ppErasedM)) (Map.toList flds)
  XVariant lbl e                  -> ((++ "⟩") . (++) ("⟨" ++ unLabel lbl ++ " = ")) <$> withPrec 0 (ppErasedM e)
  
  XProj    e   lbl                -> fmtPostfixM precTApp (pure ("." ++ unLabel lbl)) (withPrec precTApp (ppErasedM e))
  XMatch   e   brs                -> (\eStr brStrs -> parensIf (envPrec > precAppExp) (eStr ++ " ? ⟨" ++ intercalate ", " brStrs ++ "⟩")) <$> withPrec (precAppExp + 1) (ppErasedM e) <*> mapM (uncurry (\lbl -> fmap ((++) (unLabel lbl ++ " ↦ ")) . withPrec 0 . ppErasedM)) (Map.toList brs)
  
  XFix     e                      -> fmtPrefixM  precAppExp     (pure (cDepth envDepth "fix "))   (withPrec (precAppExp + 1) (ppErasedM e ))
  XReturn  e                      -> fmtPrefixM  precAppExp     (pure               "return ")    (withPrec (precAppExp + 1) (ppErasedM e ))
  XBind    e   e'                 -> fmtBinOpM   precBind ">>=" (withPrec precBind (ppErasedM e)) (withPrec (precBind   + 1) (ppErasedM e'))

--------------------------------------------------------------------------------

ppView :: View -> String
ppView = \case
  VwOmitted             -> "…"
  VwEvaluating          -> "<~ … >"
  VwUneval      e       -> "<~ " ++ ppErased 0 0 e ++ ">"
  
  VwInt         n       -> show  n
  VwDouble      x       -> show  x
  VwString      s       -> show (T.unpack s)
  
  VwClosure     e env   -> "<" ++ cDepth 0 "λ. " ++ ppErased 0 1 e ++ bool (" | [" ++ intercalate ", " (map ppView env) ++ "]") "" (null env) ++ ">"
  VwPartial     c as    -> "<" ++ unwords (ppConstE c : map ppView as)                                                                        ++ ">"
                                 
  VwRecord      flds    -> "{" ++ intercalate ", " (map (\(lbl, sn) -> unLabel lbl ++ " = " ++ ppView sn) flds) ++ "}"
  VwVariant     lbl sn  -> "⟨" ++ unLabel lbl                                      ++ " = " ++ ppView sn        ++ "⟩"
     
  VwIOReturn    sn      -> "return "             ++ ppView sn
  VwIOBind      snL snK -> ppView snL ++ " >>= " ++ ppView snK
  
  VwIPutStr     sn      -> "putStr "    ++ ppView sn
  VwIGetLine            -> "getLine"
  VwIReadFile   sn      -> "readFile "  ++ ppView sn
  VwIWriteFile  sn snK  -> "writeFile " ++ ppView sn ++ " " ++ ppView snK
  VwIArgCount           -> "argCount"
  VwIArgAt      sn      -> "argAt "     ++ ppView sn
