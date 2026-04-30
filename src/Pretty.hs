{-# LANGUAGE LambdaCase    #-}
{-# LANGUAGE PatternGuards #-}

module Pretty where

import           Data.Bool     ( bool       )
import           Data.List     ( intercalate)
import qualified Data.Map   as   Map
import qualified Data.Text  as   T

import           Syntax
import           Utils  

--------------------------------------------------------------------------------

type Prec = Int

data Assoc
  = LeftAssoc
  | RightAssoc
  | NoneAssoc

precApp, precArr, precTApp, precAppExp, precBind :: Prec

precTApp   = 11
precApp    = 10
precAppExp = 10
precArr    = 4
precBind   = 1

parensIf :: Bool -> String -> String
parensIf cond s = bool s ("(" ++ s ++ ")") cond

binOpAssoc :: Prec -> Assoc -> (Prec, Prec)
binOpAssoc opP = \case
  LeftAssoc  -> (opP    , opP + 1)
  RightAssoc -> (opP + 1, opP    )
  NoneAssoc  -> (opP + 1, opP + 1)

nameSuffixes :: [String]
nameSuffixes = "" : "′" : "″" : "‴" : map show [(1 :: Int)..]

freshName :: String -> Names -> String 
freshName base nms = findFresh nameSuffixes
  where findFresh = \case
          s : ss -> let lnm = base ++ s in bool (findFresh ss) lnm (LName lnm `notElem` nms)
          []     -> base

idxNameErr :: String -> Names -> Ix -> String
lvlNameErr :: String -> Names -> Lv -> String

idxNameErr err nms (Ix i) = checkBounds err nms "index" i  i
lvlNameErr err nms (Lv l) = checkBounds err nms "level" l (length nms - 1 - l)

checkBounds :: String -> Names -> String -> Int -> Int -> String
checkBounds err nms kind orig i =
  bool (internalErr $ "Out of bounds " ++ err ++ " " ++ kind ++ ": " ++ show orig)
       (unLName (nms !! i))
       (i >= 0 && i < length nms)

idxNmT :: Names -> Ix -> String
idxNmE :: Names -> Ix -> String
lvlNmT :: Names -> Lv -> String

idxNmT = idxNameErr "type"
idxNmE = idxNameErr "term"
lvlNmT = lvlNameErr "free neutral type"

fmtKindAnn :: Maybe Kind -> String
fmtKindAnn = maybe "" ((" ∷ " ++) . ppKind 0)

fmtTypeAnn :: Names -> Maybe Type -> String
fmtTypeAnn tNms = maybe "" ((" : " ++) . ppType tNms 0)

fmtMap :: (Label -> a -> String) -> Map.Map Label a -> String
fmtMap f = intercalate ", " . map (uncurry f) . Map.toList

fmtBinOp :: Prec -> Prec -> String -> String -> String -> String
fmtBinOp p opP sym e e' = parensIf (p > opP) $ e ++ " " ++ sym ++ " " ++ e'

--------------------------------------------------------------------------------

type BindsT      = [( String,  Kind)]
type QuantGroups = [([String], Kind)]

type Collected  a = (BindsT, Names, a)
type Quantifier a = Maybe (Quant, Kind, LName, a)

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
collectQGen isQ q nms t = case isQ t of
  Just (q', k, lnm, body) | q == q' ->
    let lnm'                 = freshName (unLName lnm) nms
        (binds, nms', inner) = collectQGen isQ q (LName lnm' : nms) body
    in  ((lnm', k) : binds, nms', inner)
  _                                 -> ([], nms, t)

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

fmtQuantGroups :: QuantGroups -> String
fmtQuantGroups = \case
  [g] -> fmtGroup g
  gs  -> unwords [ "(" ++ fmtGroup g ++ ")" | g <- gs ]
  where fmtGroup (ns, k) = unwords ns ++ " ∷ " ++ ppKind 0 k

fmtQuant :: Prec -> Quant -> BindsT -> String -> String
fmtQuant p q binds inner = parensIf (p > 0) $ sym q ++ fmtQuantGroups (groupBinds binds) ++ ". " ++ inner
  where sym = \case { QForall -> "∀ "; QExists -> "∃ " }

fmtFields :: (a -> String) -> Labels -> [a] -> String
fmtFields pp ls args = intercalate ", " $ zipWith (\l a -> unLabel l ++ " : " ++ pp a) ls args

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
ppKind p = \case
  KStar        -> "*"
  KArr dom cod -> parensIf (p > precArr) $ ppKind (precArr + 1) dom ++ " → " ++ ppKind precArr cod

--------------------------------------------------------------------------------

ppConstT :: ConstT -> String
ppConstT = \case
  TInt         -> "Int"
  TDouble      -> "Double"
  TString      -> "String"
  TArr         -> "(→)"
  TIO          -> "IO"
  
  TForall   k  -> "∀["  ++ ppKind 0 k ++ "]" -- TODO
  TExists   k  -> "∃["  ++ ppKind 0 k ++ "]"
  
  TRecordC  ls -> "{" ++ joinLbls ls ++ "}"
  TVariantC ls -> "⟨" ++ joinLbls ls ++ "⟩"
  where joinLbls = intercalate ", " . map unLabel

binOpInfoT :: ConstT -> Maybe (String, Prec, Assoc)
binOpInfoT = \case
  TArr  -> Just ("→", precArr, RightAssoc)
  _     -> Nothing

isBinOp      :: Type   -> Maybe (String, Prec, Assoc)
isBinOpNeuNf :: NeuNfT -> Maybe (String, Prec, Assoc)

isBinOp      t =  case unLoc t of { TConst     c -> binOpInfoT c; _ -> Nothing }
isBinOpNeuNf   = \case            { NfNeuConst c -> binOpInfoT c; _ -> Nothing }

ppType :: Names -> Prec -> Type -> String
ppType tNms p t = case collectArgs t of
  (TConst (TRecordC  ls), args) | length ls == length args -> "{" ++ fmtFields (pp 0) ls args ++ "}"
  (TConst (TVariantC ls), args) | length ls == length args -> "⟨" ++ fmtFields (pp 0) ls args ++ "⟩"
  _                                                        -> case t of
    TLoc    _    t'           -> pp p t'
    
    _ | Just (q, k, lnm, body) <- isQuant t ->
        let lnm'                  = freshL lnm
            (binds, tNms', inner) = collectQ q (LName lnm' : tNms) body
        in  fmtQuant p q ((lnm', k) : binds) (ppType tNms' 0 inner)

    TVar    i                 -> idxNmT tNms i
    TGlobal gnm               -> unGName gnm
    TConst  c                 -> ppConstT c
    
    TLam    lnm  mk      tBdy -> let lnm' = freshL lnm in parens 0 $ "λ" ++ lnm' ++ fmtKindAnn mk ++ ". " ++ ppBody lnm' tBdy
    TMu     t'                -> parens precApp $ "μ "  ++ pp (precApp + 1) t'
    TMu'    t'                -> parens precApp $ "μ′ " ++ pp (precApp + 1) t'
    
    TApp    (TApp op t') t''  | Just (sym, opP, assoc) <- isBinOp op ->
        let (p', p'') = binOpAssoc opP assoc
        in  fmtBinOp p opP sym (pp p' t') (pp p'' t'')
        
    TApp    t'            t'' -> parens precApp $ pp precApp t' ++ " " ++ pp (precApp + 1) t''
  where pp         = ppType tNms
        ppBody lT  = ppType (LName lT : tNms) 0
        freshL lnm = freshName (unLName lnm) tNms
        parens pr  = parensIf (p > pr)

--------------------------------------------------------------------------------

ppNfT :: Names -> Prec -> NfT -> String
ppNfT tNms p nf = maybe ppBase ppQ (isQuantNf nf)
  where ppBase = case nf of
          NfNeu         ne   -> ppNeuNfT tNms p ne
          NfLam  lnm mk body -> let lnm' = freshL lnm in parens 0 $ "λ" ++ lnm' ++ fmtKindAnn mk ++ ". " ++ ppBody lnm' body
        ppQ (q, k, lnm, body) =
          let lnm'                  = freshL lnm
              (binds, tNms', inner) = collectQNf q (LName lnm' : tNms) body
          in  fmtQuant p q ((lnm', k) : binds) (ppNfT tNms' 0 inner)
        freshL lnm = freshName (unLName lnm) tNms
        ppBody lT  = ppNfT (LName lT : tNms) 0
        parens pr  = parensIf (p > pr)

ppNeuNfT :: Names -> Prec -> NeuNfT -> String
ppNeuNfT tNms p nf = case collectArgsNeuNf nf of
  (NfNeuConst (TRecordC  ls), args) | length ls == length args -> "{" ++ fmtFields (pp 0) ls args ++ "}"
  (NfNeuConst (TVariantC ls), args) | length ls == length args -> "⟨" ++ fmtFields (pp 0) ls args ++ "⟩"
  _                                                            -> case nf of
    NfNeuBVar   i      -> idxNmT tNms i
    NfNeuFVar   l      -> lvlNmT tNms l
    NfNeuGlobal gnm    -> unGName gnm
    NfNeuConst  c      -> ppConstT c
    
    NfNeuMu     nfBody -> parens precApp $ "μ "  ++ pp (precApp + 1) nfBody
    NfNeuMu'    nfBody -> parens precApp $ "μ′ " ++ pp (precApp + 1) nfBody
    
    NfNeuApp    (NfNeuApp op nf') nf'' | Just (sym, opP, assoc) <- isBinOpNeuNf op ->
        let (p', p'') = binOpAssoc opP assoc
        in  fmtBinOp p opP sym (pp p' nf') (pp p'' nf'')
        
    NfNeuApp    nf' nf'' -> parens precApp $ ppNeuNfT tNms precApp nf' ++ " " ++ pp (precApp + 1) nf''
  where pp        = ppNfT tNms
        parens pr = parensIf (p > pr)

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

ppExp :: Names -> Names -> Prec -> Exp -> String
ppExp tNms eNms p = \case
  ELoc    _   e                  -> pp p e
  EVar    i                      -> idxNmE eNms i
  EGlobal gnm                    -> unGName gnm
  EConst  c                      -> ppConstE c
  
  EInt    n                      -> show n
  EDouble d                      -> show d
  EString s                      -> show (T.unpack s)
  
  EAnn    e   t                  -> parens 0 $ pp 0 e ++ " : " ++ ppT 0 t
  
  ELam    lnm mTy  eBdy          -> let lnm' = freshE lnm in parens 0 $ "λ" ++ lnm' ++ fmtTypeAnn tNms mTy ++ ". " ++ ppBodyE lnm' eBdy
  ETLam   lnm mk   eBdy          -> let lnm' = freshT lnm in parens 0 $ "Λ" ++ lnm' ++ fmtKindAnn mk ++ ". " ++ ppBodyT lnm' eBdy
  
  ELet    lnm mTy  e    e'       -> let lnm' = freshE lnm in parens 0 $ "let " ++ lnm' ++ fmtTypeAnn tNms mTy ++ " = " ++ pp 0 e ++ " in " ++ ppBodyE lnm' e'
  
  EApp    (EApp (EConst c) e) e' | Just (opP, p', p'', sym) <- binOpInfo c -> fmtBinOp p opP sym (pp p' e) (pp p'' e')
  
  EApp    e   e'                 -> parens precAppExp $ pp precAppExp e ++ " "  ++ pp (precAppExp + 1) e'
  ETApp   e   t                  -> parens precTApp   $ pp precTApp   e ++ " [" ++ ppT 0 t ++ "]"
    
  ERecord flds                   -> "{" ++ fmtMap (\lbl e' -> unLabel lbl ++ " = " ++ pp 0 e') flds ++ "}"
  EVariant lbl e                 -> "⟨" ++ unLabel lbl ++ " = " ++ pp 0 e ++ "⟩"
  
  EProj   e   lbl                -> parens precTApp   $ pp precTApp e ++ "." ++ unLabel lbl
  EMatch  e   brs                -> parens precAppExp $ pp (precAppExp + 1) e ++ " ? ⟨" ++ fmtMap (\lbl (lnm, e') -> unLabel lbl ++ " " ++ unLName lnm ++ " ↦ " ++ ppBodyE (unLName lnm) e') brs ++ "⟩"
    
  EPack   t   e                  -> parens precAppExp $ "pack ["   ++ ppT 0 t ++ "] " ++ pp (precAppExp + 1) e
  ERoll   t   e                  -> parens precAppExp $ "roll ["   ++ ppT 0 t ++ "] " ++ pp (precAppExp + 1) e
  EUnpack e   lnmT lnmE eBdy     -> let lnmT' = freshT lnmT; lnmE' = freshE lnmE in parens 0 $ "unpack " ++ pp 0 e ++ " as ⟨" ++ lnmT' ++ ", " ++ lnmE' ++ "⟩ in " ++ ppBody lnmT' lnmE' eBdy
  EUnroll e                      -> parens precAppExp $ "unroll "  ++ pp (precAppExp + 1) e

  EFix    e                      -> parens precAppExp $ "fix "     ++ pp (precAppExp + 1) e
  EReturn e                      -> parens precAppExp $ "return "  ++ pp (precAppExp + 1) e
  EBind   e   e'                 -> parens precBind   $ pp precBind e ++ " >>= " ++ pp (precBind + 1) e'
                              
  EHole   hnm me                 -> "?" ++ unHName hnm ++ maybe "" (("{" ++) . (++ "}") . pp 0) me
  where pp            = ppExp  tNms eNms 
        ppT           = ppType tNms
        ppBodyE    lE = ppExp  tNms             (LName lE : eNms) 0
        ppBodyT lT    = ppExp (LName lT : tNms)             eNms  0
        ppBody  lT lE = ppExp (LName lT : tNms) (LName lE : eNms) 0
        freshE  lnm   = freshName (unLName lnm) eNms
        freshT  lnm   = freshName (unLName lnm) tNms
        parens  pr    = parensIf (p > pr)

--------------------------------------------------------------------------------

ppErased :: Prec -> Erased -> String
ppErased p = \case
  XVar     i                      -> "#" ++ show i
  XGlobal  gnm                    -> unGName gnm
  XConst   c                      -> ppConstE c
  
  XInt     n                      -> show n
  XDouble  d                      -> show d
  XString  s                      -> show (T.unpack s)
  
  XLam     e                      -> parens 0          $ "λ. " ++ pp 0 e

  XApp     (XApp (XConst c) e) e' | Just (opP, p', p'', sym) <- binOpInfo c -> fmtBinOp p opP sym (pp p' e) (pp p'' e')
  
  XApp     e   e'                 -> parens precAppExp $ pp precAppExp e ++ " " ++ pp (precAppExp + 1) e'
  
  XLet     e   e'                 -> parens 0          $ "let " ++ pp 0 e ++ " in " ++ pp 0 e'
  
  XRecord  flds                   -> "{" ++ fmtMap (\lbl e' -> unLabel lbl ++ " = " ++ pp 0 e') flds ++ "}"
  XVariant lbl e                  -> "⟨" ++ unLabel lbl ++ " = " ++ pp 0 e ++ "⟩"
  
  XProj    e   lbl                -> parens precTApp   $ pp  precTApp e ++ "." ++ unLabel lbl
  XMatch   e   brs                -> parens precAppExp $ pp (precAppExp + 1) e ++ " ? ⟨" ++ fmtMap (\lbl e' -> unLabel lbl ++ " ↦ " ++ pp 0 e') brs ++ "⟩"
  
  XFix     e                      -> parens precAppExp $ "fix "    ++ pp (precAppExp + 1) e
  XReturn  e                      -> parens precAppExp $ "return " ++ pp (precAppExp + 1) e
  XBind    e   e'                 -> parens precBind   $              pp  precBind e ++ " >>= " ++ pp (precBind + 1) e'
  where pp        = ppErased
        parens pr = parensIf (p > pr)

--------------------------------------------------------------------------------

ppView :: View -> String
ppView = \case
  VwOmitted             -> "…"
  VwEvaluating          -> "<~ … >"
  VwUneval      e       -> "<~ " ++ ppErased 0 e ++ ">"
  
  VwInt         n       -> show  n
  VwDouble      x       -> show  x
  VwString      s       -> show (T.unpack s)
  
  VwClosure     e env   -> "<λ. " ++ ppErased 0 e ++ bool (" | [" ++ intercalate ", " (map ppView env) ++ "]") "" (null env) ++ ">"
  VwPartial     c as    -> "<"    ++ unwords (ppConstE c : map ppView as) ++ ">"
                                 
  VwRecord      flds    -> "{"    ++ intercalate ", " (map (\(lbl, sn) -> unLabel lbl ++ " = " ++ ppView sn) flds) ++ "}"
  VwVariant     lbl sn  -> "⟨"    ++ unLabel lbl ++ " = " ++ ppView sn ++ "⟩"
     
  VwIOReturn    sn      -> "return "             ++ ppView sn
  VwIOBind      snL snK -> ppView snL ++ " >>= " ++ ppView snK
  
  VwIPutStr     sn      -> "putStr "    ++ ppView sn
  VwIGetLine            -> "getLine"
  VwIReadFile   sn      -> "readFile "  ++ ppView sn
  VwIWriteFile  sn snK  -> "writeFile " ++ ppView sn ++ " " ++ ppView snK
  VwIArgCount           -> "argCount"
  VwIArgAt      sn      -> "argAt "     ++ ppView sn
