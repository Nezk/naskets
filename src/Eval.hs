{-# LANGUAGE LambdaCase    #-}
{-# LANGUAGE TupleSections #-}

module Eval where

import Syntax
import Utils

--------------------------------------------------------------------------------

evalT :: GTypes -> EnvT -> Type -> ValT
evalT glbT envT = \case
  TVar    (Ix i)      -> envT     !!  i
  TGlobal     gnm     -> VAlias   gnm [] (lookupOrErr gnm glbT $ "Unknown global type: " ++ unGName gnm)
  TConst      c       -> VNeu            (NeuConst      c)
  TLam    lnm mk body -> VClosure lnm mk body envT
  TApp        ty ty'  -> appT     glbT (evalT glbT envT ty) (evalT glbT envT ty')
  TMu         ty      -> VMu           (evalT glbT envT ty)    
  TLoc    _   ty      -> evalT    glbT             envT ty

appT :: GTypes -> ValT -> ValT -> ValT
appT glbT v v' = case v of
  VClosure _ _ body envT      -> evalT glbT (v'     :  envT)  body
  VNeu         ne             -> VNeu       (NeuApp ne v'  )
  VMu          _              -> internalErr "Ill-kinded application: μ _ ∷ *, not * → *"
  VAlias       gnm  args body -> VAlias gnm (args  ++ [v' ]) (appT glbT body v')

rbT :: GTypes -> Lv -> Lv -> ValT -> NfT
rbT glbT dOrg d = \case
  VAlias            gnm args _  -> NfNeu (foldl NfNeuApp (NfNeuGlobal gnm) (map    (rbT  glbT dOrg d)  args))
  VNeu              ne          -> NfNeu                 (rbNe        ne )
  val@(VClosure lnm mk  _    _) -> NfLam  lnm    mk      (rbT glbT dOrg    (d + 1) (appT glbT val (fresh d)))
  VMu               vBody       -> NfNeu        (NfNeuMu (rbT glbT dOrg     d       vBody                  ))
  where rbNe = \case
          NeuVar   l     | l < dOrg  -> NfNeuFVar      l
                         | otherwise -> NfNeuBVar (Ix (unLv d - 1 - unLv l))
          NeuConst c                 -> NfNeuConst     c
          NeuApp   ne v'             -> NfNeuApp      (rbNe ne) (rbT glbT dOrg d v')

--------------------------------------------------------------------------------

-- Consider: ∀ Y. t and ∀ Y. t'

-- where: t  = μ (λa. Y → a)
-- and:   t' = Y → μ (λb. Y → b)

-- I. e., Y is a locally-free variable bound at Level 0 (F0).

-- as: []

-- rbT      (μ (λa. Y → a)) ⇒      μ (λ. F0 → B0)
-- rbT  (Y → μ (λb. Y → b)) ⇒ F0 → μ (λ. F0 → B0)

-- Not in as. Adding (μ (λ. F0 → B0), F0 → μ (λ. F0 → B0)) to as.

-- t is μ
-- Unroll t to (Y → μ (λa. Y → a)) and recurse (see unfoldL)

-- Comparing Y to Y (True).
-- Recurses on the bodies: checkBody (μ (λa. Y → a)) (μ (λb. Y → b))

-- as: [ (μ(λ. F0 → B0), F0 → μ(λ. F0 → B0)) ]

-- rbT  (μ (λa. Y → a)) ⇒ μ (λ. F0 → B0)
-- rbT  (μ (λb. Y → b)) ⇒ μ (λ. F0 → B0)

-- Pair (μ …, μ …) is NOT in as. Adding the pair to as.
-- Left t is μ. Unroll t to (Y → μ (λa. Y → a)) and recurse.

-- as: [ (μ …, μ …), (μ …, F0 → μ …) ]

-- rbT  (Y → μ (λa. Y → a)) ⇒ F0 → μ (λ. F0 → B0)
-- rbT      (μ (λb. Y → b)) ⇒      μ (λ. F0 → B0)

-- Pair (F0 → μ …, μ …) is NOT in as. Adding the pair to as.
-- Right t' is μ now. Unroll t' to (Y → μ (λb. Y → b)) and recurse with (Y → μ (λa. Y → a)) and (Y → μ (λb. Y → b)).

-- ⇒ Compares Y to Y (True).
-- ⇒ Recurses on the bodies: checkBody (μ (λa. Y → a)) (μ (λb. Y → b))

-- as: [ (F0 → μ …, μ …), (μ …, μ …), (μ …, F0 → μ …) ]

-- rbT  (μ (λa. Y → a)) ⇒ μ (λ. F0 → B0)
-- rbT  (μ (λb. Y → b)) ⇒ μ (λ. F0 → B0)

-- Pair (μ(λ. F0 → B0), μ(λ. F0 → B0)) IS in as ⇒ t = t'

equivT :: GTypes -> Lv -> ValT -> ValT -> Bool
equivT glbT dO vO vO' = fst (eq [] dO vO vO') 
  where eq as d vRaw vRaw' = case (vRaw, vRaw') of
          -- Consider:     Phantom a ≔ Int
          -- Phantom Int = Phantom String ⇒ "Phantom" == "Phantom"                    ⇒ checkArgs
          --         Int ≠ String         ⇒ unaliasing Phantom and checking its body  ⇒ True
          (VAlias gnm args _, VAlias gnm' args' _) 
            | gnm == gnm' -> maybe (checkBody as d (unalias vRaw) (unalias vRaw')) (True,)
                                   (checkArgs d as (args,          args'        ))
          _               ->        checkBody as d (unalias vRaw) (unalias vRaw')
          where unalias = \case { VAlias _ _ body -> unalias body; val -> val }
          
        checkArgs d as = \case
          ([]    , []      ) -> Just as
          (v : vs, v' : vs') -> case eq as d v v' of
                                  (True , as') -> checkArgs d as' (vs, vs')
                                  (False, _  ) -> Nothing
          _                  -> Nothing
        
        checkBody as d v v'
          | (nf, nf') `elem` as      = (True, as)
          | otherwise                = case (v, v') of
              (VClosure{}, _         ) -> eta
              (_         , VClosure{}) -> eta
              (VMu f     , _         ) -> unfoldL f
              (_         , VMu f'    ) -> unfoldR f'
              (VNeu ne   , VNeu ne'  ) -> equivNeu as' d ne ne'
              _                        -> (False, as')
          where nf         = rb v
                nf'        = rb v'
                as'        = (nf, nf') : as
                rb         = rbT  glbT d d
                app        = appT glbT
                eta        = eq   as' (d + 1) (app v (fresh d)) (app v' (fresh d)) -- applying f from μ f to the entire μ type (i.e., to VMu f)
                unfoldL f  = if isNonContr glbT d v  then (isNonContr glbT d v', as') else eq as' d (app f  v) v' 
                unfoldR f' = if isNonContr glbT d v' then (False               , as') else eq as' d v  (app f' v')
          
        equivNeu as d ne ne' = case (ne, ne') of
          (NeuVar   l , NeuVar    l') -> (l == l', as)
          (NeuConst c , NeuConst  c') -> (c == c', as)
          (NeuApp f a , NeuApp f' a') -> case equivNeu as d f f' of
                                           (True, as') -> eq as' d a a'
                                           failed      -> failed
          _                           -> (False, as)

-- A type is non-contractive if it is a chain of µ-binders that refers back to one of its own bound variables,
-- for example, µ(λα. α) or µ(λα. µ(λβ. α)).

-- Since we use De Bruijn levels, the variables bound by the k µ-binders range from level dO to d - 1. 
-- An expression is non-contractive if its innermost body is one of these variables (l >= dO && l < d).

-- That is,

-- m is non-contractive ⇔
--   m = µ (λα₁ ∷ *. µ (λα₂ ∷ *. (… (µ (λα_k ∷ *. αᵢ)) …)))
--                                               ^^^
--                                          for some i ∈ {1 … k}

-- Suppose we have allowed µ to act on the type ((* -> *) -> (* -> *)) -> (* -> *).

-- We could define:
-- F = λα ∷ (* → *). λβ ∷ *. α β
-- And:
-- Loop = µ F (has type: * → *)

-- Now let us consider the evaluation of T = Loop Int.

-- isNonContr checks µ (λα. λβ. α β). The inner abstraction (λβ. α β) does not return α immediately.

-- When decomposeT attempts to unwrap the head of Loop Int, it applies Loop to Int:
-- Loop Int

-- Loop is expanded:
-- (F Loop) Int

-- To evaluate F Loop, F is expanded:
-- (λα. λβ. α β) Loop Int

-- The variable α is replaced with Loop
-- (λβ. Loop β) Int
-- ⇒ Loop Int

-- In this type system, µ is restricted to the kind * -> *.
-- Therefore, as long as the type is contractive, repeated expansion of appT glbT f (VMu f) is guaranteed to terminate after a finite 
-- number of reductions, eventually revealing some constructor (like a Record, Variant, or Arrow).

isNonContr :: GTypes -> Lv -> ValT -> Bool
isNonContr glbT dO = isNC dO
  where isNC d = \case
          VAlias _ _ vBody -> isNC  d       vBody
          VMu          f   -> isNC (d + 1) (appT glbT f (fresh d))
          VNeu (NeuVar l)  -> l >= dO && l < d
          _                -> False

--------------------------------------------------------------------------------

decomposeT :: GTypes -> Lv -> ValT -> Maybe (ConstT, [ValT])
decomposeT glbT d = \case
  VAlias     _ _ vBody -> decomposeT glbT d vBody
  VClosure{}           -> Nothing
  VNeu           ne    -> case spineNe [] ne of
                        (NeuConst c, args) -> Just (c, args)
                        _                  -> Nothing
  self@(VMu      f)    -> if   isNonContr glbT d  self
                          then Nothing
                          else decomposeT glbT d (appT glbT f self)
  where spineNe args = \case
          NeuApp ne arg -> spineNe (arg : args) ne
          ne            ->         (ne,   args)

--------------------------------------------------------------------------------

-- I hate this function like you wouldn't belive
nfToT :: Lv -> NfT -> Type
nfToT d = \case
  NfNeu        nf      -> neuNfToT            d      nf
  NfLam lnm mk nfBody  -> TLam lnm mk (nfToT (d + 1) nfBody)
  where neuNfToT dCurrent = \case
          NfNeuConst     c      -> TConst  c
          NfNeuGlobal    gnm    -> TGlobal gnm
          NfNeuBVar      i      -> TVar    i
          NfNeuFVar  (Lv l)     -> TVar   (Ix (unLv dCurrent - 1 - l))
          NfNeuApp       nf nf' -> TApp   (neuNfToT dCurrent nf) (nfToT dCurrent nf')
          NfNeuMu        nf     -> TMu    (nfToT    dCurrent nf)
