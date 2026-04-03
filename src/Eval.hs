{-# LANGUAGE LambdaCase #-}

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
  TMu'        ty      -> VNeu          (NeuMu'              (evalT glbT envT ty))
  TLoc    _   ty      -> evalT    glbT             envT ty

appT :: GTypes -> ValT -> ValT -> ValT
appT glbT v v' = case v of
  VClosure _ _ body envT      -> evalT glbT (v'     :  envT)  body
  VNeu         ne             -> VNeu       (NeuApp ne v'  )
  VMu          _              -> internalErr "Ill-kinded application: μ _ ∷ *, not * → *"
  VAlias       gnm  args body -> VAlias gnm (args  ++ [v' ]) (appT glbT body v')

rbT :: GTypes -> Lv -> Lv -> ValT -> NfT
rbT glbT dOrg d = \case --   v global reference map lookup is fast anyway
  VAlias            gnm args _  -> NfNeu (foldl NfNeuApp (NfNeuGlobal gnm) (map    (rbT  glbT dOrg d)  args))
  VNeu              ne          -> NfNeu                 (rbNe        ne )
  val@(VClosure lnm mk  _    _) -> NfLam  lnm    mk      (rbT glbT dOrg    (d + 1) (appT glbT val (fresh d)))
  VMu               vBody       -> NfNeu        (NfNeuMu (rbT glbT dOrg     d       vBody                  ))
  where rbNe = \case
          NeuVar   l     | l < dOrg  -> NfNeuFVar      l
                         | otherwise -> NfNeuBVar (Ix (unLv d - 1 - unLv l))
          NeuConst c                 -> NfNeuConst     c
          NeuMu'   vBody             -> NfNeuMu'      (rbT glbT dOrg d vBody)
          NeuApp   ne v'             -> NfNeuApp      (rbNe ne) (rbT glbT dOrg d v')

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
          NfNeuMu'       nf     -> TMu'   (nfToT    dCurrent nf)
