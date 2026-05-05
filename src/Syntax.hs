{-# LANGUAGE DerivingVia #-}

module Syntax where

import Data.IORef (IORef)
import Data.Map   (Map)
import Data.Text  (Text)

--------------------------------------------------------------------------------

data Pos = Pos String Int Int deriving (Show, Eq)

newtype Ix = Ix { unIx :: Int } deriving (Show, Num, Eq)      via Int
newtype Lv = Lv { unLv :: Int } deriving (Show, Num, Eq, Ord) via Int

newtype GName = GName { unGName :: String } deriving (Show, Eq, Ord) via String -- Ord is derived so that GName can be used as a Map key.
newtype LName = LName { unLName :: String } deriving (Show, Eq)      via String 
newtype HName = HName { unHName :: String } deriving (Show, Eq)      via String -- Hole names for typed holes
newtype MName = MName { unMName :: String } deriving (Show, Eq, Ord) via String -- Module names
newtype Label = Label { unLabel :: String } deriving (Show, Eq, Ord) via String -- Record and variant labels. Ord derived for Map as well (the fields have canonical order).

type GKinds  = Map GName Kind
type GTypes  = Map GName ValT
type GErased = Map GName Thunk

type Names  = [LName]
type Labels = [Label]
type Kinds  = [Kind]
type EnvT   = [ValT]

type RecFlds   = Map Label Exp
type MatchBrs  = Map Label (LName, Exp)

type XRecFlds  = Map Label Erased
type XMatchBrs = Map Label Erased

type ThunkFlds = Map Label Thunk

--------------------------------------------------------------------------------

data Kind
  = KStar          -- *                  
  | KArr Kind Kind -- k → k    
  deriving Eq

data Type
  = TVar    Ix                     
  | TConst                           ConstT 
  | TGlobal GName                         
  | TLam          LName (Maybe Kind) Type      -- λα ∷ κ. τ / λα. τ
  | TApp                             Type Type -- τ₁ τ₂
  | TMu                              Type      -- μ  τ
  | TMu'                             Type      -- μ′ τ
  | TLoc          Pos                Type

data ConstT
  = TInt | TDouble | TString    -- ι   : *
  | TArr                        -- _→_ : * → * → *
  | TIO                         -- IO  : * → *

  | TForall Kind | TExists Kind -- t[κ]   : (κ → *) → *

  | TRecordC  Labels            -- { l1 : _, …, l_n : _ }
  | TVariantC Labels            -- ⟨ l1 : _, …, l_n : _ ⟩
  deriving Eq

--------------------------------------------------------------------------------

infixl 5 :>
data Args a = Emp | Args a :> a

data ValT
  = VNeu                        NeuT
  | VMu                         ValT      
  | VClosure LName (Maybe Kind) Type EnvT  
  | VAlias   GName (Args ValT)  ValT      -- The ValT argument is lazy, I HOPE

data NeuT
  = NeuVar    Lv      
  | NeuConst     ConstT
  | NeuMu'       ValT        
  | NeuApp       NeuT   ValT

--------------------------------------------------------------------------------

data NfT
  = NfNeu                    NeuNfT  
  | NfLam LName (Maybe Kind) NfT     

instance Eq NfT where -- ignoring LName
  NfNeu ne        == NfNeu ne'         = ne == ne'
  NfLam _ mk body == NfLam _ mk' body' = mk == mk' && body == body'
  _               == _                 = False

data NeuNfT
  = NfNeuConst        ConstT      
  | NfNeuGlobal GName             
  | NfNeuBVar   Ix                
  | NfNeuFVar   Lv             -- Locally free with respect to the sub-term
  | NfNeuApp          NeuNfT  NfT 
  | NfNeuMu                   NfT 
  | NfNeuMu'                  NfT
  deriving Eq

--------------------------------------------------------------------------------

data Exp
  = EVar    Ix   
  | EGlobal GName

  | EConst  ConstE
  | EInt    Integer
  | EDouble Double
  | EString Text

  | ELam  LName (Maybe Type) Exp     -- λx : τ. t / λx. t
  | ETLam LName (Maybe Kind) Exp     -- Λα ∷ κ. t / Λa. t
  
  | EApp  Exp Exp                    -- t s
  | ETApp Exp Type                   -- t[τ]
  
  | EAnn                    Exp Type -- t : τ
  | ELet LName (Maybe Type) Exp Exp  -- let x = t in … / let x : τ = t in …
  
  | ERecord       RecFlds            -- { l = t, … }
  | EVariant      Label   Exp        -- ⟨ l = t ⟩
  
  | EProj        Exp Label           -- t.l
  | EMatch       Exp MatchBrs        -- t ? ⟨ l₁ x ↦ t₁ | … | l_n y ↦ t_n ⟩

  | EPack   Type Exp                 -- pack [σ] t
  | EUnpack      Exp LName LName Exp -- unpack t as ⟨α, x⟩ in s
  | ERoll   Type Exp                 -- roll [σ] t
  | EUnroll      Exp                 -- unroll t

  | EFix Exp                         -- fix t

  | EReturn Exp                      -- return t
  | EBind   Exp Exp                  -- t >>= s

  | EHole HName (Maybe Exp)          -- ?h{t}
  
  | ELoc  Pos   Exp

data ConstE
  = EPutStr   | EGetLine  | EReadFile | EWriteFile 
  | EArgCount | EArgAt
  
  | EAdd  | ESub  | EMul          -- +  -  *
  | EAddD | ESubD | EMulD | EDivD -- +. -. *. /.
  | ETrunc
  
  | EIntEq | EDoubleEq | EStringEq -- == =. =^
  
  | EConcat                        -- ^
  | ESubstring | ELength | EShowInt | EShowDouble                         
  deriving Eq 

--------------------------------------------------------------------------------

data Erased
  = XVar     Ix     
  | XGlobal  GName
  
  | XConst   ConstE
  | XInt     Integer
  | XDouble  Double
  | XString  Text
             
  | XLam     Erased
  | XApp     Erased Erased
             
  | XLet     Erased Erased
  
  | XRecord  XRecFlds
  | XVariant Label Erased
  
  | XProj    Erased Label
  | XMatch   Erased XMatchBrs
             
  | XFix     Erased
             
  | XReturn  Erased
  | XBind    Erased Erased

type Env      = [Thunk] -- Run env for closures
type ArgsE    = [Thunk] -- Arguments for partial application
type ExcDecls = [Exp]   -- Exec. declarations (>> …)

data ThunkState
  = Unevaluated Erased Env
  | Evaluating
  | Evaluated   ValE

newtype Thunk
  = Thunk (IORef ThunkState)

data ValE
  = VRecord   ThunkFlds
  | VVariant  Label     Thunk
  
  | VClosureE Erased    Env
  
  | VInt      Integer
  | VDouble   Double
  | VString   Text
              
  | VPartial  ConstE    ArgsE -- partial application, ie., (+) 1
              
  | VIOAct    IOActVal

data IOActVal
  = IOReturn     Thunk
  | IOStandalone IOPrim
  | IOBind       Thunk Thunk

data IOPrim
  = IPutStr    Thunk
  | IGetLine
  | IReadFile  Thunk
  | IWriteFile Thunk Thunk
  | IArgCount
  | IArgAt     Thunk

--------------------------------------------------------------------------------

type Depth = Int

data View
  = VwRecord     [(Label,    View)]
  | VwVariant      Label     View
                           
  | VwClosure      Erased   [View]
  
  | VwInt          Integer
  | VwDouble       Double
  | VwString       Text
                  
  | VwPartial      ConstE   [View]
                  
  | VwIOReturn     View
  | VwIOBind       View      View
  | VwIPutStr      View
  | VwIGetLine     
  | VwIReadFile    View
  | VwIWriteFile   View      View
  | VwIArgCount    
  | VwIArgAt       View
                  
  | VwOmitted      
  | VwEvaluating   
  | VwUneval       Erased

--------------------------------------------------------------------------------

data Decl
  = DeclType GName Kind Type
  | DeclFun  GName Type Exp 
  | DeclExc  Exp
  | DLoc     Pos   Decl

data Module
  = Module MName [MName] [Decl]

newtype Program
  = Program [Decl]
