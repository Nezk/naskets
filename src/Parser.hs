{-# LANGUAGE StrictData #-}

module Parser where

import           Text.Parsec
import           Text.Parsec.String    (Parser  )
import           Text.Parsec.Language  (emptyDef)
import           Text.Parsec.Expr
import qualified Text.Parsec.Token  as  Token

import           Data.List             (intercalate, elemIndex, sortBy, nub)
import           Data.Functor          ((<&>                              ))
import           Data.Functor.Identity (Identity                           )
import qualified Data.Map            as Map
import qualified Data.Text           as T

import           Control.Monad         (when)

import           Syntax

--------------------------------------------------------------------------------

nasketsDef :: Token.LanguageDef ()
nasketsDef = emptyDef
  { Token.commentStart    = "{-"                                               ,
    Token.commentEnd      = "-}"                                               ,
    Token.commentLine     = "--"                                               ,
    Token.nestedComments  = True                                               ,
    Token.identStart      = letter   <|> char '_'                              ,
    Token.identLetter     = alphaNum <|> char '_' <|> char '\'' <|> oneOf "′″‴",
    Token.opStart         = oneOf ":!#$%&*+./<=>?@\\^|-~"                      ,
    Token.opLetter        = oneOf ":>=\\"                                      ,
    Token.reservedNames   =
      ["module"   , "where"     , "import"  ,
       "Int"      , "Double"    , "String"  ,
       "IO"       , "return"    ,
       "let"      , "in"        ,
       "pack"     , "unpack"    , "as"      ,
       "fix"      ,             
       "putStr"   , "getLine"   , "readFile", "writeFile",
       "argCount" , "argAt"     ,
       "substring", "length"    , "trunc"   ,
       "showInt"  , "showDouble",
       "refl"     , "subst"     ,
       "mu"       ,
       "forall"   , "exists"   ],
    Token.reservedOpNames =
      ["::" , "∷"  , ":" ,
       "="  ,
       "->" , "→"  ,
       "Λ"  , "/\\", "\\", "λ",
       "."  ,
       "~"  ,
       "?"  ,
       "|"  , "↦"  ,
       ">>=", ">>" ,
       "==" , "=^" , "=.",
       "["  , "]"  ,
       "<"  , ">"  , "⟨" , "⟩",
       ","  ,
       "∀"  , "∃"  ,
       "^"  ,
       "μ" ],
    Token.caseSensitive   = True }

lexer :: Token.TokenParser ()
lexer = Token.makeTokenParser nasketsDef

identifier, stringLiteral :: Parser String

identifier    = Token.identifier    lexer
stringLiteral = Token.stringLiteral lexer

reserved, reservedOp :: String -> Parser ()

reserved   = Token.reserved   lexer
reservedOp = Token.reservedOp lexer

lsym :: String -> Parser String
lsym = Token.symbol lexer

parens, brackets, braces, angles, mathAngles :: Parser a -> Parser a

parens       = Token.parens   lexer
brackets     = Token.brackets lexer
braces       = Token.braces   lexer
angles       = Token.angles   lexer
mathAngles p = between (reservedOp "⟨") (reservedOp "⟩") p

toPos :: SourcePos -> Pos
toPos sp = Pos (sourceName sp) (sourceLine sp) (sourceColumn sp)

ensureUnique :: SourcePos -> String -> [Label] -> Parser ()
ensureUnique pos errMsg lbls = when (length (nub lbls) /= length lbls) $ do
  setPosition pos
  fail errMsg

withLoc :: (Pos -> a -> a) -> Parser a -> Parser a
withLoc wrap p = do
  sp <- getPosition
  x  <- p
  return $ wrap (toPos sp) x

--------------------------------------------------------------------------------

parseKind :: Parser Kind
parseKind = buildExpressionParser table (parens parseKind <|> (reservedOp "*" >> return KStar))
  where table = [[Infix (reservedOp "->" >> return KArr) AssocRight,
                  Infix (reservedOp "→"  >> return KArr) AssocRight]]

parseType :: Names -> Parser Type
parseType tNms = withLoc TLoc $ buildExpressionParser tTable (tyApp tNms)

tTable :: [[Operator String () Identity Type]]
tTable =
  [[Infix (try (getPosition <* reservedOp "~") >>= \sp -> brackets parseKind <&> \k l r -> TLoc (toPos sp) (TApp (TApp (TConst (TEq k)) l) r)) AssocNone],
   [infixR (reservedOp "->") (\l r -> TApp (TApp (TConst TArr) l) r),
    infixR (reservedOp "→")  (\l r -> TApp (TApp (TConst TArr) l) r)]]
  where infixR p f = Infix (try (getPosition <* p) <&> \sp l r -> TLoc (toPos sp) (f l r)) AssocRight

tyApp :: Names -> Parser Type
tyApp tNms = do
  ty <- tyExp tNms
  fs <- many (do pos <- getPosition; arg <- tyExp tNms; return $ \acc -> TLoc (toPos pos) (TApp acc arg))
  return $ foldl (\acc f -> f acc) ty fs

parseQuantifierSugar :: Names -> Parser Type
parseQuantifierSugar tNms = do
  quant        <- (reserved   "forall" >> return TForall) <|>
                  (reservedOp "∀"      >> return TForall) <|>
                  (reserved   "exists" >> return TExists) <|>
                  (reservedOp "∃"      >> return TExists)
  binderGroups <- many1 (parens parseGroup <|> parseGroup)
  _            <- reservedOp "."
  
  let flatBinders = concat binderGroups
      nms         = map fst flatBinders
  body <- parseType (reverse nms ++ tNms)
  
  return $ foldr (\(lnm, k) ty -> TApp (TConst (quant k)) (TLam lnm (Just k) ty)) body flatBinders
  where parseGroup = do nms   <- many1 identifier
                        _     <- reservedOp "::" <|> reservedOp "∷"
                        k     <- parseKind
                        return [(LName lnm, k) | lnm <- nms]

parseRow :: String -> (Labels -> ConstT) -> (Parser [(Label, Type)] -> Parser [(Label, Type)]) -> Names -> Parser Type
parseRow errMsg con wrap tNms = do
  pos    <- getPosition
  fields <- wrap (sepBy (parseField tNms) (reservedOp ","))
  let sortedFields = sortBy (\(lbl, _) (lbl', _) -> compare lbl lbl') fields
      lbls         = map fst sortedFields
  ensureUnique pos ("Duplicate labels in " ++ errMsg ++ " type") lbls
  return $ foldl TApp (TConst (con lbls)) (map snd sortedFields)

parseRecordType, parseVariantType :: Names -> Parser Type

parseRecordType  = parseRow "record"  TRecordC  braces
parseVariantType = parseRow "variant" TVariantC (\p -> angles p <|> mathAngles p)

parseField :: Names -> Parser (Label, Type)
parseField tNms = (,) . Label <$> identifier <* (reservedOp ":" <|> reservedOp "∷") <*> parseType tNms

tyExp :: Names -> Parser Type
tyExp tNms = withLoc TLoc $
      try (parseQuantifierSugar tNms)
  <|> try (parens (reservedOp "->") >> return (TConst TArr))
  <|> try (parens (reservedOp "→" ) >> return (TConst TArr))
  <|> try (parens (reservedOp "~" ) >> brackets parseKind <&> TConst . TEq)
  <|> parseRecordType        tNms
  <|> parseVariantType       tNms
  <|> try (parens (parseType tNms))
  <|>     (reserved  "Int"          >> return (TConst  TInt   ))
  <|>     (reserved  "Double"       >> return (TConst  TDouble))
  <|>     (reserved  "String"       >> return (TConst  TString))
  <|>     (reserved  "IO"           >> return (TConst  TIO    ))
  <|> try ((reserved "forall" <|> reservedOp "∀") >> brackets parseKind <&> TConst . TForall)
  <|> try ((reserved "exists" <|> reservedOp "∃") >> brackets parseKind <&> TConst . TExists)
  <|> try ((reserved "mu"     <|> reservedOp "μ") >> tyExp    tNms      <&> TMu             )
  <|> try (do _            <- reservedOp "λ" <|> reservedOp "\\"
              binderGroups <- many1 (parens parseGroup <|> parseGroup)
              _            <- reservedOp "."
              
              let flatBinders = concat binderGroups
                  nms         = map fst flatBinders
              body <- parseType (reverse nms ++ tNms)
              
              return $ foldr (uncurry TLam) body flatBinders)
  <|> try (do pos <- getPosition
              lnm <- identifier
              lookAhead (notFollowedBy (try (char '=' >> notFollowedBy (oneOf ":!#$%&*+./<=>?@\\^|-~"))))
              when      (sourceColumn pos == 1) $
                lookAhead (notFollowedBy (reservedOp "::" <|> reservedOp "∷" <|> reservedOp ":"))
              return $ maybe (TGlobal (GName lnm)) (TVar . Ix) (elemIndex (LName lnm) tNms))
  where parseGroup = do nms <- many1 identifier
                        mk  <- optionMaybe ((reservedOp "::" <|> reservedOp "∷") >> parseKind)
                        return [ (LName lnm, mk) | lnm <- nms ]

--------------------------------------------------------------------------------

parseExp :: Names -> Names -> Parser Exp
parseExp tNms eNms = withLoc ELoc $
      try (parseLet    tNms eNms)
  <|> try (parseLam    tNms eNms)
  <|> try (parseTyLam  tNms eNms)
  <|> try (parseUnpack tNms eNms)
  <|> expOp            tNms eNms

expOp :: Names -> Names -> Parser Exp
expOp tNms eNms = buildExpressionParser expTable (expApp tNms eNms)

expTable :: [[Operator String () Identity Exp]]
expTable =
  [[prefix (lsym       "-." ) (unOp  ESubD (EDouble 0.0)) ,
    prefix (reservedOp "-"  ) (unOp  ESub  (EInt 0     ))],
   [infixL (lsym       "*." ) (binOp EMulD              ) ,
    infixL (lsym       "/." ) (binOp EDivD              ) ,
    infixL (reservedOp "*"  ) (binOp EMul               )],
   [infixL (lsym       "+." ) (binOp EAddD              ) ,
    infixL (lsym       "-." ) (binOp ESubD              ) ,
    infixL (reservedOp "+"  ) (binOp EAdd               ) ,
    infixL (reservedOp "-"  ) (binOp ESub               )],
   [infixR (reservedOp "^"  ) (binOp EConcat            )],
   [infixN (lsym       "==" ) (binOp EIntEq             ) ,
    infixN (lsym       "=^" ) (binOp EStringEq          ) ,
    infixN (lsym       "=." ) (binOp EDoubleEq          )],
   [infixL (reservedOp ">>=") EBind                      ]]
  where prefix p f  = Prefix (try (getPosition <* p) <&> \sp e   -> ELoc (toPos sp) (f e))
        infixL p f  = Infix  (try (getPosition <* p) <&> \sp l r -> ELoc (toPos sp) (f l r)) AssocLeft
        infixR p f  = Infix  (try (getPosition <* p) <&> \sp l r -> ELoc (toPos sp) (f l r)) AssocRight
        infixN p f  = Infix  (try (getPosition <* p) <&> \sp l r -> ELoc (toPos sp) (f l r)) AssocNone
        binOp c l r = EApp (EApp (EConst c) l) r
        unOp c z e  = EApp (EApp (EConst c) z) e

expApp :: Names -> Names -> Parser Exp
expApp tNms eNms = do
  e  <- expTight          tNms eNms
  fs <- many (looseSuffix tNms eNms)
  return $ foldl (\e' f -> f e') e fs

looseSuffix :: Names -> Names -> Parser (Exp -> Exp)
looseSuffix tNms eNms =
      try (do pos      <- getPosition
              _        <- reservedOp "?"
              branches <- angles     (sepBy (parseBranch tNms eNms) (reservedOp "|")) <|>
                          mathAngles (sepBy (parseBranch tNms eNms) (reservedOp "|"))
              let lbls = map fst branches
              ensureUnique pos "Duplicate labels in pattern match" lbls
              return $ \e -> ELoc (toPos pos) (EMatch e (Map.fromList branches)))
  <|> try (do pos <- getPosition
              arg <- expTight tNms eNms
              return $ \e -> ELoc (toPos pos) (EApp e arg))

expTight :: Names -> Names -> Parser Exp
expTight tNms eNms = do
  e  <-       expPrefix   tNms eNms
  fs <- many (tightSuffix tNms eNms)
  return $ foldl (\e' f -> f e') e fs

tightSuffix :: Names -> Names -> Parser (Exp -> Exp)
tightSuffix tNms _ =
      try (do pos <- getPosition
              ty  <- brackets (parseType tNms)
              return $ \e -> ELoc (toPos pos) (ETApp e ty))
  <|> try (do pos <- getPosition
              _   <- reservedOp "."
              lbl <- identifier
              return $ \e -> ELoc (toPos pos) (EProj e (Label lbl)))

parseBranch :: Names -> Names -> Parser (Label, (LName, Exp))
parseBranch tNms eNms = do
  lbl <- Label <$> identifier
  lnm <- LName <$> identifier
  _   <- reservedOp "↦" <|> reservedOp "->"
  e   <- parseExp tNms (lnm : eNms)
  return (lbl, (lnm, e))

parseRecordExp :: Names -> Names -> Parser Exp
parseRecordExp tNms eNms = do
  pos    <- getPosition
  fields <- braces (sepBy (parseExpField tNms eNms) (reservedOp ","))
  ensureUnique pos "Duplicate labels in record Exp" (map fst fields)
  return $ ERecord (Map.fromList fields)

parseExpField :: Names -> Names -> Parser (Label, Exp)
parseExpField tNms eNms = (,) . Label <$> identifier <* reservedOp "=" <*> parseExp tNms eNms

parseVariantExp :: Names -> Names -> Parser Exp
parseVariantExp tNms eNms = uncurry EVariant <$>
  (angles (parseExpField tNms eNms) <|> mathAngles (parseExpField tNms eNms))

expPrefix :: Names -> Names -> Parser Exp
expPrefix tNms eNms =
      try (parseLam        tNms eNms)
  <|> try (parseTyLam      tNms eNms)
  <|>     (parseRecordExp  tNms eNms)
  <|>     (parseVariantExp tNms eNms)
  <|> try (reserved "fix"    >> EFix    <$> expTight tNms eNms)
  <|> try (reserved "return" >> EReturn <$> expTight tNms eNms)
  <|> try (reserved "pack"   >> EPack   <$> brackets (parseType tNms) <*> expTight tNms eNms)
  <|> expAtom tNms eNms

expAtom :: Names -> Names -> Parser Exp
expAtom tNms eNms = withLoc ELoc $
      (reserved "putStr"     >> return (EConst EPutStr    ))
  <|> (reserved "getLine"    >> return (EConst EGetLine   ))
  <|> (reserved "readFile"   >> return (EConst EReadFile  ))
  <|> (reserved "writeFile"  >> return (EConst EWriteFile ))
  <|> (reserved "argCount"   >> return (EConst EArgCount  ))
  <|> (reserved "argAt"      >> return (EConst EArgAt     ))
  <|> (reserved "substring"  >> return (EConst ESubstring ))
  <|> (reserved "length"     >> return (EConst ELength    ))
  <|> (reserved "showInt"    >> return (EConst EShowInt   ))
  <|> (reserved "showDouble" >> return (EConst EShowDouble))
  <|> (reserved "trunc"      >> return (EConst ETrunc     ))
  <|> (reserved "refl"       >> EConst . ERefl  <$> brackets parseKind)
  <|> (reserved "subst"      >> EConst . ESubst <$> brackets parseKind)
  <|> try (Token.naturalOrFloat lexer      <&> either EInt EDouble)
  <|> try (EString . T.pack                <$> stringLiteral)
  <|> try (reservedOp "?" >> EHole . HName <$> identifier <*> optionMaybe (braces (parseExp tNms eNms)))
  <|> try (parseParens tNms eNms)
  <|> try (do pos <- getPosition
              lnm <- identifier
              lookAhead (notFollowedBy (try (char '=' >> notFollowedBy (oneOf ":!#$%&*+./<=>?@\\^|-~"))))
              when (sourceColumn pos == 1) $
                lookAhead (notFollowedBy (reservedOp "::" <|> reservedOp "∷" <|> reservedOp ":"))
              return $ maybe (EGlobal (GName lnm)) (EVar . Ix) (elemIndex (LName lnm) eNms))

parseParens :: Names -> Names -> Parser Exp
parseParens tNms eNms = do
  _ <- lsym "("                              
  (lsym ")" >> return (ERecord Map.empty))
    <|> (try (lsym       "+." >> lsym ")") >> return (EConst EAddD    ))
    <|> (try (lsym       "-." >> lsym ")") >> return (EConst ESubD    ))
    <|> (try (lsym       "*." >> lsym ")") >> return (EConst EMulD    ))
    <|> (try (lsym       "/." >> lsym ")") >> return (EConst EDivD    ))
    <|> (try (lsym       "==" >> lsym ")") >> return (EConst EIntEq   ))
    <|> (try (lsym       "=^" >> lsym ")") >> return (EConst EStringEq))
    <|> (try (lsym       "=." >> lsym ")") >> return (EConst EDoubleEq))
    <|> (try (reservedOp "+"  >> lsym ")") >> return (EConst EAdd     ))
    <|> (try (reservedOp "-"  >> lsym ")") >> return (EConst ESub     ))
    <|> (try (reservedOp "*"  >> lsym ")") >> return (EConst EMul     ))
    <|> (try (reservedOp "^"  >> lsym ")") >> return (EConst EConcat  ))
    <|> (parseExp tNms eNms >>= \e -> (reservedOp ":" >> parseType tNms <* lsym ")" <&> EAnn e) <|> (lsym ")" >> return e))

parseLet :: Names -> Names -> Parser Exp
parseLet tNms eNms = do
  reserved   "let"
  lnm <- identifier
  mTy <- optionMaybe (reservedOp ":" >> parseType tNms)
  reservedOp "="
  e   <- parseExp tNms eNms
  reserved   "in"
  e'  <- parseExp tNms (LName lnm : eNms)
  return $ ELet (LName lnm) mTy e e'

parseLam :: Names -> Names -> Parser Exp
parseLam tNms eNms = do
  _            <- reservedOp "λ" <|> reservedOp "\\"
  binderGroups <- many1 (parens parseGroup <|> parseGroup)
  _            <- reservedOp "."
  
  let flatBinders = concat binderGroups
      nms         = map fst flatBinders
  body <- parseExp tNms (reverse nms ++ eNms)
  
  return $ foldr (uncurry ELam) body flatBinders
  where parseGroup = do nms <- many1 identifier
                        mTy <- optionMaybe (reservedOp ":" >> parseType tNms)
                        return [ (LName lnm, mTy) | lnm <- nms ]

parseTyLam :: Names -> Names -> Parser Exp
parseTyLam tNms eNms = do
  _            <- reservedOp "Λ" <|> reservedOp "/\\"
  binderGroups <- many1 (parens parseGroup <|> parseGroup)
  _            <- reservedOp "."
  
  let flatBinders = concat binderGroups
      nms         = map fst flatBinders
  body <- parseExp (reverse nms ++ tNms) eNms
  
  return $ foldr (uncurry ETLam) body flatBinders
  where parseGroup = do nms <- many1 identifier
                        mk  <- optionMaybe ((reservedOp "::" <|> reservedOp "∷") >> parseKind)
                        return [ (LName lnm, mk) | lnm <- nms ]

parseUnpack :: Names -> Names -> Parser Exp
parseUnpack tNms eNms = do
  reserved   "unpack"
  e     <- parseExp tNms eNms
  reserved   "as"
  _     <- reservedOp "⟨" <|> reservedOp "<"
  lnmT  <- identifier
  reservedOp ","
  lnmE  <- identifier
  _     <- reservedOp "⟩" <|> reservedOp ">"
  reserved   "in"
  eBody <- parseExp (LName lnmT : tNms) (LName lnmE : eNms)
  return $ EUnpack e (LName lnmT) (LName lnmE) eBody

--------------------------------------------------------------------------------

parseDecl :: Parser Decl
parseDecl = withLoc DLoc $
            try (reservedOp ">>" >> parseExp [] [] <&> DeclExc)
        <|> do gnm <- identifier
               parseTypeDeclBody gnm <|> parseFunDeclBody gnm

parseTypeDeclBody :: String -> Parser Decl
parseTypeDeclBody gnm = do
  _    <- reservedOp "::" <|> reservedOp "∷"         
  k    <- parseKind
  gnm' <- identifier
  if gnm == gnm'
    then reservedOp "=" >> parseType [] <&> DeclType (GName gnm) k
    else fail $ "Type definition name '" ++ gnm' ++ "' does not match signature name '" ++ gnm ++ "'"

parseFunDeclBody :: String -> Parser Decl
parseFunDeclBody gnm = do
  _    <- reservedOp ":"
  ty   <- parseType []
  gnm' <- identifier
  if gnm == gnm'
    then reservedOp "=" >> parseExp [] [] <&> DeclFun (GName gnm) ty
    else fail $ "Function definition name '" ++ gnm' ++ "' does not match signature name '" ++ gnm ++ "'"

parseMNm :: Parser MName
parseMNm = sepBy1 identifier (reservedOp ".") <&> MName . intercalate "."

parseImport :: Parser MName
parseImport = reserved "import" >> parseMNm

parseModule :: Parser Module
parseModule = do
  Token.whiteSpace lexer
  reserved "module"
  mnm <- parseMNm
  reserved "where"
  imports <- many parseImport
  decls   <- many parseDecl
  eof
  return $ Module mnm imports decls
