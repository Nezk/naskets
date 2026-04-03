{-# LANGUAGE LambdaCase #-}

module Main where

import           System.Environment (getArgs      , withArgs                                 )
import           System.Exit        (exitFailure  , exitSuccess                              )
import           System.IO          (hPutStrLn    , stderr                                   )
import           System.FilePath    (takeDirectory, takeBaseName, pathSeparator, (<.>), (</>))
import           System.Directory   (doesFileExist                                           )
                                                                                             
import           Control.Monad      (foldM        , when         , unless                    )
import           Data.List          (isInfixOf                                               )
import           Data.Bool          (bool                                                    )
                                                                                             
import           Data.Set           (Set                                                     )
import qualified Data.Set         as Set                                                     
import qualified Data.Map         as Map                                                     
                                                                                             
import           Text.Parsec        (parse                                                   )
                                                                                             
import           Syntax                                                                      
import           Eval               (evalT                                                   )
import           Equiv              (equivT                                                  )
import           Run                (buildGlobals , runProgram   , runExcs                   )
import           Typechecker        (checkProgram , Ctx(..)                                  )
import           Parser             (parseModule                                             )

--------------------------------------------------------------------------------

abort :: String -> IO a
abort = (>> exitFailure) . hPutStrLn stderr

--------------------------------------------------------------------------------

data LoadState
  = LoadState { stVisiting :: Set MName,
                stLoaded   :: Set MName,
                stOrder    :: [Module ] }

loadModule :: FilePath -> FilePath -> Maybe MName -> LoadState -> IO (MName, LoadState)
loadModule base path mnmExp st = case mnmExp of
  Just e | Set.member e (stVisiting st) -> abort  $ errC e
         | Set.member e (stLoaded   st) -> return   (e, st)
  _                                     -> do
    m@(Module mnm includes decls) <- readFile path >>= either (abort . errP) return . parse parseModule path
    
    let fileBase = MName (takeBaseName path)
    when (mnm /= fileBase && mnm /= MName "Main") $
      abort $ "Module name mismatch in " ++ path ++ ": expected " ++ unMName fileBase ++ " or Main but got " ++ unMName mnm
    
    mapM_ (\e -> when (e /= mnm) $ abort $ errM e mnm) mnmExp
    
    if Set.member mnm (stVisiting st)
      then abort  $ errC mnm
      else if Set.member mnm (stLoaded st)
             then return (mnm, st)
             else do
               hPutStrLn stderr ("Loading module " ++ unMName mnm)
               
               let isMain  = \case { DLoc _ d -> isMain d; DeclFun (GName "main") _ _ -> True; _ -> False }
                   hasMain = any isMain decls
                   
               if mnm == MName "Main"
                 then unless hasMain $ abort  errNoMain
                 else when   hasMain $ abort (errHasMain mnm)
                 
               stV <- foldM (loadInclude base) (st { stVisiting = Set.insert mnm (stVisiting st) }) includes
               
               return (mnm, stV {stVisiting = Set.delete mnm (stVisiting stV),
                                 stLoaded   = Set.insert mnm (stLoaded   stV),
                                 stOrder    = m :             stOrder    stV})
  where errP       e     = "Parse error in "          ++ path ++ ":\n" ++ show e
        errM       e mnm = "Module name mismatch in " ++ path ++ ": expected " ++ unMName e ++ " but got " ++ unMName mnm
        errC         mnm = "Cyclic module dependency detected involving: " ++ unMName mnm
        errNoMain        = "Module Main must export a main function."
        errHasMain   mnm = "Library module "  ++ unMName mnm ++ " cannot define a main function."

loadInclude :: FilePath -> LoadState -> MName -> IO LoadState
loadInclude base st mnm = doesFileExist path >>= bool
  (abort $ "Could not find module " ++ unMName mnm ++ " at " ++ path)
  (snd <$> loadModule base path (Just mnm) st)
  where path = base </> map (\case '.' -> pathSeparator; c -> c) (unMName mnm) <.> "nsk"

--------------------------------------------------------------------------------

main :: IO ()
main = getArgs >>= \case
  []         -> abort "Usage: naskets <source> [args…]"
  (f : args) -> processAndRun f args

processAndRun :: FilePath -> [String] -> IO ()
processAndRun file args = do
  (entryNm, finalState) <- loadModule (takeDirectory file) file Nothing (LoadState Set.empty Set.empty [])
  
  hPutStrLn stderr ""
  
  let flatProgram     = Program $ concatMap (\(Module _ _ ds) -> ds) (reverse $ stOrder finalState)
      entryDecls      =  case stOrder finalState of { Module _ _ ds : _ -> ds      ; []        -> []           }
      getExc          = \case                       { DLoc   _ d        -> getExc d; DeclExc e -> [e]; _ -> [] }
      excs            = concatMap getExc entryDecls
      (tcRes, report) = checkProgram flatProgram
  
  mapM_ (hPutStrLn stderr) report
  
  either (abort  . ("Type error:\n" ++)) (exec entryNm flatProgram report excs) tcRes
  where mainNm   = GName "main"
        ioUnitT  = TApp  (TConst TIO) (TConst (TRecordC []))
        finish   = (>> exitSuccess) . hPutStrLn stderr
        
        exec eNm prg rep excDecls ctx
          | hasHoles  = finish hlsErr
          | otherwise = do
              rtGlbs <- buildGlobals prg
              unless (null excDecls) $ runExcs rtGlbs excDecls >> putStrLn ""
              if eNm == MName "Main"
                then maybe (abort mnErr) (bool (abort mtErr) (runScript rtGlbs) . isValidMain) mainNIn
                else finish "Typechecking succeeded."
          where mainNIn        = Map.lookup mainNm (ctxGlbET ctx)
                hasHoles       = any ("Hole:" `isInfixOf`) rep
                isValidMain vt = equivT glbT 0 vt (evalT glbT [] ioUnitT)
                glbT           = ctxGlbT ctx
                
                runScript rtG  = withArgs args (runProgram rtG mainNm) >> exitSuccess
                
                hlsErr         = "Typechecking succeeded (with holes)."
                mtErr          = "Typechecking succeeded, but main does not have type IO {}. Execution aborted."
                mnErr          = "Typechecking succeeded, but main was not found."
