module Utils where

import           Data.Maybe (fromMaybe)
import qualified Data.Map as Map

import           GHC.Stack  (HasCallStack)

import           Syntax

fresh :: Lv -> ValT
fresh = VNeu . NeuVar

internalErr :: HasCallStack => String -> a
internalErr msg = error $ "[Internal Error] " ++ msg

lookupOrErr :: (Ord k, HasCallStack) => k -> Map.Map k v -> String -> v
lookupOrErr k m msg = fromMaybe (internalErr msg) (Map.lookup k m)
