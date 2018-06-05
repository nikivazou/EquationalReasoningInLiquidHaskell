{-@ LIQUID "--no-termination" @-}

module Slides where

import Data.Maybe
import Text.Pandoc.JSON
import Data.List
import Debug.Trace

main :: IO ()
main = toJSONFilter tx

tx :: Block -> [Block]
tx (Div (_, ["slideonly"], _) bs)
  = bs
tx z
  = [z]
