{-# OPTIONS --cubical #-}
module Transitivity where

open import Lib.Primitives public
open import Level
open import Data.Bool using (Bool; true; false)
open import Lib.PathPrelude

not : Bool → Bool
not true = false
not false = true

test : (b : Bool) → Path b (not (not b))
test true  i = true
test false i = false

boolToInterval : (b : Bool) → I
boolToInterval false = i0
boolToInterval true  = i1

open import Common.IO
open import Common.String
open import Common.Unit
open import Common.Maybe

reflrefl : (b : Bool) → Path b b
reflrefl b = trans (test b) (sym (test b))

main : IO Unit
main =
  readBool >>= \
    { nothing  -> putStrLn "NO INPUT"
    ; (just b) ->
        putStrLn  "Test 1"      ,,
        printBool (test b (boolToInterval b))  ,,
        putStr    "\n" ,,
        printBool (reflrefl (not b) (boolToInterval b)) ,,
        putStr    "\n" ,,
        return    unit
   }

