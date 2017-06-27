{-# OPTIONS --cubical #-}
module Apply where

open import Lib.Primitives public
open import Level
open import Data.Bool using (Bool; true; false)
open import Lib.PathPrelude

test : (b : Bool) → Path b b
test b i = b

open import Common.IO
open import Common.String
open import Common.Unit
open import Common.Maybe

fun₁ : Bool → Bool
fun₁ x = x

not : Bool → Bool
not true = false
not false = true

fun₂ : Bool → Bool
fun₂ x = not (not x)

pointwise : (b : Bool) → Path (fun₁ b) (fun₂ b)
pointwise false i = false
pointwise true i = true

global : Path fun₁ fun₂
global = fun-ext pointwise

main : IO Unit
main =
  readBool >>= \
    { nothing  -> putStrLn "NO INPUT"
    ; (just b) ->
        putStrLn  "Test 1"      ,,
        printBool (test b i0)  ,,
        putStr    "\n" ,,
        printBool (test (not b) i0) ,,
        putStr    "\n" ,,
        putStrLn  "Test 2"      ,,
        printBool (test b i1)  ,,
        putStr    "\n" ,,
        printBool (test (not b) i1) ,,
        putStr    "\n" ,,
        putStrLn  "Test 3"      ,,
        printBool (global i0 b)  ,,
        putStr    "\n" ,,
        printBool (global i1 b) ,,
        putStr    "\n" ,,
        return    unit
   }

