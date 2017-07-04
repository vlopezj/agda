{-# OPTIONS --cubical #-}
module Bool where

open import Level
open import Data.Bool using (Bool; true; false)
open import Data.Product public using (Σ; _,_) renaming (proj₁ to fst; proj₂ to snd)
open import Lib.PathPrelude


unglue-equiv : ∀ {a} (A : Set a) → (φ : I) → (T : Partial (Set a) φ) (f : PartialP φ \ o → Equiv (T o) A)  → Equiv (Glue A φ T f) A
unglue-equiv A φ T f = unglue {φ = φ} , (λ b → ((glue {φ = φ} ((\{_ → fst (fst (snd (snd (w itIsOne)) b)) }))
                                                               (primComp (\ _ → A) φ (\ j → (\{_ → snd (fst (snd (snd (w itIsOne)) b)) j })) b))
                                                           , (\ k → fill (λ v → A) φ (\ j → (\{_ → snd (fst (snd (snd (w itIsOne)) b)) j })) b k))
                                                  , (λ v → \ j →
                                                      (glue {φ = φ} (\{_ → fst ((snd (snd (snd (w itIsOne)) b)) v j) })
                                                        (primComp (λ _ → A) _ (\ k → [ φ   ↦ (\{_ → (snd (snd (snd (snd (w itIsOne)) b) v j) k ) }) , _ ↦
                                                                                     [ ~ j ↦ (\{_ → fill (λ _ → A) φ (\ j →
                                                                                                     (\{_ → snd (fst (snd (snd (w itIsOne)) b)) j })) b k })
                                                                                     , j   ↦ (\{_ → snd v k }) ] ])
                                                                              b))
                                                      , ( (\ z -> fill (\ _ → A) _ (\ k →
                                                                       [ φ   ↦ (\{_ → (snd (snd (snd (snd (w itIsOne)) b) v j) k ) }) , _ ↦
                                                                       [ ~ j ↦ (\{_ → fill (λ _ → A) φ (\ j →
                                                                                       (\{_ → snd (fst (snd (snd (w itIsOne)) b)) j })) b k })
                                                                       , j   ↦ (\{_ → (snd v)  k }) ] ])
                                                                       b
                                                                       z) )))
   where w : PartialP φ \ _ → Σ _ \ T → Equiv T A
         w = \ o → (T o , f o)

Equiv-contr : ∀ {a} (A : Set a) → Contr.isContr (Σ _ \ T → Equiv T A)
Equiv-contr A = (A , idEquiv) , (λ w →  \ i → let φ = (~ i ∨ i)
                                                  Tf : Partial (Σ _ \ T → Equiv T A) (~ i ∨ i)
                                                  Tf = [ ~ i ↦ (\{_ → A , idEquiv }) , i ↦ (\{_ → w }) ]
                                              in Glue A φ (\ o → fst (Tf o)) (\ o → snd (Tf o))
                                                 , unglue-equiv A φ (\ o → fst (Tf o)) (\ o → snd (Tf o)))


univ : ∀ {l} {A B : Set l} → Equiv A B → Path A B
univ {A = A} {B = B} eq = let ((T , ev) , p) = Equiv-contr B in \ i →
   fst (Contr.isContrProp (Equiv-contr B) (A , eq) (B , idEquiv) i)


not : Bool → Bool
not true = false
not false = true

notnot : ∀ y → y ≡ not (not y)
notnot true = refl
notnot false = refl

nothelp : ∀ y (y₁ : Σ Bool (λ x → Path y (not x))) →
          Path (not y , notnot y) y₁
nothelp y (true , eq) = pathJ (λ y₁ eq' → Path (not y₁ , notnot y₁) (true , sym eq')) refl _ (sym eq)
nothelp y (false , eq) = pathJ (λ y₁ eq' → Path (not y₁ , notnot y₁) (false , sym eq')) refl _ (sym eq)


notEquiv : Equiv Bool Bool
notEquiv = not , (\ { y → (not y , notnot y) , nothelp y })

testBool : Path Bool Bool -> Bool -> Bool
testBool p b = primComp (\ i → p i) i0 (\ _ → empty) b

test₁ : Bool -> Bool
test₁ = testBool refl

test₂ : Bool -> Bool
test₂ = testBool (univ notEquiv)

open import Common.IO
open import Common.String
open import Common.Unit

main : IO Unit
main =
  putStrLn  "Test 1"      ,,
  -- printBool (test₁ true)  ,,
  putStrLn "" ,,
  -- printBool (test₁ false) ,,
  putStrLn "" ,,
  putStrLn  "Test 2"      ,,
  -- printBool (test₂ true)  ,,
  putStrLn "" ,,
  -- printBool (test₂ false) ,,
  putStrLn "" ,,
  return    unit
