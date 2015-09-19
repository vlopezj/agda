{-# OPTIONS --allow-unsolved-metas #-}

infixr 6 _∷_

data List (A : Set) : Set where
  [] : List A
  _∷_ : A -> List A -> List A

postulate
  Bool : Set
  t : Bool

long : List Bool
long = <?php for($i=0; $i < $argv[1]; $i++) { ?> _∷_ t ( <?php } ?> []
 <?php for($i=0; $i < $argv[1]; $i++) { ?> ) <?php } ?>

meta : Set
meta = _
