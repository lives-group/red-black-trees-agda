module Intrinsic where

  open import Agda.Primitive

  open import Data.Nat
  open import Data.Product

  open import Relation.Binary
  open import Relation.Binary.PropositionalEquality


  -- a data type for ordering

  data Ord : Set where
    LT : Ord
    EQ : Ord
    GT : Ord

  -- definition of colors and trees

  module TreeDef {Key : Set}(compare : Key → Key → Ord)(Value : Set) where

    data Color (n : ℕ) : ℕ → Set where
      Red   : Color n n
      Black : Color n (suc n)

    data Tree : ℕ → Set where
      Empty : Tree 1
      Node  : ∀ {n m : ℕ} → (Key × Value) → (c : Color n m) → (l r : Tree n) → Tree m


    -- balance

    balance : ∀ {n m : ℕ}→ Key × Value → (c : Color n m) → (l r : Tree n) → Tree m
    balance kv Black (Node y Red (Node x Red a b) c) d = Node y Red (Node x Black a b) (Node kv Black c d)
    balance kv Black (Node x Red a (Node y Red b c)) d = Node y Red (Node x Black a b) (Node kv Black c d)
    balance kv Black a (Node z Red (Node y Red b c) d) = Node y Red (Node kv Black a b) (Node z Black c d)
    balance kv Black a (Node y Red b (Node z Red c d)) = Node y Red (Node kv Black a b) (Node z Black c d)
    balance kv c l r = Node kv c l r


    -- insertion

    ins : ∀ {n} → (Key × Value) → Tree n → Tree n
    ins kv Empty = Node kv Red Empty Empty
    ins (k , v) (Node (k' , v') c l r) with compare k k'
    ins (k , v) (Node (k' , v') c l r) | LT = balance (k' , v') c (ins (k , v) l) r
    ins (k , v) (Node (k' , v') c l r) | EQ = Node (k , v) c l r
    ins (k , v) (Node (k' , v') c l r) | GT = balance (k' , v') c l (ins (k , v) r)

    blackenRoot : ∀ {n} → Tree n → ∃ (λ m → Tree m)
    blackenRoot Empty = _ , Empty
    blackenRoot (Node kv _ l r) = _ , Node kv Black l r

    insert : ∀ {n} → (Key × Value) → Tree n → ∃ (λ m → Tree m)
    insert kv t = blackenRoot (ins kv t)
