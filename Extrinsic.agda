module Extrinsic where

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

    data Color : Set where
      Red   : Color
      Black : Color

    data Tree : Set where
      Empty : Tree
      Node  : (Key × Value) → Color → (l r : Tree) → Tree

    balance : (Key × Value) → Color → Tree → Tree → Tree
    balance kv Black (Node y Red (Node x Red a b) c) d = Node y Red (Node x Black a b) (Node kv Black c d)
    balance kv Black (Node x Red a (Node y Red b c)) d = Node y Red (Node x Black a b) (Node kv Black c d)
    balance kv Black a (Node z Red (Node y Red b c) d) = Node y Red (Node kv Black a b) (Node z Black c d)
    balance kv Black a (Node y Red b (Node z Red c d)) = Node y Red (Node kv Black a b) (Node z Black c d)
    balance kv c l r = Node kv c l r


    ins : (Key × Value) → Tree → Tree
    ins kv Empty = Node kv Red Empty Empty
    ins (k , v) (Node (k' , v') c l r) with compare k k'
    ins (k , v) (Node (k' , v') c l r) | LT = balance (k' , v') c (ins (k , v) l) r
    ins (k , v) (Node (k' , v') c l r) | EQ = Node (k , v) c l r
    ins (k , v) (Node (k' , v') c l r) | GT = balance (k' , v') c l (ins (k , v) r)

    blackenRoot : Tree → Tree
    blackenRoot Empty = Empty
    blackenRoot (Node kv _ l r) = Node kv Black l r


    insert : (Key × Value) → Tree → Tree
    insert kv t = blackenRoot (ins kv t)


    module BlackHeightTake1 where

      -- a family for representing the black height property

      data HasBH : Tree → ℕ → Set where
        HBH-Empty : HasBH Empty 1
        HBH-Node-Red : ∀ {n : ℕ}{l r : Tree}{kv : Key × Value} → HasBH l n → HasBH r n → HasBH (Node kv Red l r) n
        HBH-Node-Black : ∀ {n : ℕ}{l r : Tree}{kv : Key × Value} → HasBH l n → HasBH r n → HasBH (Node kv Black l r) (suc n)

      -- some simple examples

      module Examples (k k' : Key)(v v' : Value) where

        t : Tree
        t = Node (k , v) Black (Node (k' , v') Red Empty Empty) Empty

        t-bh : HasBH t 2
        t-bh = HBH-Node-Black (HBH-Node-Red HBH-Empty HBH-Empty) HBH-Empty

      blackenRoot-bh : ∀ (t : Tree)(n : ℕ) → HasBH t n → ∃ (λ (m : ℕ) → HasBH (blackenRoot t) m)
      blackenRoot-bh Empty n prf = 1 , HBH-Empty
      blackenRoot-bh (Node kv Red l r) n (HBH-Node-Red prf prf') = _ , HBH-Node-Black prf prf'
      blackenRoot-bh (Node kv Black l r) ._ (HBH-Node-Black prf prf') = _ , HBH-Node-Black prf prf'


    -- another way of defining blackheight

    module BlackHeightTake2 where

      data ColorHeight : Color → ℕ → ℕ → Set where
        CH-Red : ∀ {n : ℕ} → ColorHeight Red n n
        CH-Black : ∀ {n : ℕ} → ColorHeight Black n (suc n)

      data HasBH : Tree → ℕ → Set where
        HBH-Empty : HasBH Empty 1
        HBH-Node : ∀ {n m : ℕ}{c : Color}{l r : Tree}{kv : Key × Value} →
                   HasBH l n →
                   HasBH r n →
                   ColorHeight c n m →
                   HasBH (Node kv c l r) m

      blackenRoot-bh : ∀ (t : Tree)(n : ℕ) → HasBH t n → ∃ (λ (m : ℕ) → HasBH (blackenRoot t) m)
      blackenRoot-bh .Empty .1 HBH-Empty = _ , HBH-Empty
      blackenRoot-bh ._ m (HBH-Node prf prf₁ x) = _ , HBH-Node prf prf₁ CH-Black


    module BalanceTake1 where

      open BlackHeightTake2 -- here we get stuck due to balance overlapping equations.

      balance-bh : ∀ {l r : Tree}{c : Color}{kv : Key × Value}{n m : ℕ} →
                   HasBH l n → HasBH r n → ColorHeight c n m → HasBH (balance kv c l r) m
      balance-bh {(Node x Red a (Node y Red b c))} {r} {c'} {kv} {n} {m} hl hr ch = {!HBH-Node ? ? ?!}
      balance-bh hl hr ch = {!!}
