module plfa.part1.Naturals where

import Relation.Binary.PropositionalEquality as Eq
open import Data.Nat
open import Data.Nat.Properties

open Eq using (_≡_; refl)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _∎)


data Bin : Set where
  ⟨⟩ : Bin
  _O : Bin → Bin
  _I : Bin → Bin

inc : Bin → Bin
inc ⟨⟩ = ⟨⟩ I
inc (b O) = b I
inc (b I) = (inc b) O

to : ℕ → Bin
to zero = ⟨⟩
to (suc n) = inc (to n)

from : Bin → ℕ
from ⟨⟩ = 0
from (b O) = 2 * from b
from (b I) = 1 + 2 * from b

from-inc-suc : {b : Bin} → from (inc b) ≡ suc (from b)
from-inc-suc {⟨⟩} = refl
from-inc-suc {b O} = refl
from-inc-suc {b I}
  rewrite from-inc-suc {b}
        | +-identityʳ (from b)
        | +-suc (from b) (from b) = refl

from-to : (n : ℕ) → from (to n) ≡ n
from-to zero = refl
from-to (suc n)
  rewrite from-inc-suc {to n}
        | from-to n = refl


-- to (from b) ≡ b is not true
-- since the presence of to (from (⟨⟩ O O O)) = ⟨⟩
