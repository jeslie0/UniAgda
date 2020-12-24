-- Perform: M-x load-file RET to-Σ-editor-tactic.el
--
--------------------------------------------------------------------------------
-- Preamble
module UniAgda.experimental.test where

open import UniAgda.core.CORE public

infix -666 Σ∶•
syntax Σ∶• A (λ x → B) = Σ x ∶ A • B
--------------------------------------------------------------------------------
{- Select the following record and press “C-x C-t” -}

record R (A : Set) (n : ℕ) : Set where

  Alias = A

  id-1 : Set → Set
  id-1 X = X

  field
    x : id Alias

  m : ℕ
  m = n

  field
    y : m ≡ n
    z : A

  more : Set → ℕ
  more = λ _ → n

--------------------------------------------------------------------------------
{- Now press “C-y” to paste in the derived Σ-version, as shown below -}
--------------------------------------------------------------------------------
{- Configuration

In the Lisp file, at the very top:

➬ Change the ‘Σ-naming-format’ string to alter how the Σ-variant should be named.

➬ Change the ‘record→Σ-coe-format’ string to alter how the record-to-Σ coercision
  should be named.

Likewise for the to-from bijection proofs.
-}
