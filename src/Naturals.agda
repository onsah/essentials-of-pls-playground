module Naturals where
    import Relation.Binary.PropositionalEquality as Eq
    import Data.Nat as Nat
    
    open Eq using (_≡_; refl)
    open Nat using (ℕ; suc; zero)

    {- seven : ℕ
    seven = suc (suc (suc (suc (suc (suc (suc zero)))))) -}
    
    _+_ : ℕ → ℕ → ℕ
    zero + n = n
    (suc m) + n = suc (m + n)

    _ : suc zero ≡ 1
    _ = refl
