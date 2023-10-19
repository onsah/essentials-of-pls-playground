module Naturals where
    import Relation.Binary.PropositionalEquality as Eq
    import Data.Nat as Nat
    
    open Eq using (_≡_; refl)
    open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _∎)
    open Nat using (ℕ; suc; zero)

    {- seven : ℕ
    seven = suc (suc (suc (suc (suc (suc (suc zero)))))) -}
    
    -- addition
    infixl 6 _+_
    _+_ : ℕ → ℕ → ℕ
    zero + n = n
    suc m + n = suc (m + n)
    {- zero + n = n
    (suc m) + n = suc (m + n) -}

    _ : 2 + 3 ≡ 5
    _ = 
        begin 
            2 + 3
        ≡⟨⟩
            (suc (suc zero)) + (suc (suc (suc zero)))
        ≡⟨⟩
            suc ((suc zero) + (suc (suc (suc zero))))
        ≡⟨⟩
            suc (suc (zero + (suc (suc (suc zero)))))
        ≡⟨⟩
            suc (suc (suc (suc (suc zero))))
        ≡⟨⟩
            5
        ∎

    _ : 3 + 4 ≡ 7
    _ = 
        begin
            3 + 4
        ≡⟨⟩ 
            suc (2 + 4)
        ≡⟨⟩
            suc (suc (1 + 4))
        ≡⟨⟩
            suc (suc (suc (0 + 4)))
        ≡⟨⟩
            suc (suc (suc 4))
        ≡⟨⟩ 
            7
        ∎

    -- multiplication
    infixl 7 _*_
    _*_ : ℕ → ℕ → ℕ
    zero * n = zero
    (suc m) * n = n + (m * n)

    _ : 5 * 2 ≡ 10
    _ = refl

    _ : 3 * 4 ≡ 12
    _ = 
        begin
            3 * 4
        ≡⟨⟩
            (suc 2) * 4
        ≡⟨⟩
            4 + (2 * 4)
        ≡⟨⟩
            4 + ((suc 1) * 4)
        ≡⟨⟩
            4 + (4 + (1 * 4))
        ≡⟨⟩
            4 + (4 + ((suc 0) * 4))
        ≡⟨⟩
            4 + (4 + (4 + (0 * 4)))
        ≡⟨⟩
            4 + (4 + (4 + 0))
        ≡⟨⟩
            12
        ∎

    _^_ : ℕ → ℕ → ℕ
    m ^ 0 = 1
    m ^ (suc n) = m * (m ^ n)

    _ : 3 ^ 4 ≡ 81
    _ = 
        begin
            3 ^ 4
        ≡⟨⟩
            3 * (3 ^ 3)
        ≡⟨⟩
            3 * (3 * (3 ^ 2))
        ≡⟨⟩
            3 * (3 * (3 * (3 ^ 1)))
        ≡⟨⟩
            3 * (3 * (3 * (3 * (3 ^ 0))))
        ≡⟨⟩
            3 * (3 * (3 * (3 * 1)))
        ≡⟨⟩
            81
        ∎

    infixl 6 _∸_
    _∸_ : ℕ → ℕ → ℕ
    m ∸ zero = m
    zero ∸ (suc n) = zero
    (suc m) ∸ (suc n) = m ∸ n

    _ : 5 ∸ 3 ≡ 2
    _ = 
        begin
            5 ∸ 3
        ≡⟨⟩ 
            (suc 4) ∸ (suc 2)
        ≡⟨⟩
            4 ∸ 2
        ≡⟨⟩
            (suc 3) ∸ (suc 1)
        ≡⟨⟩
            3 ∸ 1
        ≡⟨⟩
            (suc 2) ∸ (suc 0)
        ≡⟨⟩
            2 ∸ 0
        ≡⟨⟩
            2
        ∎

    _ : 3 ∸ 5 ≡ 0
    _ = 
        begin
            3 ∸ 5
        ≡⟨⟩
            (suc 2) ∸ (suc 4)
        ≡⟨⟩
            2 ∸ 4
        ≡⟨⟩
            (suc 1) ∸ (suc 3)
        ≡⟨⟩
            1 ∸ 3
        ≡⟨⟩
            (suc 0) ∸ (suc 2)
        ≡⟨⟩
            0 ∸ 2
        ≡⟨⟩
            0
        ∎
        