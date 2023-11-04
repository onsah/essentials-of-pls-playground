module Relations where
    import Relation.Binary.PropositionalEquality as Eq
    import Data.Nat as Nat
    import Data.Nat.Properties as Properties
    
    open Eq using (_≡_; refl; cong)
    open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _∎)
    open Nat using (ℕ; suc; zero; _+_)
    open Properties using (+-comm)

    module first-try where
        data _≤_ : ℕ -> ℕ -> Set where
            z≤n : ∀ (n : ℕ) -> zero ≤ n
            s≤s : ∀ (m n : ℕ) -> m ≤ n -> suc m ≤ suc n

        _ : 3 ≤ 5
        _ = s≤s 2 4 (s≤s 1 3 (s≤s 0 2 (z≤n 2)))

    data _≤_ : ℕ -> ℕ -> Set where
        z≤n : {n : ℕ} -> 
            zero ≤ n
        s≤s : {m n : ℕ} -> 
            m ≤ n ->
            suc m ≤ suc n
    _ : 3 ≤ 5
    _ = s≤s (s≤s (s≤s z≤n))

    invert-suc-≤ : ∀ {m n} -> suc m ≤ suc n -> m ≤ n
    invert-suc-≤ (s≤s sm≤sn) = sm≤sn

    invert-zero-≤ : {m : ℕ} -> m ≤ zero -> m ≡ zero
    invert-zero-≤ z≤n = refl

    ≤-refl : {n : ℕ} → n ≤ n
    ≤-refl {zero} = z≤n
    ≤-refl {suc n} = s≤s ≤-refl

    module first-trans where
        ≤-trans : { m n p : ℕ } → m ≤ n → n ≤ p → m ≤ p  
        ≤-trans z≤n z≤n = z≤n
        ≤-trans z≤n (s≤s n≤p) = z≤n
        ≤-trans (s≤s m≤n) (s≤s n≤p) = s≤s (≤-trans m≤n n≤p)

    ≤-trans : { m n p : ℕ } → m ≤ n → n ≤ p → m ≤ p  
    ≤-trans z≤n n≤p = z≤n
    ≤-trans (s≤s m≤n) (s≤s n≤p) = s≤s (≤-trans m≤n n≤p)
   
    ≤-antisym : {m n : ℕ} -> m ≤ n → n ≤ m → m ≡ n
    ≤-antisym z≤n z≤n = refl 
    ≤-antisym (s≤s m≤n) (s≤s n≤m) = cong suc (≤-antisym m≤n n≤m)

    data Total : ℕ → ℕ → Set where
        forward : {m n : ℕ} → m ≤ n → Total m n
        
        flipped : {m n : ℕ} → n ≤ m → Total m n 

    ≤-total : (m n : ℕ) → Total m n
    ≤-total zero n = forward z≤n 
    ≤-total (suc m) zero = flipped z≤n 
    ≤-total (suc m) (suc n) with (≤-total m n)
    ... | forward m≤n = forward (s≤s m≤n) 
    ... | flipped n≤m = flipped (s≤s n≤m)

    +-monoʳ-≤ : (m p q : ℕ) → p ≤ q → (m + p) ≤ (m + q)
    +-monoʳ-≤ zero p q p≤q = p≤q 
    +-monoʳ-≤ (suc m) p q p≤q = s≤s (+-monoʳ-≤ m p q p≤q)

    +-monoˡ-≤ : (m n p : ℕ) → m ≤ n → (m + p) ≤ (n + p)
    +-monoˡ-≤ m n p m≤n rewrite +-comm m p | +-comm n p = +-monoʳ-≤ p m n m≤n

    +-mono-≤ : {m n p q : ℕ} → m ≤ n → p ≤ q -> (m + p) ≤ (n + q)
    +-mono-≤ {m} {n} {p} {q} m≤n p≤q = ≤-trans (+-monoˡ-≤ m n p m≤n) (+-monoʳ-≤ n p q p≤q)

    data even : ℕ → Set
    data odd : ℕ → Set

    data even where
        zero : even zero

        suc : {n : ℕ} → odd n → even (suc n)
        
    data odd where
        suc : {n : ℕ} → even n → odd (suc n)

    _ : even 4
    _ = suc (suc (suc (suc zero)))

    e+e=e : {m n : ℕ} → even m → even n → even (m + n)
    o+e=o : {m n : ℕ} → odd m → even n → odd (m + n)
    
    e+e=e zero en = en
    e+e=e (suc om) en = suc (o+e=o om en)

    o+e=o (suc em) en = suc (e+e=e em en)

    e+o=o : {m n : ℕ} → even m → odd n → odd (m + n)
    e+o=o {m} {n} em on rewrite +-comm m n = o+e=o on em
 