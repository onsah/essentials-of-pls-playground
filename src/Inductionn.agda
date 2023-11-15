module Inductionn where
    import Relation.Binary.PropositionalEquality as Eq

    open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans)
    open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _∎; step-≡)
    open import Data.Nat using (ℕ; _+_; zero; suc; _*_; _∸_)

    +-assoc : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
    +-assoc ℕ.zero n p = refl 
    +-assoc (ℕ.suc m) n p = cong ℕ.suc (+-assoc m n p)

    +-identityʳ : ∀ (m : ℕ) → m + zero ≡ m
    +-identityʳ zero = refl
    +-identityʳ (ℕ.suc m) rewrite +-identityʳ m = refl
    
    +-suc : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)
    +-suc zero n = refl
    +-suc (suc m) n rewrite +-suc m n = refl

    +-comm : ∀ (m n : ℕ) → m + n ≡ n + m
    +-comm ℕ.zero n = sym (+-identityʳ n)
    +-comm (ℕ.suc m) n = trans (cong suc (+-comm m n)) (sym (+-suc n m))

    +-swap : ∀ (m n p : ℕ) → m + (n + p) ≡ n + (m + p)
    +-swap zero n p = refl
    +-swap (suc m) n p = trans (cong suc (+-swap m n p)) (sym (+-suc n (m + p)))

    postulate
        +-transʳ : (m : ℕ) {n p : ℕ}
            → n ≡ p 
            → m + n ≡ m + p

    *-distrib-+ : (m n p : ℕ) → (m + n) * p ≡ (m * p) + (n * p)
    *-distrib-+ zero n p = refl
    *-distrib-+ (suc m) n p = trans (+-transʳ p ((*-distrib-+ m n p))) (sym (+-assoc p (m * p) (n * p)))

    *-assoc : (m n p : ℕ) → (m * n) * p ≡ m * (n * p)
    *-assoc zero n p = refl
    *-assoc (suc m) n p = trans (*-distrib-+ n (m * n) p) (+-transʳ (n * p) (*-assoc m n p))

    *-identityʳ : (m : ℕ) → m * zero ≡ zero
    *-identityʳ zero = refl
    *-identityʳ (suc m) = *-identityʳ m

    *-suc : (m n : ℕ) → m * suc n ≡ m + (m * n)
    *-suc zero n = sym refl
    *-suc (suc m) n = cong suc (trans (+-transʳ n (*-suc m n)) (+-swap n m (m * n)))

    *-comm : (m n : ℕ) → m * n ≡ n * m
    *-comm zero n = sym (*-identityʳ n)
    *-comm (suc m) n = trans (+-transʳ n (*-comm m n)) (sym (*-suc n m))

    0∸n≡0 : (n : ℕ) → zero ∸ n ≡ zero
    0∸n≡0 zero = refl
    0∸n≡0 (suc n) = refl

    ∸-+-assoc : (m n p : ℕ) → m ∸ n ∸ p ≡ m ∸ (n + p)
    ∸-+-assoc zero n p rewrite (0∸n≡0 n) | (0∸n≡0 (n + p)) = 0∸n≡0 p
    ∸-+-assoc (suc m) zero p = refl
    ∸-+-assoc (suc m) (suc n) p = ∸-+-assoc m n p
  