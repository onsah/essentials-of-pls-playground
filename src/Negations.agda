module Negations where
    open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
    open import Data.Nat using (ℕ; zero; suc; _<_; z≤n; s≤s; _>_)
    open import Data.Nat.Properties using (suc-injective)
    open import Data.Empty using (⊥; ⊥-elim)
    open import Data.Sum using (_⊎_; inj₁; inj₂)
    open import Data.Product using (_×_; _,_)
    open import Isomorphism using (_≃_; extensionality)
    
    ¬_ : Set → Set
    ¬ A = A → ⊥

    ¬-elim : {A : Set}
        → ¬ A
        → A
        → ⊥
    ¬-elim ¬a a = ¬a a

    ¬¬-intro : {A : Set}
        → A
        → ¬ ¬ A
    ¬¬-intro a = λ ¬a → ¬a a

    ¬¬¬-elim : {A : Set}
        → ¬ ¬ ¬ A
        → ¬ A
    ¬¬¬-elim ¬¬¬a = λ a → ¬¬¬a (¬¬-intro a)

    contraposition : {A B : Set}
        → (A → B)
        → (¬ B → ¬ A)
    contraposition a→b = λ ¬b a → ¬b (a→b a)

    _≢_ : { A : Set } → A → A → Set
    x ≢ y = ¬ (x ≡ y)

    id : ⊥ → ⊥
    id x = x

    id′ : ⊥ → ⊥
    id′ ()

    id≡id′ : id ≡ id′
    id≡id′ = extensionality λ()

    assimilation : {A : Set} (¬x ¬x′ : ¬ A) → ¬x ≡ ¬x′
    assimilation ¬x ¬x′ = extensionality λ x → ⊥-elim (¬x′ x)

    <-suc-elim : {n : ℕ} 
        → suc n < suc n
        → n < n
    <-suc-elim (s≤s n<n) = n<n

    <-irreflexive : (n : ℕ) → ¬ (n < n)
    <-irreflexive zero = λ()
    <-irreflexive (suc n) sucn<sucn = <-irreflexive n (<-suc-elim sucn<sucn)

    data Trichotomy (m n : ℕ) : Set where
        first :
            m < n
            → ¬ (m ≡ n)
            → ¬ (m > n)
            → Trichotomy m n

        second :
            ¬ (m < n)
            → m ≡ n
            → ¬ (m > n)
            → Trichotomy m n

        third :
            ¬ (m < n)
            → ¬ (m ≡ n)
            → m > n
            → Trichotomy m n

    suc-trichotomy : {m n : ℕ}
        → Trichotomy m n
        → Trichotomy (suc m) (suc n)
    suc-trichotomy (first m<n ¬m≡n ¬m>n) = 
        first 
            (s≤s m<n) 
            (λ{ refl → ¬m≡n refl }) 
            (λ{ (s≤s m>n) → ¬m>n m>n })
    suc-trichotomy (second ¬m<n m≡n ¬m>n) = 
        second 
            (λ{ (s≤s m<n) → ¬m<n m<n}) 
            (cong suc m≡n) 
            (λ{ (s≤s m>n) → ¬m>n m>n})
    suc-trichotomy (third ¬m<n ¬m≡n m>n) = 
        third 
            (λ{ (s≤s m<n) → ¬m<n m<n}) 
            (λ{ refl → ¬m≡n refl }) 
            (s≤s m>n)

    trichotomy : (m n : ℕ) → Trichotomy m n
    trichotomy zero zero = second 
        (<-irreflexive zero) 
        refl 
        (<-irreflexive zero)
    trichotomy zero (suc n) = 
        first 
            (s≤s z≤n) 
            (λ()) 
            (λ())
    trichotomy (suc m) zero = 
        third 
            (λ()) 
            (λ()) 
            (s≤s z≤n)
    trichotomy (suc m) (suc n) = suc-trichotomy (trichotomy m n)

    ⊎-dual-x : {A B : Set}
        → ¬ (A ⊎ B) ≃ (¬ A) × (¬ B)
    ⊎-dual-x = 
        record { 
            to = λ ¬a⊎b → (λ a → ¬a⊎b (inj₁ a)) , λ b → ¬a⊎b (inj₂ b) ; 
            from = λ{ (¬a , _) (inj₁ a) → ¬a a
                    ; (_ , ¬b) (inj₂ b) → ¬b  b }; 
            from∘to = λ{ ¬a⊎b 
                → extensionality λ  { (inj₁ a) → refl
                                    ; (inj₂ b) → refl}}; 
            to∘from = λ{ (¬a , ¬b) → refl} 
        }

    em-irrefutable : {A : Set} → ¬ ¬ (A ⊎ ¬ A)
    em-irrefutable k = k (inj₂ λ{ a → k (inj₁ a) })
  