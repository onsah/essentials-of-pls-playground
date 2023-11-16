import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; cong-app; sym; trans)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-comm)

module Isomorphism where
    _∘_ : ∀ {A B C : Set} → (B → C) → (A → B) → (A → C)
    g ∘ f = λ x → g (f x)

    postulate
        extentionality : ∀ {A B : Set} {f g : A → B}
            → (∀ (x : A) → f x ≡ g x)
            → f ≡ g
        
        +-identityʳ : ∀ (m : ℕ) → m + zero ≡ m

        +-suc : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)

    _+′_ : ℕ → ℕ → ℕ
    m +′ zero = m
    m +′ suc n = suc (m +′ n)

    same-app : (m n : ℕ) → m +′ n ≡ m + n
    same-app m zero = sym (+-identityʳ m)
    same-app m (suc n) rewrite (+-comm m n) = 
        trans (cong suc (same-app m n)) (sym (+-suc m n))

    same : _+′_ ≡ _+_
    same = extentionality ((λ m → extentionality (λ n → same-app m n)))

    postulate
        ∀-extensionality : ∀ {A : Set} {B : A → Set} {f g : ∀(x : A) → B x}
            → (∀ (x : A) → f x ≡ g x)
            -----------------------
            → f ≡ g
 
    infix 0 _≃_
    record _≃_ (A B : Set) : Set where
        field
            to      : A → B
            from    : B → A
            from∘to : ∀ (x : A) → from (to x) ≡ x
            to∘from : ∀ (y : B) → to (from y) ≡ y
    open _≃_
    
    ≃-refl : {A : Set} → A ≃ A
    ≃-refl = 
        record { 
            to = λ x → x ; 
            from = λ y → y ; 
            from∘to = λ x → refl ; 
            to∘from = λ y → refl
        }

    ≃-sym : {A B : Set}
        → A ≃ B
        → B ≃ A

    ≃-sym a≃b = 
        record { 
            to = from a≃b ; 
            from = to a≃b ; 
            from∘to = to∘from a≃b ; 
            to∘from = from∘to a≃b 
        }

    ≃-trans : {A B C : Set}
        → A ≃ B
        → B ≃ C
        → A ≃ C

    ≃-trans a≃b b≃c = 
        record { 
            to = (to b≃c) ∘ (to a≃b) ; 
            from = (from a≃b) ∘ (from b≃c) ; 
            from∘to = λ a → 
                begin 
                    (from a≃b ∘ from b≃c) ((to b≃c ∘ to a≃b) a) 
                ≡⟨⟩
                    from a≃b (from b≃c (to b≃c ((to a≃b) a))) 
                ≡⟨ cong (from a≃b) (from∘to b≃c ((to a≃b) a)) ⟩ 
                    from a≃b (to a≃b a)
                ≡⟨ from∘to a≃b a ⟩
                    a 
                ∎; 
            to∘from = λ c → 
            begin 
                (to b≃c ∘ to a≃b) ((from a≃b ∘ from b≃c) c) 
            ≡⟨⟩ 
                to b≃c (to a≃b (from a≃b (from b≃c c))) 
            ≡⟨ cong (to b≃c) (to∘from a≃b (from b≃c c)) ⟩ 
                to b≃c (from b≃c c) 
            ≡⟨ to∘from b≃c c ⟩ 
                c
            ∎ 
        } 

    module ≃-Reasoning where

        infix  1 ≃-begin_
        infixr 2 _≃⟨_⟩_
        infix  3 _≃-∎

        ≃-begin_ : {A B : Set}
            → A ≃ B
            → A ≃ B
        ≃-begin A≃B = A≃B

        _≃⟨_⟩_ : ∀ (A : Set) {B C : Set}
            → A ≃ B
            → B ≃ C
            -----
            → A ≃ C
        A ≃⟨ A≃B ⟩ B≃C = ≃-trans A≃B B≃C

        _≃-∎ : ∀ (A : Set)
            -----
            → A ≃ A
        A ≃-∎ = ≃-refl

    open ≃-Reasoning

    infix 0 _≲_
    record _≲_ (A B : Set) : Set where
        field
            to      : A → B
            from    : B → A
            from∘to : (x : A) → from (to x) ≡ x
    open _≲_

    identity : {A : Set} → A → A
    identity = λ x → x

    ≲-refl : {A : Set} → A ≲ A
    ≲-refl = 
        record { 
            to = identity ; 
            from = identity ; 
            from∘to = λ x → 
                begin 
                    identity (identity x) 
                ≡⟨⟩ 
                    (identity x) 
                ≡⟨⟩ 
                    x 
                ∎
        }

    ≲-trans : {A B C : Set} 
        → A ≲ B 
        → B ≲ C
        → A ≲ C
        
    ≲-trans a≲b b≲c = 
        record { 
            to = (to b≲c) ∘ (to a≲b) ; 
            from = (from a≲b) ∘ (from b≲c) ; 
            from∘to = λ a → 
                begin 
                    (from a≲b ∘ from b≲c) ((to b≲c ∘ to a≲b) a) 
                ≡⟨⟩ 
                    (from a≲b (from b≲c (to b≲c (to a≲b a))))
                ≡⟨ cong (from a≲b) (from∘to b≲c (to a≲b a)) ⟩ 
                    from a≲b (to a≲b a)
                ≡⟨ from∘to a≲b a ⟩ 
                    a 
                ∎ 
        }

    ≲-antisym : {A B : Set}
        → (a≲b : A ≲ B)
        → (b≲a : B ≲ A)
        → to a≲b ≡ from b≲a
        → from a≲b ≡ to b≲a
        → A ≃ B

    ≲-antisym a≲b b≲a to≡from from≡to = 
        record { 
            to = to a≲b ; 
            from = from a≲b ; 
            from∘to = from∘to a≲b ; 
            to∘from = λ b → 
                begin 
                    to a≲b (from a≲b b) 
                ≡⟨ cong (to a≲b) (cong-app from≡to b) ⟩ 
                    to a≲b (to b≲a b) 
                ≡⟨ cong-app to≡from (to b≲a b) ⟩ 
                    from b≲a (to b≲a b) 
                ≡⟨ from∘to b≲a b ⟩ 
                    b
                ∎
        }
    
    module ≲-Reasoning where

        infix  1 ≲-begin_
        infixr 2 _≲⟨_⟩_
        infix  3 _≲-∎

        ≲-begin_ : ∀ {A B : Set}
            → A ≲ B
            -----
            → A ≲ B
        ≲-begin A≲B = A≲B

        _≲⟨_⟩_ : ∀ (A : Set) {B C : Set}
            → A ≲ B
            → B ≲ C
            -----
            → A ≲ C
        A ≲⟨ A≲B ⟩ B≲C = ≲-trans A≲B B≲C

        _≲-∎ : ∀ (A : Set)
            -----
            → A ≲ A
        A ≲-∎ = ≲-refl

    open ≲-Reasoning

    ≃-implies-≲ : ∀ {A B : Set}
        → A ≃ B
        -----
        → A ≲ B

    ≃-implies-≲ a≃b = 
        record { 
            to = to a≃b ; 
            from = from a≃b ; 
            from∘to = from∘to a≃b 
        }

    record _⇔_ (A B : Set) : Set where
      field
        to   : A → B
        from : B → A

    open _⇔_

    ⇔-refl : {A : Set} → A ⇔ A
    ⇔-refl = 
      record { 
        to = identity ; 
        from = identity 
      }

    ⇔-sym : {A B : Set} 
      → A ⇔ B
      → B ⇔ A

    ⇔-sym a⇔b = 
      record { 
        to = from a⇔b ; 
        from = to a⇔b 
      }

    ⇔-trans : {A B C : Set}
      → A ⇔ B
      → B ⇔ C
      → A ⇔ C

    ⇔-trans a⇔b b⇔c = 
      record { 
        to = (to b⇔c) ∘ (to a⇔b) ; 
        from = (from a⇔b) ∘ (from b⇔c) 
      }

    open import Data.Nat.Binary

    _ : ℕᵇ
    _ = 2[1+ ℕᵇ.zero ]
