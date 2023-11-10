module Equality where
    data _≡_ {A : Set} (x : A) : A → Set where
        refl : x ≡ x

    infix 4 _≡_

    sym : ∀ {A : Set} {x y : A}
        → x ≡ y
        → y ≡ x

    sym refl = refl

    trans : ∀ {A : Set} {x y z : A}
        → x ≡ y
        → y ≡ z
        → x ≡ z

    trans refl refl = refl

    cong : ∀ {A B : Set} {x y : A} (f : A → B)
        → x ≡ y
        → f x ≡ f y

    cong f refl = refl

    cong₂ : ∀ {A B C : Set} {u x : A} {v y : B} (f : A → B → C)
        → u ≡ x
        → v ≡ y
        → f u v ≡ f x y

    cong₂ f refl refl = refl
    -- cong₂ {_} {_} {_} {u} {_} {_} {y} f u≡x v≡y = trans (cong (f u) v≡y) (cong (λ u → f u y) u≡x)

    cong-app : ∀ {A B : Set} {f g : A → B}
        → f ≡ g
        → ∀ (x : A) → f x ≡ g x
    
    cong-app refl x = refl

    Pred : Set → Set₁
    Pred A = A → Set

    subst : ∀ {A : Set} {x y : A} (P : Pred A)
        → x ≡ y
        → P x → P y

    subst p refl Px = Px

    Rel : Set → Set → Set₁
    Rel A B = A → B → Set

    subst₂ : ∀ {A B : Set} {x₁ x₂ : A} {y₁ y₂ : B}
        → (R : Rel A B)
        → x₁ ≡ x₂
        → y₁ ≡ y₂
        → R x₁ y₁ → R x₂ y₂

    subst₂ R refl refl R1 = R1

    subst-cong : ∀ {A B : Set} {x y : A}
        → (f : A → B)
        → (P : Pred B)
        → (x≡y : x ≡ y)
        → (Px : P (f x))
        → subst (λ x → P (f x)) x≡y Px ≡ subst P (cong f x≡y) Px
        
    subst-cong f P refl Px = refl

    module ≡-Reasoning {A : Set} where

        infix  1 begin_
        infixr 2 _≡⟨⟩_ step-≡
        infix  3 _∎

        begin_ : ∀ {x y : A}
            → x ≡ y
            -----
            → x ≡ y
        begin x≡y  =  x≡y

        _≡⟨⟩_ : ∀ (x : A) {y : A}
            → x ≡ y
            -----
            → x ≡ y
        x ≡⟨⟩ x≡y  =  x≡y

        step-≡ : ∀ (x {y z} : A) → y ≡ z → x ≡ y → x ≡ z
        step-≡ x y≡z x≡y  =  trans x≡y y≡z

        syntax step-≡ x y≡z x≡y  =  x ≡⟨  x≡y ⟩ y≡z

        _∎ : ∀ (x : A)
            -----
            → x ≡ x
        x ∎  =  refl

    module ≡-Reasoning-exercises where
        open ≡-Reasoning

        trans' : ∀ {A : Set} {x y z : A}
            → x ≡ y
            → y ≡ z
            → x ≡ z

        trans' {x = x} {y = y} {z = z} x≡y y≡z = 
            begin 
                x 
            ≡⟨ x≡y ⟩
                y
            ≡⟨ y≡z ⟩ 
                z
            ∎

    
    import Data.Nat as Nat
    open Nat using (ℕ; suc; zero; _+_)

    data _≤_ : ℕ -> ℕ -> Set where
        z≤n : {n : ℕ} -> 
            zero ≤ n
        s≤s : {m n : ℕ} -> 
            m ≤ n ->
            suc m ≤ suc n

    postulate 
        ≤-trans : { m n p : ℕ } → m ≤ n → n ≤ p → m ≤ p
        ≤-refl : {n : ℕ} → n ≤ n

    module ≤-Reasoning where
        infix  1 begin_
        infixr 2 _≤⟨⟩_ _≤⟨_⟩_ 
        infix  3 _∎

        begin_ : ∀ {x y : ℕ}
            → x ≤ y
            → x ≤ y
            
        begin_ x≤y = x≤y

        _≤⟨⟩_ : (x : ℕ) {y : ℕ}
            → x ≤ y
            → x ≤ y
        
        x ≤⟨⟩ x≤y = x≤y

        _≤⟨_⟩_ : (x {y z} : ℕ) → x ≤ y → y ≤ z → x ≤ z
        x ≤⟨ x≤y ⟩ y≤z = ≤-trans x≤y y≤z

        _∎ : (x : ℕ)
            → x ≤ x
        x ∎ = ≤-refl

    open ≤-Reasoning

    postulate
        +-monoʳ-≤ : (m p q : ℕ) → p ≤ q → (m + p) ≤ (m + q)
        +-monoˡ-≤ : (m n p : ℕ) → m ≤ n → (m + p) ≤ (n + p)

    +-mono-≤ : {m n p q : ℕ} → m ≤ n → p ≤ q -> (m + p) ≤ (n + q)
    +-mono-≤ {m} {n} {p} {q} m≤n p≤q = 
        begin 
            (m + p)
        ≤⟨ +-monoˡ-≤ m n p m≤n ⟩
            (n + p)
        ≤⟨ +-monoʳ-≤ n p q p≤q ⟩ 
            (n + q)
        ∎