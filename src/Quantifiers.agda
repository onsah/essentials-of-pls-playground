module Quantifiers where
    import Relation.Binary.PropositionalEquality as Eq
    open Eq using (_≡_; refl; cong; sym)
    open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _∎; step-≡)
    open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _≤_)
    open import Relation.Nullary using (¬_)
    open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
    open import Data.Sum using (_⊎_; inj₁; inj₂)
    open import Isomorphism using (_≃_; extensionality; ∀-extensionality)
    open import Function using (_∘_)
    
    ∀-distrib-× : ∀ {A : Set} {B C : A → Set} →
        (∀ (x : A) → B x × C x) ≃ (∀ (x : A) → B x) × (∀ (x : A) → C x)
    ∀-distrib-× = 
        record { 
            to = λ BxCx → ⟨ (proj₁ ∘ BxCx) , (proj₂ ∘ BxCx) ⟩ ; 
            from = λ f a → ⟨ ((proj₁ f) a) , ((proj₂ f)  a) ⟩ ; 
            from∘to = λ x → refl ; 
            to∘from = λ y → refl 
        } 

    ⊎∀-implies-∀=⊎ : ∀ {A : Set} {B C : A → Set} →
        (∀ (x : A) → B x) ⊎ (∀ (x : A) → C x) → ∀ (x : A) → B x ⊎ C x
    ⊎∀-implies-∀=⊎ (inj₁ Bx) = inj₁ ∘ Bx 
    ⊎∀-implies-∀=⊎ (inj₂ Cx) = inj₂ ∘ Cx

    data Tri : Set where
        aa : Tri
        bb : Tri
        cc : Tri

    Tri-isomorphic-× : {B : Tri → Set} 
        → (∀ (x : Tri) → B x) ≃ (B aa × B bb × B cc)
    Tri-isomorphic-× = 
        record { 
            to = λ{ f → ⟨ (f aa) , ⟨ (f bb) , (f cc) ⟩ ⟩} ; 
            from = λ{ ⟨ Baa , _ ⟩ aa → Baa
                    ; ⟨ _ , ⟨ Bbb , _ ⟩ ⟩ bb → Bbb
                    ; ⟨ _ , ⟨ _ , Bcc ⟩ ⟩ cc → Bcc }; 
            from∘to = λ x → ∀-extensionality (λ{ aa → refl
                                               ; bb → refl
                                               ; cc → refl}) ; 
            to∘from = λ y → refl 
        }

    data Σ (A : Set) (B : A → Set) : Set where
        ⟨_,_⟩ : (x : A) → B x → Σ A B

    Σ-syntax = Σ
    infix 2 Σ-syntax
    syntax Σ-syntax A (λ x → Bx) = Σ[ x ∈ A ] Bx

    ∃ : ∀ {A : Set} (B : A → Set) → Set
    ∃ {A} B = Σ A B

    ∃-syntax = ∃
    syntax ∃-syntax (λ x → B) = ∃[ x ] B

    ∃-elim : ∀ {A : Set} {B : A → Set} {C : Set}
        → (∀ x → B x → C)
        → ∃[ x ] B x
            ---------------
        → C
    ∃-elim f ⟨ x , y ⟩ = f x y

    ∀∃-currying : ∀ {A : Set} {B : A → Set} {C : Set}
        → (∀ x → B x → C) ≃ (∃[ x ] B x → C)
    ∀∃-currying = 
        record { 
            to = λ{ f ⟨ x , y ⟩ → f x y } ; 
            from = λ{ f a Bx → f ⟨ a , Bx ⟩ } ; 
            from∘to = {!   !} ; 
            to∘from = {!   !}
        }
        
    ∃-distrib-⊎ : {A : Set} {B C : A → Set} 
        → ∃[ x ] (B x ⊎ C x) ≃ (∃[ x ] B x) ⊎ (∃[ x ] C x)
    ∃-distrib-⊎ = 
        record { 
            to = λ{  ⟨ a , inj₁ bₓ ⟩ → inj₁ ⟨ a , bₓ ⟩
                   ; ⟨ a , inj₂ cₓ ⟩ → inj₂ ⟨ a , cₓ ⟩ } ; 
            from = λ{ (inj₁ ⟨ a , bₓ ⟩) → ⟨ a , inj₁ bₓ ⟩
                    ; (inj₂ ⟨ a , cₓ ⟩) → ⟨ a , inj₂ cₓ ⟩ } ; 
            from∘to = λ{ ⟨ a , inj₁ x ⟩ → refl
                       ; ⟨ a , inj₂ y ⟩ → refl } ; 
            to∘from = λ{ (inj₁ ⟨ a , bₓ ⟩) → refl
                       ; (inj₂ ⟨ a , cₓ ⟩) → refl } 
        }

    ∃x-implies-x∃ : ∀ {A : Set} {B C : A → Set} →
        ∃[ x ] (B x × C x) → (∃[ x ] B x) × (∃[ x ] C x)
    ∃x-implies-x∃ ⟨ a , ⟨ bₐ , cₐ ⟩ ⟩ = ⟨ ⟨ a , bₐ ⟩ , ⟨ a , cₐ ⟩ ⟩

    ∃x-isomorphism-⊎ : ∀ {B : Tri → Set}
        → ∃[ x ] B x ≃ (B aa ⊎ B bb ⊎ B cc) 
    ∃x-isomorphism-⊎ = 
        record { 
            to = λ{ ⟨ aa , ba ⟩ → inj₁ ba
                  ; ⟨ bb , bx ⟩ → inj₂ (inj₁ bx)
                  ; ⟨ cc , bc ⟩ → inj₂ (inj₂ bc) } ; 
            from = λ{ (inj₁ ba) → ⟨ aa , ba ⟩
                    ; (inj₂ (inj₁ bx)) → ⟨ bb , bx ⟩
                    ; (inj₂ (inj₂ bc)) → ⟨ cc , bc ⟩ } ; 
            from∘to = λ{ ⟨ aa , b_a ⟩ → refl
                       ; ⟨ bb , b_b ⟩ → refl
                       ; ⟨ cc , b_c ⟩ → refl } ; 
            to∘from = λ{ (inj₁ b_a) → refl
                       ; (inj₂ (inj₁ b_b)) → refl
                       ; (inj₂ (inj₂ b_c)) → refl } 
        }

    open import Relations using (even; odd)

    even-∃ : ∀ {n : ℕ} → even n → ∃[ m ] (    2 * m ≡ n)
    odd-∃  : ∀ {n : ℕ} →  odd n → ∃[ m ] ((2 * m) + 1 ≡ n)  

    open import Data.Nat.Properties using (+-comm; +-identityˡ; +-assoc; +-suc)

    postulate
        +-left-trans : {n o : ℕ} (m : ℕ)
            → n ≡ o
            → m + n ≡ m + o
            

    even-∃ even.zero = ⟨ zero , refl ⟩
    even-∃ {n = n} (even.suc o) with odd-∃ o
    ... | ⟨ m , m+m+1≡n ⟩ = 
        let p = begin 
                    n 
                ≡⟨ sym (cong suc m+m+1≡n) ⟩ 
                    suc (m + (m + 0) + 1)
                ≡⟨ cong suc (+-assoc m (m + 0) 1) ⟩
                    suc (m + ((m + 0) + 1))
                ≡⟨ cong suc (+-left-trans m (+-comm (m + 0) 1)) ⟩ 
                    suc (m + (1 + (m + 0)))
                ≡⟨⟩
                    suc (m + (suc (0 + (m + 0))))
                ≡⟨⟩
                    suc (m + (suc (m + 0)))
                ∎
        in
        ⟨ suc m  , sym p ⟩
    odd-∃ {n = n} (odd.suc even-n) with even-∃ even-n
    ... | ⟨ m , m+m+0=n ⟩ = 
        let p = begin
                    m + (m + 0) + 1
                ≡⟨ +-assoc m (m + 0) 1 ⟩ 
                    m + ((m + 0) + 1)
                ≡⟨ +-left-trans m (+-comm (m + 0) 1) ⟩
                    m + (1 + (m + 0))
                ≡⟨⟩
                    m + (0 + suc (m + 0))
                ≡⟨⟩
                    m + (suc (m + 0))
                ≡⟨ +-suc m (m + 0) ⟩
                    suc (m + (m + 0))
                ≡⟨ cong suc m+m+0=n ⟩
                    n
                ∎
        in
        ⟨ m , p ⟩

    open import Data.Nat using (s≤s; z≤n)
    open import Data.Nat.Properties using (≤-refl; suc-injective)

    ∃-+-≤ : {y z : ℕ} 
        → ∃[ x ] (x + y ≡ z) 
        → y ≤ z
    ∃-+-≤ ⟨ zero , refl ⟩ = ≤-refl
    ∃-+-≤ {y = zero} {z = z} ⟨ x , x+y≡z ⟩ = z≤n
    ∃-+-≤ {y = suc y} {z = suc z} ⟨ x , x+y≡z ⟩ = s≤s 
        let sucx+y≡sucz = begin 
                    suc (x + y)
                ≡⟨ sym (+-suc x y) ⟩
                    x + suc y
                ≡⟨ x+y≡z ⟩
                    suc z
                ∎
        in
        (∃-+-≤ ⟨ x , suc-injective sucx+y≡sucz ⟩)

    ¬∃≃∀¬ : ∀ {A : Set} {B : A → Set}
        → (¬ ∃[ x ] B x) ≃ ∀ x → ¬ B x
    ¬∃≃∀¬ =
        record
            { to      =  λ{ ¬∃ab a b → ¬∃ab ⟨ a , b ⟩ }
            ; from    =  λ{ ∀a→¬b ⟨ a , b ⟩ → ∀a→¬b a b }
            ; from∘to =  λ{ ¬∃xy → extensionality λ{ ⟨ x , y ⟩ → refl } }
            ; to∘from =  λ{ ∀¬xy → refl }
            }

    ∃¬-implies-¬∀ : ∀ {A : Set} {B : A → Set}
        → ∃[ x ] (¬ B x)
        --------------
        → ¬ (∀ x → B x)
    ∃¬-implies-¬∀ ⟨ a , ¬b ⟩ a→b = ¬b (a→b a)
  