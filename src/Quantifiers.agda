module Quantifiers where
    import Relation.Binary.PropositionalEquality as Eq
    open Eq using (_≡_; refl)
    open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
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

        
