import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong-app)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ)
open import Function using (_∘_)
open import Isomorphism using (_≃_; _≲_; extensionality; _⇔_)
open Isomorphism.≃-Reasoning

module Connectives where
  
  data _x_ (A B : Set) : Set where
    
    ⟨_,_⟩ : 
      A 
      → B 
      → (A x B)

  infixr 2 _x_

  proj₁ : {A B : Set}
    → A x B
    → A
  
  proj₁ ⟨ x , _ ⟩ = x

  proj₂ : {A B : Set}
    → A x B
    → B

  proj₂ ⟨ _ , y ⟩ = y

  η-x : {A B : Set} (w : A x B) → ⟨ proj₁ w , proj₂ w ⟩ ≡ w
  η-x ⟨ x , y ⟩ = refl

  x-comm : {A B : Set} → A x B ≃ B x A
  x-comm = 
    record { 
      to = λ{ ⟨ x , y ⟩ → ⟨ y , x ⟩ } ; 
      from = λ{ ⟨ y , x ⟩ → ⟨ x , y ⟩ } ; 
      from∘to = λ{ ⟨ x , y ⟩ → refl } ; 
      to∘from = λ{ ⟨ y , x ⟩ → refl } 
    }

  x-assoc : {A B C : Set} → (A x B) x C ≃ A x (B x C)
  x-assoc = 
    record { 
      to = λ{ ⟨ ⟨ a , b ⟩ , c ⟩ → ⟨ a , ⟨ b , c ⟩ ⟩ } ; 
      from = λ{ ⟨ a , ⟨ b , c ⟩ ⟩ → ⟨ ⟨ a , b ⟩ , c ⟩ } ; 
      from∘to = λ{ ⟨ ⟨ a , b ⟩ , c ⟩ → refl } ; 
      to∘from = λ{ ⟨ a , ⟨ b , c ⟩ ⟩ → refl } 
    }

  open _⇔_
  
  ⇔≃x : {A B : Set} → A ⇔ B ≃ (A → B) x (B → A)
  ⇔≃x = 
    record { 
      to = λ a⇔b → ⟨ (to a⇔b) , (from a⇔b) ⟩; 
      from = λ{ ⟨ a→b , b→a ⟩ → 
        record { 
          to = a→b ; 
          from = b→a 
        } 
      } ; 
      from∘to = λ{ a⇔b → refl } ; 
      to∘from = λ{ ⟨ a→b , b→a ⟩ → refl } 
    }

  data _⊎_ (A B : Set) : Set where
    inj₁ : A → A ⊎ B

    inj₂ : B → A ⊎ B

  ⊎-comm : {A B : Set} → A ⊎ B ≃ B ⊎ A
  ⊎-comm =
    record { 
      to =      λ { (inj₁ a) → inj₂ a
                  ; (inj₂ b) → inj₁ b } ; 
      from =    λ { (inj₁ b) → inj₂ b
                  ; (inj₂ a) → inj₁ a } ; 
      from∘to = λ { (inj₁ a) → refl
                  ; (inj₂ b) → refl } ; 
      to∘from = λ { (inj₁ x) → refl
                  ; (inj₂ x) → refl } 
    }

  ⊎-assoc : {A B C : Set} → A ⊎ (B ⊎ C) ≃ (A ⊎ B) ⊎ C
  ⊎-assoc = 
    record { 
      to = λ{ (inj₁ a) → inj₁ (inj₁ a)
            ; (inj₂ (inj₁ b)) → inj₁ (inj₂ b)
            ; (inj₂ (inj₂ c)) → inj₂ c } ; 
      from = λ{ (inj₁ (inj₁ a)) → inj₁ a
              ; (inj₁ (inj₂ b)) → inj₂ (inj₁ b)
              ; (inj₂ c) → inj₂ (inj₂ c) } ; 
      from∘to = λ { (inj₁ a) → refl
                  ; (inj₂ (inj₁ b)) → refl
                  ; (inj₂ (inj₂ c)) → refl} ; 
      to∘from = λ{(inj₁ (inj₁ a)) → refl
                ; (inj₁ (inj₂ b)) → refl
                ; (inj₂ c) → refl} 
    }

  data ⊥ : Set where
    
  ⊥-elim : {A : Set} → ⊥ → A
  ⊥-elim ()

  ⊥-identityˡ : {A : Set} → ⊥ ⊎ A ≃ A
  ⊥-identityˡ = 
    record { 
      to = λ { (inj₂ a) → a } ; 
      from = λ a → inj₂ a  ; 
      from∘to = λ { (inj₂ a) → refl } ; 
      to∘from = λ a → refl 
    }

  ⊎-weak-x : {A B C : Set} → (A ⊎ B) x C → A ⊎ (B x C)
  ⊎-weak-x ⟨ inj₁ a , _ ⟩ = inj₁ a
  ⊎-weak-x ⟨ inj₂ b , c ⟩ = inj₂ ⟨ b , c ⟩

  ⊎x-implies-x⊎ : {A B C D : Set} → (A x B) ⊎ (C x D) → (A ⊎ C) x (B ⊎ D)
  ⊎x-implies-x⊎ (inj₁ ⟨ a , b ⟩) = ⟨ inj₁ a , inj₁ b ⟩
  ⊎x-implies-x⊎ (inj₂ ⟨ c , d ⟩) = ⟨ inj₂ c , inj₂ d ⟩
