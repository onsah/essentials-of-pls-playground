import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ; zero; suc; _<_; _≤_; z≤n; s≤s; pred)
open import Data.Product using (_×_) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Negation using ()
  renaming (contradiction to ¬¬-intro)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Function.Base using (_∘_)

module Decidable where
  data Bool : Set where
      true  : Bool
      false : Bool

  infix 4 _≤ᵇ_

  _≤ᵇ_ : ℕ → ℕ → Bool
  zero ≤ᵇ n       =  true
  suc m ≤ᵇ zero   =  false
  suc m ≤ᵇ suc n  =  m ≤ᵇ n

  T : Bool → Set
  T true = ⊤ 
  T false = ⊥

  T-≡ : (b : Bool) → T b → b ≡ true
  T-≡ true tt = refl
  
  ≡-T : {b : Bool} → b ≡ true → T b
  ≡-T refl = tt

  ≤ᵇ→≤ : (m n : ℕ) → T (m ≤ᵇ n) → m ≤ n
  ≤ᵇ→≤ zero _ _ = z≤n
  ≤ᵇ→≤ (suc m) (suc n) t = s≤s (≤ᵇ→≤ m n t)

  ≤-≤ᵇ : {m n : ℕ} → m ≤ n → T (m ≤ᵇ n)
  ≤-≤ᵇ z≤n = tt
  ≤-≤ᵇ (s≤s m≤n) = ≤-≤ᵇ m≤n

  data Dec (A : Set) : Set where
    yes : A → Dec A
    no : ¬ A → Dec A

  ¬s≤z : {m : ℕ} → ¬ (suc m ≤ zero)
  ¬s≤z ()

  ¬s≤s : {m n : ℕ} → ¬ (m ≤ n) → ¬ (suc m ≤ suc n)
  ¬s≤s ¬m≤n (s≤s m≤n) = ¬m≤n m≤n

  _≤?_ : (m n : ℕ) → Dec (m ≤ n)
  zero ≤? n = yes z≤n
  suc m ≤? zero = no ¬s≤z
  suc m ≤? suc n with m ≤? n
  ... | yes m≤n = yes (s≤s m≤n)
  ... | no ¬m≤n = no (¬s≤s ¬m≤n)
    
  _<?_ : (m n : ℕ) → Dec (m < n)
  zero <? zero = no (λ z<z → ¬s≤z z<z)
  zero <? suc n = yes (s≤s z≤n)
  suc m <? zero = no (λ sucm<z → ¬s≤z sucm<z)
  suc m <? suc n with m <? n
  ... | yes sucm≤n = yes (s≤s sucm≤n)
  ... | no ¬sucm≤n = no (¬s≤s ¬sucm≤n)

  ¬z≡s : {n : ℕ} → ¬ (zero ≡ suc n)
  ¬z≡s ()

  ¬s≡z : {n : ℕ} → ¬ (suc n ≡ zero)
  ¬s≡z ()

  _≡ℕ?_ : (m n : ℕ) → Dec (m ≡ n)
  zero ≡ℕ? zero = yes refl
  zero ≡ℕ? suc n = no ¬z≡s
  suc m ≡ℕ? zero = no ¬s≡z
  suc m ≡ℕ? suc n with m ≡ℕ? n
  ... | yes m≡n = yes (cong suc m≡n)
  ... | no ¬m≡n = no (¬m≡n ∘ (cong pred))

  ⌊_⌋ : ∀ {A : Set} → Dec A → Bool
  ⌊ yes _ ⌋  =  true
  ⌊ no _ ⌋  =  false

  toWitness : ∀ {A : Set} {D : Dec A} → T ⌊ D ⌋ → A
  toWitness {A} {yes x} tt  =  x
  toWitness {A} {no ¬x} ()

  toWitnessFalse : ∀ {A : Set} {¬D : Dec (¬ A)} → T ⌊ ¬D ⌋ → ¬ A
  toWitnessFalse {¬D = yes ¬a} tt = ¬a 

  fromWitness : ∀ {A : Set} {D : Dec A} → A → T ⌊ D ⌋
  fromWitness {A} {yes x} _  =  tt
  fromWitness {A} {no ¬x} x  =  ¬x x

  fromWitnessFalse : ∀ {A : Set} {¬D : Dec (¬ A)} → ¬ A → T ⌊ ¬D ⌋
  fromWitnessFalse {¬D = yes ¬a} _ = tt
  fromWitnessFalse {¬D = no ¬¬a} ¬a = ¬¬a ¬a

  True : ∀ {Q} → Dec Q → Set
  True decq = T ⌊ decq ⌋

  False : ∀ {Q} → Dec (¬ Q) → Set
  False dec¬q = T ⌊ dec¬q ⌋

  infixr 6 _×-dec_

  _×-dec_ : ∀ {A B : Set} → Dec A → Dec B → Dec (A × B)
  yes x ×-dec yes y = yes ⟨ x , y ⟩
  no ¬x ×-dec _     = no λ{ ⟨ x , y ⟩ → ¬x x }
  _     ×-dec no ¬y = no λ{ ⟨ x , y ⟩ → ¬y y } 

  infixr 5 _⊎-dec_

  _⊎-dec_ : ∀ {A B : Set} → Dec A → Dec B → Dec (A ⊎ B)
  yes x ⊎-dec _     = yes (inj₁ x)
  _     ⊎-dec yes y = yes (inj₂ y)
  no ¬x ⊎-dec no ¬y = no λ{ (inj₁ x) → ¬x x ; (inj₂ y) → ¬y y }

  ¬? : ∀ {A : Set} → Dec A → Dec (¬ A)
  ¬? (yes a)  =  no (¬¬-intro a)
  ¬? (no ¬a)  =  yes ¬a

  _⊃_ : Bool → Bool → Bool
  _     ⊃ true   =  true
  false ⊃ _      =  true
  true  ⊃ false  =  false

  _→-dec_ : ∀ {A B : Set} → Dec A → Dec B → Dec (A → B)
  _     →-dec yes y  =  yes (λ _ → y)
  no ¬x →-dec _      =  yes (λ x → ⊥-elim (¬x x))
  yes x →-dec no ¬y  =  no (λ f → ¬y (f x))
