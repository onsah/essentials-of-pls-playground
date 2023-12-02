open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Relation.Nullary using (¬_)
open import Data.Nat using (ℕ; zero; suc; _<_; z≤n; s≤s; _>_)
open import Data.Nat.Properties using (suc-injective)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; _,_)
open import Isomorphism using (_≃_; extensionality)
open import Data.Bool using (Bool; true; false)

module Practice where
    data Dec (A : Set) : Set where
        yes : A → Dec A
        no : ¬ A → Dec A

    _==_ : ℕ → ℕ → Bool
    zero == zero = true 
    zero == suc y = false
    suc x == zero = false
    suc x == suc y = x == y

    
