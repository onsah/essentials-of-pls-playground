module Negations where
    open import Relation.Binary.PropositionalEquality using (_≡_; refl)
    open import Data.Nat using (ℕ; zero; suc)
    open import Data.Empty using (⊥; ⊥-elim)
    open import Data.Sum using (_⊎_; inj₁; inj₂)
    open import Data.Product using (_×_)
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
