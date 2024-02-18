open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; cong; cong₂)
open import Data.String using (String; _≟_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product
  using (_×_; proj₁; proj₂; ∃; ∃-syntax)
  renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Isomorphism
open import Lambda

module Properties where
    
    V¬—→ : ∀ {M N}
        → Value M
        → ¬ (M —→ N)
    V¬—→ V-ƛ ()
    V¬—→ V-zero ()
    V¬—→ (V-suc V-M) (ξ-suc M—→N) = V¬—→ V-M M—→N

    —→¬V : ∀ {M N}
        → M —→ N
        → ¬ (Value M)
    —→¬V (ξ-suc M—→N) (V-suc V-M) = —→¬V M—→N V-M

    infix 4 Canonical_⦂_
    
    data Canonical_⦂_ : Term → Type → Set where

      C-ƛ : ∀ {x A N B}
        → ∅ , x ⦂ A ⊢ N ⦂ B
        → Canonical (ƛ x ⇒ N) ⦂ (A ⇒ B)

      C-zero :
        Canonical `zero ⦂ `ℕ
      
      C-suc : ∀ {V}
        → Canonical V ⦂ `ℕ
        → Canonical `suc V ⦂ `ℕ

    Canonicalv⦂a≃ : ∀ {V A}
      → Canonical_⦂_ V A ≃ ((∅ ⊢ V ⦂ A) × (Value V))
    Canonicalv⦂a≃ = 
      record { 
        to = Canonicalv⦂a≃-to; 
        from = Canonicalv⦂a≃-from ; 
        from∘to = Canonicalv⦂a≃-from∘to; 
        to∘from = {!   !} 
      }
      where
        Canonicalv⦂a≃-to : ∀ {V A}
          → Canonical_⦂_ V A → ((∅ ⊢ V ⦂ A) × (Value V))
        Canonicalv⦂a≃-to (C-ƛ ƛ-⊢) = ⟨ ⊢ƛ ƛ-⊢ , V-ƛ ⟩
        Canonicalv⦂a≃-to C-zero = ⟨ ⊢zero {∅} , V-zero ⟩
        Canonicalv⦂a≃-to (C-suc C-V⦂N) = 
          let
            ⟨ V⦂N , V-V ⟩ = Canonicalv⦂a≃-to C-V⦂N
          in
          ⟨ ⊢suc V⦂N , V-suc V-V ⟩
        Canonicalv⦂a≃-from : ∀ {V A}
          → ((∅ ⊢ V ⦂ A) × (Value V)) → Canonical V ⦂ A
        Canonicalv⦂a≃-from ⟨ ⊢ƛ V⦂A , V-ƛ ⟩ = C-ƛ V⦂A
        Canonicalv⦂a≃-from ⟨ ⊢zero , V-zero ⟩ = C-zero
        Canonicalv⦂a≃-from ⟨ ⊢suc V⦂A , V-suc V ⟩ 
          = C-suc (Canonicalv⦂a≃-from ⟨ V⦂A , V ⟩)
        Canonicalv⦂a≃-from∘to : ∀ {A V}
          → (C : Canonical V ⦂ A)
          → (Canonicalv⦂a≃-from ∘ Canonicalv⦂a≃-to) C ≡ C
        Canonicalv⦂a≃-from∘to (C-ƛ x) = refl
        Canonicalv⦂a≃-from∘to C-zero = refl
        Canonicalv⦂a≃-from∘to (C-suc C) = 
          let
            ind = Canonicalv⦂a≃-from∘to C
          in 
            cong C-suc ind 
        Canonicalv⦂a≃-to∘from : ∀ {V A}
          → (C : (∅ ⊢ V ⦂ A) × (Value V))
          → (Canonicalv⦂a≃-to ∘ Canonicalv⦂a≃-from) C ≡ C
        Canonicalv⦂a≃-to∘from ⟨ ⊢ƛ _ , V-ƛ ⟩ = refl
        Canonicalv⦂a≃-to∘from ⟨ ⊢zero , V-zero ⟩ = refl
        Canonicalv⦂a≃-to∘from ⟨ ⊢suc M⦂ℕ , V-suc V-M ⟩ = 
          let
            ind = Canonicalv⦂a≃-to∘from ⟨ M⦂ℕ , V-M ⟩
          in 
            cong (λ{ ⟨ fst , snd ⟩ → ⟨ ⊢suc fst , V-suc snd ⟩}) ind
        
    
    -- Progress: If ∅ ⊢ M ⦂ A then either M is a value or there is an N such that M —→ N.
    data Progress (M : Term) : Set where
      
      step : {N : Term}
        → M —→ N
        → Progress M

      done : Value M
        → Progress M

    progress : ∀ {M A}
      → ∅ ⊢ M ⦂ A
      → Progress M
    progress (⊢ƛ _) = done V-ƛ
    progress (f · x) with progress f
    ... | step f—→f' = step (ξ-·₁ f—→f')
    ... | done V-ƛ with progress x
    ... |   step x—→x' = step (ξ-·₂ V-ƛ x—→x')
    ... |   done V-M = step (β-ƛ V-M)
    progress ⊢zero = done V-zero
    progress (⊢suc m⦂ℕ) with progress m⦂ℕ
    ... | step M—→N = step (ξ-suc M—→N)
    ... | done V-M  = done (V-suc V-M)
    progress (⊢case b z s) with progress b
    ... | step l—→l' = step (ξ-case l—→l')
    ... | done V-zero = step β-zero
    ... | done (V-suc V-V) = step (β-suc V-V)
    progress (⊢μ x) = step β-μ

    Progress-≃ : (M : Term)
      → Progress M ≃ (Value M ⊎ ∃[ N ](M —→ N))
    Progress-≃ M = 
      record { 
        to = λ {(step {N} M—→N) → inj₂ ⟨ N , M—→N ⟩
              ; (done V-M) → inj₁ V-M} ; 
        from = λ{ (inj₁ V-M) → done V-M
                ; (inj₂ ⟨ _ , M—→N ⟩) → step M—→N }; 
        from∘to = λ{ (step _) → refl
                   ; (done _) → refl }; 
        to∘from = λ{ (inj₁ _) → refl
                   ; (inj₂ _) → refl } 
      }

    value? : ∀ {A M} 
      → ∅ ⊢ M ⦂ A 
      → Dec (Value M)
    value? M⦂A with progress M⦂A
    ... | step M—→N = no (—→¬V M—→N)
    ... | done V-M = yes V-M 

    -- Preservation: If ∅ ⊢ M ⦂ A and M —→ N then ∅ ⊢ N ⦂ A.
    ext : ∀ {Γ Δ}
      → (∀ {x A}     → Γ ∋ x ⦂ A        → Δ ∋ x ⦂ A)
      → (∀ {x y A B} → Γ , y ⦂ B ∋ x ⦂ A → Δ , y ⦂ B ∋ x ⦂ A)
    ext _ Z = Z
    ext ρ (S x≢y Γ∋x⦂A) = S x≢y (ρ Γ∋x⦂A)

    rename : ∀ {Γ Δ}
      → (∀ {x A} → Γ ∋ x ⦂ A → Δ ∋ x ⦂ A)
      → (∀ {M A} → Γ ⊢ M ⦂ A → Δ ⊢ M ⦂ A)
    rename ρ (⊢` ∋x) = ⊢` (ρ ∋x)
    rename ρ (⊢ƛ ⊢N) = ⊢ƛ (rename (ext ρ) ⊢N)
    rename ρ (f · x) = (rename ρ f) · (rename ρ x)
    rename ρ ⊢zero = ⊢zero
    rename ρ (⊢suc x) = ⊢suc (rename ρ x)
    rename ρ (⊢case ⊢L ⊢M ⊢N) = 
      ⊢case (rename ρ ⊢L) (rename ρ ⊢M) (rename (ext ρ) ⊢N)
    rename ρ (⊢μ x) = ⊢μ (rename (ext ρ) x)

    weaken : ∀ {Γ M A}
      → ∅ ⊢ M ⦂ A
      → Γ ⊢ M ⦂ A
    weaken M⦂A = rename σ M⦂A
      where
        σ : ∀ {x A Γ} → (∅ ∋ x ⦂ A) → (Γ ∋ x ⦂ A)
        σ ()

    drop : ∀ {Γ x M A B C}
      → Γ , x ⦂ A , x ⦂ B ⊢ M ⦂ C
      → Γ , x ⦂ B ⊢ M ⦂ C
    drop {Γ} {x} {M} {A} {B} {C} ⊢M = rename σ ⊢M
      where
        σ : ∀ {z C} 
          → Γ , x ⦂ A , x ⦂ B ∋ z ⦂ C
          → Γ , x ⦂ B ∋ z ⦂ C
        σ Z = Z
        σ (S x≢x Z) = ⊥-elim (x≢x refl)
        σ (S z≢x (S _ ∋z)) = S z≢x ∋z

    swap : ∀ {Γ x y M A B C}
      → x ≢ y
      → Γ , x ⦂ A , y ⦂ B ⊢ M ⦂ C
      → Γ , y ⦂ B , x ⦂ A ⊢ M ⦂ C
    swap {Γ} {x} {y} {A = A} {B = B} {C = C} x≢y ⊢M = rename σ ⊢M
      where
        σ : ∀ {z C}
          → Γ , x ⦂ A , y ⦂ B ∋ z ⦂ C
          → Γ , y ⦂ B , x ⦂ A ∋ z ⦂ C
        σ Z = S (x≢y ∘ sym) Z 
        σ (S x≢y Z) = Z
        σ (S z≢y (S z≢x ∋z)) = S z≢x (S z≢y ∋z)

    subst : ∀ {Γ x V N A B}
      → ∅ ⊢ V ⦂ A
      → Γ , x ⦂ A ⊢ N ⦂ B
      → Γ ⊢ N [ x := V ] ⦂ B
    subst {x = y} V⦂A (⊢` {x = x} Z) with x ≟ y
    ... | yes refl  = weaken V⦂A
    ... | no y≢y    = ⊥-elim (y≢y refl)
    subst {x = y} V⦂A (⊢` {x = x} (S x≢y ∋x)) with x ≟ y
    ... | yes x≡y   = ⊥-elim (x≢y x≡y)
    ... | no x≢y    = ⊢` ∋x
    subst {x = y} V⦂A (⊢ƛ {x = x} ⊢N) with x ≟ y
    ... | yes refl  = ⊢ƛ (drop ⊢N)
    ... | no x≢y    = ⊢ƛ (subst V⦂A (swap (x≢y ∘ sym) ⊢N))
    subst V⦂A (⊢F · ⊢N) = subst V⦂A ⊢F · subst V⦂A ⊢N
    subst V⦂A ⊢zero = ⊢zero
    subst V⦂A (⊢suc ⊢N) = ⊢suc (subst V⦂A ⊢N)
    subst {x = y} V⦂A (⊢case {x = x} ⊢B ⊢Z ⊢S) with x ≟ y 
    ... | yes refl = 
      ⊢case (subst V⦂A ⊢B) (subst V⦂A ⊢Z) (drop ⊢S)
    ... | no x≢y = 
      ⊢case (subst V⦂A ⊢B) ((subst V⦂A ⊢Z)) (subst V⦂A (swap (x≢y ∘ sym) ⊢S))
    subst {x = y} V⦂A (⊢μ {x = x} ⊢N) with x ≟ y
    ... | yes refl = ⊢μ (drop ⊢N)
    ... | no x≢y = ⊢μ (subst V⦂A (swap (x≢y ∘ sym) ⊢N))

    preserve : ∀ {M N A}
      → ∅ ⊢ M ⦂ A
      → M —→ N
      → ∅ ⊢ N ⦂ A
    preserve (⊢L · ⊢M) (ξ-·₁ L—→L`) = (preserve ⊢L L—→L`) · ⊢M
    preserve (⊢L · ⊢M) (ξ-·₂ _ M—→M`) = ⊢L · (preserve ⊢M M—→M`)
    preserve (⊢ƛ ⊢L · ⊢M) (β-ƛ V-M) = subst ⊢M ⊢L
    preserve (⊢suc ⊢M) (ξ-suc M—→M`) = ⊢suc (preserve ⊢M M—→M`)
    preserve (⊢case ⊢L ⊢M ⊢N) (ξ-case L—→L`) = 
      ⊢case (preserve ⊢L L—→L`) ⊢M ⊢N
    preserve (⊢case _ ⊢M _) β-zero = 
      ⊢M
    preserve (⊢case (⊢suc ⊢M) _ ⊢N) (β-suc V-N) = 
      subst ⊢M ⊢N
    preserve (⊢μ ⊢M) β-μ = subst (⊢μ ⊢M) ⊢M

    record Gas : Set where
      constructor gas
      field
        amount : ℕ

    data Finished (N : Term) : Set where
      
      done : Value N → Finished N

      out-of-gas : Finished N

    data Steps (L : Term) : Set where
      
      steps : ∀ {N}
        → L —↠ N
        → Finished N
        → Steps L

    eval : ∀ {L A}
      → Gas
      → ∅ ⊢ L ⦂ A
      → Steps L
    eval {L} (gas zero) ⊢L = steps (L ∎) out-of-gas
    eval {L} (gas (suc amount)) ⊢L with progress ⊢L
    ... | done V-L = steps (L ∎) (done V-L)
    ... | step {N} L—→N with eval (gas amount) (preserve ⊢L L—→N)
    ...   | steps N—↠M F-N = steps (L —→⟨ L—→N ⟩ N—↠M) F-N

    2*2 : Term
    2*2 = mul · two · two

    ⊢plus : ∅ ⊢ plus ⦂ `ℕ ⇒ `ℕ ⇒ `ℕ
    ⊢plus = ⊢μ (⊢ƛ (⊢ƛ (
      ⊢case 
        (⊢` (S` Z)) 
        (⊢` Z) 
        (⊢suc (((⊢` (S` (S` (S` Z)))) · 
                ⊢` Z) · 
                ⊢` (S` Z)
              ))
      )))

    ⊢mul : ∅ ⊢ mul ⦂ `ℕ ⇒ `ℕ ⇒ `ℕ
    ⊢mul = ⊢μ (⊢ƛ (⊢ƛ (
        ⊢case 
          (⊢` (S` Z)) 
          ⊢zero 
          ( (weaken ⊢plus · ⊢` (S` Z)) · 
            ((
              (⊢` (S` (S` (S` Z)))) · 
              ⊢` Z) · 
              ⊢` (S` Z)))
        )
      ))

    ⊢2*2 : ∅ ⊢ 2*2 ⦂ `ℕ
    ⊢2*2 = ⊢mul · (⊢suc (⊢suc ⊢zero)) · (⊢suc (⊢suc ⊢zero))

    -- progress : ∀ N : (∃ M . N —→ M) ⊎ (Value N)
    -- preservation : ∀ N : ∅ ⊢ N ⦂ A → N —→ M → ∅ ⊢ M ⦂ A

    Normal : Term → Set
    Normal M = ∀ {N} → ¬ (M —→ N)

    Stuck : Term → Set
    Stuck M = Normal M × ¬ Value M

    unstuck : ∀ {M A}
      → ∅ ⊢ M ⦂ A
        -----------
      → ¬ (Stuck M)
    unstuck ⊢M ⟨ ¬M—→N , ¬V-M ⟩ with progress ⊢M
    ... | step M—→N = ¬M—→N M—→N
    ... | done V-M = ¬V-M V-M

    preserves : ∀ {M N A}
      → ∅ ⊢ M ⦂ A
      → M —↠ N
        ---------
      → ∅ ⊢ N ⦂ A
    preserves ⊢M (_ ∎) = ⊢M
    preserves ⊢M (_ —→⟨ M—→N ⟩ N—↠L) with preserve ⊢M M—→N
    ... | ⊢N = preserves ⊢N N—↠L

    wttdgs : ∀ {M N A}
      → ∅ ⊢ M ⦂ A
      → M —↠ N
        -----------
      → ¬ (Stuck N)
    wttdgs ⊢M (_ ∎) = unstuck ⊢M
    wttdgs ⊢M (_ —→⟨ M—→N ⟩ N—↠L) = 
      let
        ⊢N = (preserves ⊢M (_ —→⟨ M—→N ⟩ _ ∎)) 
      in wttdgs ⊢N N—↠L
 