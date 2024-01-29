import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ; zero; suc; _<_; _≤?_; z≤n; s≤s)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Decidable using (True; toWitness)

module DeBruijin where
    infix  4 _⊢_
    infix  4 _∋_
    infixl 5 _,_

    infixr 7 _⇒_

    infix  5 ƛ_
    infix  5 μ_
    infixl 7 _·_
    infix  8 `suc_
    infix  9 `_
    infix  9 S_
    infix  9 #_

    data Type : Set where
        _⇒_ : Type → Type → Type
        `ℕ : Type

    data Context : Set where
        ∅ : Context
        _,_ : Context → Type → Context

    data _∋_ : Context → Type → Set where

        Z : ∀ {Γ A}
            → (Γ , A) ∋ A

        S_ : ∀ {Γ A B}
            → Γ ∋ A
            → (Γ , B) ∋ A

    data _⊢_ : Context → Type → Set where

        `_ : ∀ {Γ A}
            → Γ ∋ A
            → Γ ⊢ A
        
        ƛ_ : ∀ {Γ A B}
            → Γ , A ⊢ B
            → Γ ⊢ (A ⇒ B)

        _·_ : ∀ {Γ A B}
            → Γ ⊢ (A ⇒ B)
            → Γ ⊢ A
            → Γ ⊢ B

        `zero : ∀ {Γ}
            → Γ ⊢ `ℕ

        `suc : ∀ {Γ}
            → Γ ⊢ `ℕ
            → Γ ⊢ `ℕ

        case : ∀ {Γ A}
            → Γ ⊢ `ℕ
            → Γ ⊢ A
            → Γ , `ℕ ⊢ A
            → Γ ⊢ A

        μ_ : ∀ {Γ A}
            → Γ , A ⊢ A
            → Γ ⊢ A

    length : Context → ℕ
    length ∅ = zero
    length (Γ , _) = suc (length Γ)

    lookup : {Γ : Context} → {n : ℕ} → (p : n < length Γ) → Type
    lookup {_ , A} {n = zero} (s≤s z≤n) = A
    lookup {_ , _} {n = suc n} (s≤s p) = lookup p

    count : ∀ {Γ} → {n : ℕ} → (p : n < length Γ) → Γ ∋ lookup p
    count {Γ , A} {n = zero} (s≤s z≤n) = Z
    count {Γ , A} {n = suc n} (s≤s p) = S (count p)

    #_ : ∀ {Γ}
        → (n : ℕ)
        → {n∈Γ : True (suc n ≤? length Γ)}
        → Γ ⊢ lookup (toWitness n∈Γ)

    #_ n {n∈Γ} = ` (count (toWitness n∈Γ))

    _ : ∅ ⊢ (`ℕ ⇒ `ℕ) ⇒ `ℕ ⇒ `ℕ
    _ = ƛ ƛ (# 1 · (# 1 · # 0))

    plus : ∀ {Γ} → Γ ⊢ `ℕ ⇒ `ℕ ⇒ `ℕ
    plus = μ ƛ ƛ (case (# 1) (# 0) (`suc (# 3 · # 0 · # 1)))

    mul : ∀ {Γ} → Γ ⊢ `ℕ ⇒ `ℕ ⇒ `ℕ
    mul = μ ƛ ƛ (case (# 1) `zero (plus · (# 1) · ((# 3) · (# 0) · (# 1))))

    ext : ∀ {Γ Δ}
        → (∀ {A} → Γ ∋ A → Δ ∋ A)
        → (∀ {A B} → Γ , B ∋ A → Δ , B ∋ A)
    ext ρ Z = Z
    ext ρ (S Γ∋A) = S (ρ Γ∋A)

    rename : ∀ {Γ Δ}
        → (∀ {A} → Γ ∋ A → Δ ∋ A)
        → (∀ {A} → Γ ⊢ A → Δ ⊢ A)
    rename ρ (` x) = ` (ρ x)
    rename ρ (ƛ y) = ƛ rename (ext ρ) y
    rename ρ (f · x) = (rename ρ f) · (rename ρ x)
    rename ρ `zero = `zero
    rename ρ (`suc y) = `suc (rename ρ y)
    rename ρ (case b z s) = case (rename ρ b) (rename ρ z) (rename (ext ρ) s)
    rename ρ (μ y) = μ (rename (ext ρ) y)

    exts : ∀ {Γ Δ}
        → (∀ {A}   →     Γ ∋ A →     Δ ⊢ A)
        → (∀ {A B} → Γ , B ∋ A → Δ , B ⊢ A)
    exts _ Z = ` Z 
    exts σ (S x) = rename S_ (σ x)

    subst : ∀ {Γ Δ}
        → (∀ {A} → Γ ∋ A → Δ ⊢ A)
        → (∀ {A} → Γ ⊢ A → Δ ⊢ A)
    subst σ (` x) = σ x
    subst σ (ƛ x) = ƛ subst (exts σ) x
    subst σ (f · x) = (subst σ f) · (subst σ x)
    subst σ `zero = `zero
    subst σ (`suc x) = `suc (subst σ x)
    subst σ (case b z s) = case (subst σ b) (subst σ z) (subst (exts σ) s)
    subst σ (μ x) = μ (subst (exts σ) x)

    _[_] : ∀ {Γ A B}
        → Γ , B ⊢ A
        → Γ ⊢ B
        → Γ ⊢ A
    _[_] {Γ} {A} {B} r,b⊢a r⊢b = subst {Γ , B} {Γ} σ {A} r,b⊢a 
        where
        σ : ∀ {A} →  Γ , B ∋ A → Γ ⊢ A
        σ Z = r⊢b
        σ (S r∋a) = ` r∋a

    data Value : ∀ {Γ A} → Γ ⊢ A → Set where

        V-ƛ : ∀ {Γ A B} {N : Γ , A ⊢ B}
            → Value (ƛ N)

        V-zero : ∀ {Γ}
            → Value (`zero {Γ})

        V-suc : ∀ {Γ} {V : Γ ⊢ `ℕ}
            → Value V
            → Value (`suc V)

    infixr 2 _—→_

    data _—→_ : ∀ {Γ A} → (Γ ⊢ A) → (Γ ⊢ A) → Set where

        ξ-·₁ : ∀ {Γ A B} {L L` : Γ ⊢ A ⇒ B} {M : Γ ⊢ A}
            → L —→ L`
            → L · M —→ L` · M

        ξ-·₂ : ∀ {Γ A B} {L : Γ ⊢ A ⇒ B} {M M` : Γ ⊢ A}
            → Value L
            → M —→ M`
            → L · M —→ L · M`

        β-ƛ : ∀ {Γ A B} {N : Γ , A ⊢ B} {W : Γ ⊢ A}
            → Value W
            → (ƛ N) · W —→ N [ W ]

        ξ-suc : ∀ {Γ} {M M` : Γ ⊢ `ℕ}
            → M —→ M`
            → `suc M —→ `suc M`

        ξ-case : ∀ {Γ A} {L L` : Γ ⊢ `ℕ} {M : Γ ⊢ A} {N : Γ , `ℕ ⊢ A}
            → L —→ L`
            → case L M N —→ case L` M N

        β-zero : ∀ {Γ A} {M : Γ ⊢ A} {N : Γ , `ℕ ⊢ A}
            → case `zero M N —→ M

        β-suc : ∀ {Γ A} {V : Γ ⊢ `ℕ} {M : Γ ⊢ A} {N : Γ , `ℕ ⊢ A}
            → Value V
            → case (`suc V) M N —→ N [ V ]

        β-μ : ∀ {Γ A} {N : Γ , A ⊢ A}
            → μ N —→ (N [ μ N ])

    infix 2 _—↠_
    infix 1 begin_
    infixr 2 _—→⟨_⟩_
    infix 3 _∎

    data _—↠_ {Γ A} : (Γ ⊢ A) → (Γ ⊢ A) → Set where
        _∎ : (M : Γ ⊢ A)
            ------
            → M —↠ M

        step—→ : (L : Γ ⊢ A) {M N : Γ ⊢ A}
            → M —↠ N
            → L —→ M
            ------
            → L —↠ N

    pattern _—→⟨_⟩_ L L—→M M—↠N = step—→ L M—↠N L—→M

    begin_ : ∀ {Γ A} {M N : Γ ⊢ A}
        → M —↠ N
        ------
        → M —↠ N
    begin M—↠N = M—↠N

    V¬—→ : ∀ {Γ} {A} {V : Γ ⊢ A} {M : Γ ⊢ A}
        → Value V
        → ¬ (V —→ M)
    V¬—→ (V-suc V-V) (ξ-suc V—→M) = V¬—→ V-V V—→M

    data Progress {A} (M : ∅ ⊢ A) : Set where
        
        step : ∀ {N : ∅ ⊢ A}
            → M —→ N
            → Progress M

        done : Value M
            → Progress M

    progress : ∀ {A} (M : ∅ ⊢ A)
        → Progress M
    progress (ƛ ⊢M) = done V-ƛ
    progress (M · N) with progress M
    ... | step M—→N = step (ξ-·₁ M—→N)
    ... | done V-ƛ with progress N
    ...   | step N—→L = step (ξ-·₂ V-ƛ N—→L)
    ...   | done V-N = step (β-ƛ V-N)
    progress `zero = done V-zero
    progress (`suc M) with progress M
    ... | step M—→N = step (ξ-suc M—→N)
    ... | done V-M = done (V-suc V-M)
    progress (case L M N) with progress L
    ... | step L—→L' = step (ξ-case L—→L')
    ... | done V-zero = step β-zero
    ... | done (V-suc V-L) = step (β-suc V-L)
    progress (μ ⊢M) = step β-μ

    record Gas : Set where
        constructor gas
        field
            amount : ℕ

    data Finished {Γ : Context} {A : Type} (N : Γ ⊢ A) : Set where

        done : Value N
            → Finished N

        out-of-gas :
            Finished N

    data Steps {A} : ∅ ⊢ A → Set where
        
        steps : {L N : ∅ ⊢ A}
            → L —↠ N
            → Finished N
            → Steps L

    eval : ∀ {A : Type}
        → Gas
        → (L : ∅ ⊢ A)
        → Steps L
    eval (gas zero) L = steps (L ∎) out-of-gas
    eval (gas (suc amount)) L 
        with progress L
    ... | done V-L = steps (L ∎) (done V-L)
    ... | step {N} L—→N
        with eval (gas amount) N 
    ...   | steps N—↠N₁ F-N₁ = 
            steps (L —→⟨ L—→N ⟩ N—↠N₁) F-N₁

    T⟦_⟧ : Type → Set
    T⟦ f ⇒ x ⟧ = (T⟦ f ⟧) → (T⟦ x ⟧)
    T⟦ `ℕ ⟧ = ℕ

    Env : Context → Set
    Env Γ = ∀ {A} → Γ ∋ A → T⟦ A ⟧ 

    ext-E : ∀ {Γ} {A} → Env Γ → T⟦ A ⟧ → Env (Γ , A)
    ext-E E a Z = a
    ext-E E a (S x) = E x

    postulate
        fix : ∀ {A : Set} → (A → A) → A

    E⟦_⟧ : ∀ {Γ} {A} 
        → Γ ⊢ A 
        → Env Γ
        → T⟦ A ⟧
    E⟦ ` x ⟧ E = E x
    E⟦ ƛ f ⟧ E = λ x → E⟦ f ⟧ (ext-E E x)
    E⟦ f · x ⟧ E = E⟦ f ⟧ E (E⟦ x ⟧ E)
    E⟦ `zero ⟧ E = zero
    E⟦ `suc x ⟧ E = suc (E⟦ x ⟧ E)
    E⟦ case L M N ⟧ Y with E⟦ L ⟧ Y
    ... | zero = E⟦ M ⟧ Y
    ... | suc n = E⟦ N ⟧ (ext-E Y n)
    E⟦ μ M ⟧ Y = fix λ a → E⟦ M ⟧ (ext-E Y a)

    sucμ : ∅ ⊢ `ℕ
    sucμ = μ (`suc (# 0))

    _ : eval (gas 3) sucμ ≡ steps
            (μ `suc (` Z) —→⟨ β-μ ⟩
            `suc (μ `suc (` Z)) —→⟨ ξ-suc β-μ ⟩
            `suc (`suc (μ `suc (` Z))) —→⟨ ξ-suc (ξ-suc β-μ) ⟩
            `suc (`suc (`suc (μ `suc (` Z)))) ∎)
            out-of-gas
    _ = refl

    Ch : Type → Type
    Ch A = (A ⇒ A) ⇒ A ⇒ A

    twoᶜ : ∀ {Γ : Context} {A : Type} 
        → Γ ⊢ Ch A
    twoᶜ = ƛ (ƛ ((# 1) · (# 1 · (# 0))))

    plusᶜ : {Γ : Context} {A : Type}
        → Γ ⊢ (Ch A ⇒ Ch A ⇒ Ch A)
    plusᶜ = ƛ (ƛ (ƛ (ƛ 
                        ((# 3) · (# 1) · ((# 2) · (# 1) · (# 0)))
                    )))
    
    sucᶜ : {Γ : Context}
        → Γ ⊢ `ℕ ⇒ `ℕ
    sucᶜ = ƛ (`suc (# 0))

    2+2ᶜ : {Γ : Context}
        → Γ ⊢ `ℕ
    2+2ᶜ = (((plusᶜ · twoᶜ) · twoᶜ) · sucᶜ) · `zero

    _ : eval (gas 100) (twoᶜ · sucᶜ · `zero) ≡ 
        steps
            ((ƛ (ƛ ` (S Z) · (` (S Z) · ` Z))) · (ƛ `suc (` Z)) · `zero —→⟨
            ξ-·₁ (β-ƛ V-ƛ) ⟩
            (ƛ (ƛ `suc (` Z)) · ((ƛ `suc (` Z)) · ` Z)) · `zero —→⟨ β-ƛ V-zero
            ⟩
            (ƛ `suc (` Z)) · ((ƛ `suc (` Z)) · `zero) —→⟨ ξ-·₂ V-ƛ (β-ƛ V-zero)
            ⟩
            (ƛ `suc (` Z)) · `suc `zero —→⟨ β-ƛ (V-suc V-zero) ⟩
            `suc (`suc `zero) ∎)
            (done (V-suc (V-suc V-zero)))
    _ = refl

    one : {Γ : Context} → Γ ⊢ `ℕ
    one = `suc `zero

    two : {Γ : Context} → Γ ⊢ `ℕ
    two = `suc (`suc `zero)

    2*2≡4 : eval (gas 100) (mul · two · two) ≡ steps
            ((μ
            (ƛ
            (ƛ
                case (` (S Z)) `zero
                ((μ
                (ƛ
                (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
                · ` (S Z)
                · (` (S (S (S Z))) · ` Z · ` (S Z))))))
            · `suc (`suc `zero)
            · `suc (`suc `zero)
            —→⟨ ξ-·₁ (ξ-·₁ β-μ) ⟩
            (ƛ
            (ƛ
            case (` (S Z)) `zero
            ((μ
                (ƛ
                (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
                · ` (S Z)
                ·
                ((μ
                (ƛ
                (ƛ
                    case (` (S Z)) `zero
                    ((μ
                    (ƛ
                    (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
                    · ` (S Z)
                    · (` (S (S (S Z))) · ` Z · ` (S Z))))))
                · ` Z
                · ` (S Z)))))
            · `suc (`suc `zero)
            · `suc (`suc `zero)
            —→⟨ ξ-·₁ (β-ƛ (V-suc (V-suc V-zero))) ⟩
            (ƛ
            case (`suc (`suc `zero)) `zero
            ((μ
                (ƛ
                (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
            · ` (S Z)
            ·
            ((μ
                (ƛ
                (ƛ
                case (` (S Z)) `zero
                ((μ
                    (ƛ
                    (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
                    · ` (S Z)
                    · (` (S (S (S Z))) · ` Z · ` (S Z))))))
                · ` Z
                · ` (S Z))))
            · `suc (`suc `zero)
            —→⟨ β-ƛ (V-suc (V-suc V-zero)) ⟩
            case (`suc (`suc `zero)) `zero
            ((μ
            (ƛ
                (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
            · `suc (`suc `zero)
            ·
            ((μ
                (ƛ
                (ƛ
                case (` (S Z)) `zero
                ((μ
                    (ƛ
                    (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
                · ` (S Z)
                · (` (S (S (S Z))) · ` Z · ` (S Z))))))
            · ` Z
            · `suc (`suc `zero)))
            —→⟨ β-suc (V-suc V-zero) ⟩
            (μ
            (ƛ
            (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
            · `suc (`suc `zero)
            ·
            ((μ
            (ƛ
                (ƛ
                case (` (S Z)) `zero
                ((μ
                (ƛ
                    (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
                · ` (S Z)
                · (` (S (S (S Z))) · ` Z · ` (S Z))))))
            · `suc `zero
            · `suc (`suc `zero))
            —→⟨ ξ-·₁ (ξ-·₁ β-μ) ⟩
            (ƛ
            (ƛ
            case (` (S Z)) (` Z)
            (`suc
                ((μ
                (ƛ
                (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
                · ` Z
                · ` (S Z)))))
            · `suc (`suc `zero)
            ·
            ((μ
            (ƛ
                (ƛ
                case (` (S Z)) `zero
                ((μ
                (ƛ
                    (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
                · ` (S Z)
                · (` (S (S (S Z))) · ` Z · ` (S Z))))))
            · `suc `zero
            · `suc (`suc `zero))
            —→⟨ ξ-·₁ (β-ƛ (V-suc (V-suc V-zero))) ⟩
            (ƛ
            case (`suc (`suc `zero)) (` Z)
            (`suc
            ((μ
                (ƛ
                (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
                · ` Z
                · ` (S Z))))
            ·
            ((μ
            (ƛ
                (ƛ
                case (` (S Z)) `zero
                ((μ
                (ƛ
                    (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
                · ` (S Z)
                · (` (S (S (S Z))) · ` Z · ` (S Z))))))
            · `suc `zero
            · `suc (`suc `zero))
            —→⟨ ξ-·₂ V-ƛ (ξ-·₁ (ξ-·₁ β-μ)) ⟩
            (ƛ
            case (`suc (`suc `zero)) (` Z)
            (`suc
            ((μ
                (ƛ
                (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
                · ` Z
                · ` (S Z))))
            ·
            ((ƛ
            (ƛ
                case (` (S Z)) `zero
                ((μ
                (ƛ
                (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
                · ` (S Z)
                ·
                ((μ
                (ƛ
                    (ƛ
                    case (` (S Z)) `zero
                    ((μ
                    (ƛ
                        (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
                    · ` (S Z)
                    · (` (S (S (S Z))) · ` Z · ` (S Z))))))
                · ` Z
                · ` (S Z)))))
            · `suc `zero
            · `suc (`suc `zero))
            —→⟨ ξ-·₂ V-ƛ (ξ-·₁ (β-ƛ (V-suc V-zero))) ⟩
            (ƛ
            case (`suc (`suc `zero)) (` Z)
            (`suc
            ((μ
                (ƛ
                (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
                · ` Z
                · ` (S Z))))
            ·
            ((ƛ
            case (`suc `zero) `zero
            ((μ
                (ƛ
                (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
                · ` (S Z)
                ·
                ((μ
                (ƛ
                (ƛ
                    case (` (S Z)) `zero
                    ((μ
                    (ƛ
                    (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
                    · ` (S Z)
                    · (` (S (S (S Z))) · ` Z · ` (S Z))))))
                · ` Z
                · ` (S Z))))
            · `suc (`suc `zero))
            —→⟨ ξ-·₂ V-ƛ (β-ƛ (V-suc (V-suc V-zero))) ⟩
            (ƛ
            case (`suc (`suc `zero)) (` Z)
            (`suc
            ((μ
                (ƛ
                (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
                · ` Z
                · ` (S Z))))
            ·
            case (`suc `zero) `zero
            ((μ
            (ƛ
                (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
            · `suc (`suc `zero)
            ·
            ((μ
                (ƛ
                (ƛ
                case (` (S Z)) `zero
                ((μ
                    (ƛ
                    (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
                · ` (S Z)
                · (` (S (S (S Z))) · ` Z · ` (S Z))))))
            · ` Z
            · `suc (`suc `zero)))
            —→⟨ ξ-·₂ V-ƛ (β-suc V-zero) ⟩
            (ƛ
            case (`suc (`suc `zero)) (` Z)
            (`suc
            ((μ
                (ƛ
                (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
                · ` Z
                · ` (S Z))))
            ·
            ((μ
            (ƛ
                (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
            · `suc (`suc `zero)
            ·
            ((μ
                (ƛ
                (ƛ
                case (` (S Z)) `zero
                ((μ
                    (ƛ
                    (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
                · ` (S Z)
                · (` (S (S (S Z))) · ` Z · ` (S Z))))))
            · `zero
            · `suc (`suc `zero)))
            —→⟨ ξ-·₂ V-ƛ (ξ-·₁ (ξ-·₁ β-μ)) ⟩
            (ƛ
            case (`suc (`suc `zero)) (` Z)
            (`suc
            ((μ
                (ƛ
                (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
                · ` Z
                · ` (S Z))))
            ·
            ((ƛ
            (ƛ
                case (` (S Z)) (` Z)
                (`suc
                ((μ
                (ƛ
                    (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
                · ` Z
                · ` (S Z)))))
            · `suc (`suc `zero)
            ·
            ((μ
                (ƛ
                (ƛ
                case (` (S Z)) `zero
                ((μ
                    (ƛ
                    (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
                · ` (S Z)
                · (` (S (S (S Z))) · ` Z · ` (S Z))))))
            · `zero
            · `suc (`suc `zero)))
            —→⟨ ξ-·₂ V-ƛ (ξ-·₁ (β-ƛ (V-suc (V-suc V-zero)))) ⟩
            (ƛ
            case (`suc (`suc `zero)) (` Z)
            (`suc
            ((μ
                (ƛ
                (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
                · ` Z
                · ` (S Z))))
            ·
            ((ƛ
            case (`suc (`suc `zero)) (` Z)
            (`suc
                ((μ
                (ƛ
                (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
                · ` Z
                · ` (S Z))))
            ·
            ((μ
                (ƛ
                (ƛ
                case (` (S Z)) `zero
                ((μ
                    (ƛ
                    (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
                · ` (S Z)
                · (` (S (S (S Z))) · ` Z · ` (S Z))))))
            · `zero
            · `suc (`suc `zero)))
            —→⟨ ξ-·₂ V-ƛ (ξ-·₂ V-ƛ (ξ-·₁ (ξ-·₁ β-μ))) ⟩
            (ƛ
            case (`suc (`suc `zero)) (` Z)
            (`suc
            ((μ
                (ƛ
                (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
                · ` Z
                · ` (S Z))))
            ·
            ((ƛ
            case (`suc (`suc `zero)) (` Z)
            (`suc
                ((μ
                (ƛ
                (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
                · ` Z
                · ` (S Z))))
            ·
            ((ƛ
                (ƛ
                case (` (S Z)) `zero
                ((μ
                (ƛ
                    (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
                · ` (S Z)
                ·
                ((μ
                    (ƛ
                    (ƛ
                    case (` (S Z)) `zero
                    ((μ
                        (ƛ
                        (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
                    · ` (S Z)
                    · (` (S (S (S Z))) · ` Z · ` (S Z))))))
                · ` Z
                · ` (S Z)))))
            · `zero
            · `suc (`suc `zero)))
            —→⟨ ξ-·₂ V-ƛ (ξ-·₂ V-ƛ (ξ-·₁ (β-ƛ V-zero))) ⟩
            (ƛ
            case (`suc (`suc `zero)) (` Z)
            (`suc
            ((μ
                (ƛ
                (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
                · ` Z
                · ` (S Z))))
            ·
            ((ƛ
            case (`suc (`suc `zero)) (` Z)
            (`suc
                ((μ
                (ƛ
                (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
                · ` Z
                · ` (S Z))))
            ·
            ((ƛ
                case `zero `zero
                ((μ
                (ƛ
                (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
                · ` (S Z)
                ·
                ((μ
                (ƛ
                    (ƛ
                    case (` (S Z)) `zero
                    ((μ
                    (ƛ
                        (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
                    · ` (S Z)
                    · (` (S (S (S Z))) · ` Z · ` (S Z))))))
                · ` Z
                · ` (S Z))))
            · `suc (`suc `zero)))
            —→⟨ ξ-·₂ V-ƛ (ξ-·₂ V-ƛ (β-ƛ (V-suc (V-suc V-zero)))) ⟩
            (ƛ
            case (`suc (`suc `zero)) (` Z)
            (`suc
            ((μ
                (ƛ
                (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
                · ` Z
                · ` (S Z))))
            ·
            ((ƛ
            case (`suc (`suc `zero)) (` Z)
            (`suc
                ((μ
                (ƛ
                (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
                · ` Z
                · ` (S Z))))
            ·
            case `zero `zero
            ((μ
                (ƛ
                (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
            · `suc (`suc `zero)
            ·
            ((μ
                (ƛ
                (ƛ
                case (` (S Z)) `zero
                ((μ
                    (ƛ
                    (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
                    · ` (S Z)
                    · (` (S (S (S Z))) · ` Z · ` (S Z))))))
                · ` Z
                · `suc (`suc `zero))))
            —→⟨ ξ-·₂ V-ƛ (ξ-·₂ V-ƛ β-zero) ⟩
            (ƛ
            case (`suc (`suc `zero)) (` Z)
            (`suc
            ((μ
                (ƛ
                (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
                · ` Z
                · ` (S Z))))
            ·
            ((ƛ
            case (`suc (`suc `zero)) (` Z)
            (`suc
                ((μ
                (ƛ
                (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
                · ` Z
                · ` (S Z))))
            · `zero)
            —→⟨ ξ-·₂ V-ƛ (β-ƛ V-zero) ⟩
            (ƛ
            case (`suc (`suc `zero)) (` Z)
            (`suc
            ((μ
                (ƛ
                (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
                · ` Z
                · ` (S Z))))
            ·
            case (`suc (`suc `zero)) `zero
            (`suc
            ((μ
                (ƛ
                (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
            · ` Z
            · `zero))
            —→⟨ ξ-·₂ V-ƛ (β-suc (V-suc V-zero)) ⟩
            (ƛ
            case (`suc (`suc `zero)) (` Z)
            (`suc
            ((μ
                (ƛ
                (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
                · ` Z
                · ` (S Z))))
            ·
            `suc
            ((μ
            (ƛ
                (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
            · `suc `zero
            · `zero)
            —→⟨ ξ-·₂ V-ƛ (ξ-suc (ξ-·₁ (ξ-·₁ β-μ))) ⟩
            (ƛ
            case (`suc (`suc `zero)) (` Z)
            (`suc
            ((μ
                (ƛ
                (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
                · ` Z
                · ` (S Z))))
            ·
            `suc
            ((ƛ
            (ƛ
                case (` (S Z)) (` Z)
                (`suc
                ((μ
                (ƛ
                    (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
                · ` Z
                · ` (S Z)))))
            · `suc `zero
            · `zero)
            —→⟨ ξ-·₂ V-ƛ (ξ-suc (ξ-·₁ (β-ƛ (V-suc V-zero)))) ⟩
            (ƛ
            case (`suc (`suc `zero)) (` Z)
            (`suc
            ((μ
                (ƛ
                (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
                · ` Z
                · ` (S Z))))
            ·
            `suc
            ((ƛ
            case (`suc `zero) (` Z)
            (`suc
                ((μ
                (ƛ
                (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
                · ` Z
                · ` (S Z))))
            · `zero)
            —→⟨ ξ-·₂ V-ƛ (ξ-suc (β-ƛ V-zero)) ⟩
            (ƛ
            case (`suc (`suc `zero)) (` Z)
            (`suc
            ((μ
                (ƛ
                (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
                · ` Z
                · ` (S Z))))
            ·
            `suc
            (case (`suc `zero) `zero
            (`suc
            ((μ
                (ƛ
                (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
                · ` Z
                · `zero)))
            —→⟨ ξ-·₂ V-ƛ (ξ-suc (β-suc V-zero)) ⟩
            (ƛ
            case (`suc (`suc `zero)) (` Z)
            (`suc
            ((μ
                (ƛ
                (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
                · ` Z
                · ` (S Z))))
            ·
            `suc
            (`suc
            ((μ
                (ƛ
                (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
            · `zero
            · `zero))
            —→⟨ ξ-·₂ V-ƛ (ξ-suc (ξ-suc (ξ-·₁ (ξ-·₁ β-μ)))) ⟩
            (ƛ
            case (`suc (`suc `zero)) (` Z)
            (`suc
            ((μ
                (ƛ
                (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
                · ` Z
                · ` (S Z))))
            ·
            `suc
            (`suc
            ((ƛ
                (ƛ
                case (` (S Z)) (` Z)
                (`suc
                ((μ
                    (ƛ
                    (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
                · ` Z
                · ` (S Z)))))
            · `zero
            · `zero))
            —→⟨ ξ-·₂ V-ƛ (ξ-suc (ξ-suc (ξ-·₁ (β-ƛ V-zero)))) ⟩
            (ƛ
            case (`suc (`suc `zero)) (` Z)
            (`suc
            ((μ
                (ƛ
                (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
                · ` Z
                · ` (S Z))))
            ·
            `suc
            (`suc
            ((ƛ
                case `zero (` Z)
                (`suc
                ((μ
                (ƛ
                    (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
                · ` Z
                · ` (S Z))))
            · `zero))
            —→⟨ ξ-·₂ V-ƛ (ξ-suc (ξ-suc (β-ƛ V-zero))) ⟩
            (ƛ
            case (`suc (`suc `zero)) (` Z)
            (`suc
            ((μ
                (ƛ
                (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
                · ` Z
                · ` (S Z))))
            ·
            `suc
            (`suc
            (case `zero `zero
            (`suc
                ((μ
                (ƛ
                (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
                · ` Z
                · `zero))))
            —→⟨ ξ-·₂ V-ƛ (ξ-suc (ξ-suc β-zero)) ⟩
            (ƛ
            case (`suc (`suc `zero)) (` Z)
            (`suc
            ((μ
                (ƛ
                (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
                · ` Z
                · ` (S Z))))
            · `suc (`suc `zero)
            —→⟨ β-ƛ (V-suc (V-suc V-zero)) ⟩
            case (`suc (`suc `zero)) (`suc (`suc `zero))
            (`suc
            ((μ
                (ƛ
                (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
            · ` Z
            · `suc (`suc `zero)))
            —→⟨ β-suc (V-suc V-zero) ⟩
            `suc
            ((μ
            (ƛ
                (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
            · `suc `zero
            · `suc (`suc `zero))
            —→⟨ ξ-suc (ξ-·₁ (ξ-·₁ β-μ)) ⟩
            `suc
            ((ƛ
            (ƛ
                case (` (S Z)) (` Z)
                (`suc
                ((μ
                (ƛ
                    (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
                · ` Z
                · ` (S Z)))))
            · `suc `zero
            · `suc (`suc `zero))
            —→⟨ ξ-suc (ξ-·₁ (β-ƛ (V-suc V-zero))) ⟩
            `suc
            ((ƛ
            case (`suc `zero) (` Z)
            (`suc
                ((μ
                (ƛ
                (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
                · ` Z
                · ` (S Z))))
            · `suc (`suc `zero))
            —→⟨ ξ-suc (β-ƛ (V-suc (V-suc V-zero))) ⟩
            `suc
            (case (`suc `zero) (`suc (`suc `zero))
            (`suc
            ((μ
                (ƛ
                (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
                · ` Z
                · `suc (`suc `zero))))
            —→⟨ ξ-suc (β-suc V-zero) ⟩
            `suc
            (`suc
            ((μ
                (ƛ
                (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
            · `zero
            · `suc (`suc `zero)))
            —→⟨ ξ-suc (ξ-suc (ξ-·₁ (ξ-·₁ β-μ))) ⟩
            `suc
            (`suc
            ((ƛ
                (ƛ
                case (` (S Z)) (` Z)
                (`suc
                ((μ
                    (ƛ
                    (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
                · ` Z
                · ` (S Z)))))
            · `zero
            · `suc (`suc `zero)))
            —→⟨ ξ-suc (ξ-suc (ξ-·₁ (β-ƛ V-zero))) ⟩
            `suc
            (`suc
            ((ƛ
                case `zero (` Z)
                (`suc
                ((μ
                (ƛ
                    (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
                · ` Z
                · ` (S Z))))
            · `suc (`suc `zero)))
            —→⟨ ξ-suc (ξ-suc (β-ƛ (V-suc (V-suc V-zero)))) ⟩
            `suc
            (`suc
            (case `zero (`suc (`suc `zero))
            (`suc
                ((μ
                (ƛ
                (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
                · ` Z
                · `suc (`suc `zero)))))
            —→⟨ ξ-suc (ξ-suc β-zero) ⟩ `suc (`suc (`suc (`suc `zero))) ∎)
            (done (V-suc (V-suc (V-suc (V-suc V-zero)))))
    2*2≡4 = refl
   