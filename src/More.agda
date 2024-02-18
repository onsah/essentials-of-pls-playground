{-# OPTIONS --allow-unsolved-metas #-}

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; cong₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ; zero; suc; _*_; _<_; _≤?_; z≤n; s≤s)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Decidable using (True; toWitness)
open import Data.Product using (∃-syntax)

module More where
    infix  4 _⊢_
    infix  4 _∋_
    infixl 5 _,_

    infixr 7 _⇒_
    infixr 9 _`×_

    infix  5 ƛ_
    infix  5 μ_
    infixl 7 _·_
    infixl 8 _`*_
    infix  8 `suc_
    infix  9 `_
    infix  9 S_
    infix  9 #_

    data Type : Set where
        `ℕ      : Type
        _⇒_     : Type → Type → Type
        Nat     : Type
        _`×_    : Type → Type → Type
        _`⊎_    : Type → Type → Type
        `⊤      : Type
        `⊥      : Type
        `List_  : Type → Type

    data Context : Set where
        ∅   : Context
        _,_ : Context → Type → Context

    data _∋_ : Context → Type → Set where

        Z : ∀ {Γ A}
            ---------
            → Γ , A ∋ A

        S_ : ∀ {Γ A B}
            → Γ ∋ B
            ---------
            → Γ , A ∋ B

    data _⊢_ : Context → Type → Set where

        -- variables

        `_ : ∀ {Γ A}
            → Γ ∋ A
            -----
            → Γ ⊢ A

        -- functions

        ƛ_  :  ∀ {Γ A B}
            → Γ , A ⊢ B
            ---------
            → Γ ⊢ A ⇒ B

        _·_ : ∀ {Γ A B}
            → Γ ⊢ A ⇒ B
            → Γ ⊢ A
            ---------
            → Γ ⊢ B

        -- naturals

        `zero : ∀ {Γ}
            ------
            → Γ ⊢ `ℕ

        `suc_ : ∀ {Γ}
            → Γ ⊢ `ℕ
            ------
            → Γ ⊢ `ℕ

        case : ∀ {Γ A}
            → Γ ⊢ `ℕ
            → Γ ⊢ A
            → Γ , `ℕ ⊢ A
            -----
            → Γ ⊢ A

        -- fixpoint

        μ_ : ∀ {Γ A}
            → Γ , A ⊢ A
            ----------
            → Γ ⊢ A

        -- primitive numbers

        con : ∀ {Γ}
            → ℕ
            -------
            → Γ ⊢ Nat

        _`*_ : ∀ {Γ}
            → Γ ⊢ Nat
            → Γ ⊢ Nat
            -------
            → Γ ⊢ Nat

        -- let

        `let : ∀ {Γ A B}
            → Γ ⊢ A
            → Γ , A ⊢ B
            ----------
            → Γ ⊢ B

        -- products

        `⟨_,_⟩ : ∀ {Γ A B}
            → Γ ⊢ A
            → Γ ⊢ B
            -----------
            → Γ ⊢ A `× B

        `proj₁ : ∀ {Γ A B}
            → Γ ⊢ A `× B
            -----------
            → Γ ⊢ A

        `proj₂ : ∀ {Γ A B}
            → Γ ⊢ A `× B
            -----------
            → Γ ⊢ B

        -- alternative formulation of products

        case× : ∀ {Γ A B C}
            → Γ ⊢ A `× B
            → Γ , A , B ⊢ C
            --------------
            → Γ ⊢ C

        -- sums
        `inj₁ : {Γ : Context} {A B : Type}
            → Γ ⊢ A
            → Γ ⊢ (A `⊎ B)

        `inj₂ : {Γ : Context} {A B : Type}
            → Γ ⊢ B
            → Γ ⊢ (A `⊎ B)

        case⊎ : {Γ : Context} {A B C : Type}
            → Γ ⊢ A `⊎ B
            → Γ , A ⊢ C
            → Γ , B ⊢ C
            → Γ ⊢ C

        -- unit
        `tt : {Γ : Context}
            → Γ ⊢ `⊤

        case⊤ : {Γ : Context} {A : Type}
            → Γ ⊢ `⊤
            → Γ ⊢ A
            → Γ ⊢ A

        -- empty
        case⊥ : {Γ : Context} {A : Type}
            → (Γ ⊢ `⊥)
            → (Γ ⊢ A)

        -- lists
        `[] : {Γ : Context} {A : Type}
           → Γ ⊢ `List A

        _`∷_ : {Γ : Context} {A : Type}
            → Γ ⊢ A
            → Γ ⊢ `List A
            → Γ ⊢ `List A

        caseL : {Γ : Context} {A B : Type}
            → Γ ⊢ `List A
            → Γ ⊢ B
            → Γ , A , `List A ⊢ B
            → Γ ⊢ B


    length : Context → ℕ
    length ∅        =  zero
    length (Γ , _)  =  suc (length Γ)

    lookup : {Γ : Context} → {n : ℕ} → (p : n < length Γ) → Type
    lookup {(_ , A)} {zero}    (s≤s z≤n)  =  A
    lookup {(Γ , _)} {(suc n)} (s≤s p)    =  lookup p

    count : ∀ {Γ} → {n : ℕ} → (p : n < length Γ) → Γ ∋ lookup p
    count {_ , _} {zero}    (s≤s z≤n)  =  Z
    count {Γ , _} {(suc n)} (s≤s p)    =  S (count p)

    #_ : ∀ {Γ}
        → (n : ℕ)
        → {n∈Γ : True (suc n ≤? length Γ)}
            --------------------------------
        → Γ ⊢ lookup (toWitness n∈Γ)
    #_ n {n∈Γ}  =  ` count (toWitness n∈Γ)

    ext : ∀ {Γ Δ}
        → (∀ {A}   →     Γ ∋ A →     Δ ∋ A)
            ---------------------------------
        → (∀ {A B} → Γ , A ∋ B → Δ , A ∋ B)
    ext ρ Z      =  Z
    ext ρ (S x)  =  S (ρ x)

    rename : ∀ {Γ Δ}
        → (∀ {A} → Γ ∋ A → Δ ∋ A)
            -----------------------
        → (∀ {A} → Γ ⊢ A → Δ ⊢ A)
    rename ρ (` x)           =  ` (ρ x)
    rename ρ (ƛ N)           =  ƛ (rename (ext ρ) N)
    rename ρ (L · M)         =  (rename ρ L) · (rename ρ M)
    rename ρ (`zero)         =  `zero
    rename ρ (`suc M)        =  `suc (rename ρ M)
    rename ρ (case L M N)    =  case (rename ρ L) (rename ρ M) (rename (ext ρ) N)
    rename ρ (μ N)           =  μ (rename (ext ρ) N)
    rename ρ (con n)         =  con n
    rename ρ (M `* N)        =  rename ρ M `* rename ρ N
    rename ρ (`let M N)      =  `let (rename ρ M) (rename (ext ρ) N)
    rename ρ `⟨ M , N ⟩      =  `⟨ rename ρ M , rename ρ N ⟩
    rename ρ (`proj₁ L)      =  `proj₁ (rename ρ L)
    rename ρ (`proj₂ L)      =  `proj₂ (rename ρ L)
    rename ρ (case× L M)     =  case× (rename ρ L) (rename (ext (ext ρ)) M)
    rename σ (`inj₁ N)       = `inj₁ (rename σ N)
    rename σ (`inj₂ N)       = `inj₂ (rename σ N)
    rename σ (case⊎ L M N)   = case⊎ (rename σ L) (rename (ext σ) M) (rename (ext σ) N)
    rename _ `tt             = `tt
    rename σ (case⊤ L M)     = case⊤ (rename σ L) (rename σ M)
    rename σ (case⊥ N)       = case⊥ (rename σ N)
    rename _ `[]             = `[]
    rename σ (L `∷ M)        = (rename σ L) `∷ (rename σ M)
    rename σ (caseL L M N) = caseL (rename σ L) (rename σ M) (rename (ext (ext σ)) N)

    exts : ∀ {Γ Δ} 
        → (∀ {A}   →     Γ ∋ A →     Δ ⊢ A) 
        → (∀ {A B} → Γ , A ∋ B → Δ , A ⊢ B)
    exts σ Z      =  ` Z
    exts σ (S x)  =  rename S_ (σ x)

    subst : ∀ {Γ Δ} 
        → (∀ {C} → Γ ∋ C → Δ ⊢ C) 
        → (∀ {C} → Γ ⊢ C → Δ ⊢ C)
    subst σ (` k)          =  σ k
    subst σ (ƛ N)          =  ƛ (subst (exts σ) N)
    subst σ (L · M)        =  (subst σ L) · (subst σ M)
    subst _ (`zero)        =  `zero
    subst σ (`suc M)       =  `suc (subst σ M)
    subst σ (case L M N)   =  case (subst σ L) (subst σ M) (subst (exts σ) N)
    subst σ (μ N)          =  μ (subst (exts σ) N)
    subst _ (con n)        =  con n
    subst σ (M `* N)       =  subst σ M `* subst σ N
    subst σ (`let M N)     =  `let (subst σ M) (subst (exts σ) N)
    subst σ `⟨ M , N ⟩     =  `⟨ subst σ M , subst σ N ⟩
    subst σ (`proj₁ L)     =  `proj₁ (subst σ L)
    subst σ (`proj₂ L)     =  `proj₂ (subst σ L)
    subst σ (case× L M)    =  case× (subst σ L) (subst (exts (exts σ)) M)
    subst σ (`inj₁ N)      = `inj₁ (subst σ N)
    subst σ (`inj₂ N)      = `inj₂ (subst σ N)
    subst σ (case⊎ L M N)  = case⊎ (subst σ L) (subst (exts σ) M) (subst (exts σ) N)
    subst _ `tt            = `tt
    subst σ (case⊤ L M)    = case⊤ (subst σ L) (subst σ M)
    subst σ (case⊥ N)      = case⊥ (subst σ N)
    subst _ `[]            = `[]
    subst σ (L `∷ M)       = subst σ L `∷ subst σ M
    subst σ (caseL L M N)  = caseL (subst σ L) (subst σ M) (subst (exts (exts σ)) N)

    substZero : ∀ {Γ}{A B} 
        → Γ ⊢ A 
        → Γ , A ∋ B 
        → Γ ⊢ B
    substZero V Z = V
    substZero V (S ∋b) = ` ∋b

    _[_] : ∀ {Γ A B}
        → Γ , B ⊢ A
        → Γ ⊢ B
            ---------
        → Γ ⊢ A
    _[_] {Γ} {A} {B} N M = subst {Γ , B} {Γ} (substZero M) {A} N

    substZeroOne : {Γ : Context} {A B C : Type}
        → Γ ⊢ A
        → Γ ⊢ B
        → Γ , A , B ∋ C
        → Γ ⊢ C
    substZeroOne V W Z = W
    substZeroOne V W (S Z) = V
    substZeroOne V W (S (S N)) = ` N 

    _[_][_] : ∀ {Γ A B C}
        → Γ , A , B ⊢ C
        → Γ ⊢ A
        → Γ ⊢ B
        -------------
        → Γ ⊢ C
    _[_][_] {Γ} {A} {B} N V W = subst {Γ , A , B} {Γ} (substZeroOne V W) N

    data Value : ∀ {Γ A} → Γ ⊢ A → Set where

        -- functions
        V-ƛ : ∀ {Γ A B} {N : Γ , A ⊢ B}
            ---------------------------
            → Value (ƛ N)

        -- naturals
        V-zero : ∀ {Γ}
            -----------------
            → Value (`zero {Γ})

        V-suc_ : ∀ {Γ} {V : Γ ⊢ `ℕ}
            → Value V
            --------------
            → Value (`suc V)

        -- primitives
        V-con : ∀ {Γ n}
            -----------------
            → Value (con {Γ} n)

        -- products
        V-⟨_,_⟩ : ∀ {Γ A B} {V : Γ ⊢ A} {W : Γ ⊢ B}
            → Value V
            → Value W
            ----------------
            → Value `⟨ V , W ⟩

        -- sums
        V-inj₁ : {Γ : Context} {A B : Type} {V : Γ ⊢ A}
            → Value V
            → Value (`inj₁ {B = B} V)
        
        V-inj₂ : {Γ : Context} {A B : Type} {V : Γ ⊢ B}
            → Value V
            → Value (`inj₂ {A = A} V)

        -- unit
        V-tt : {Γ : Context}
            → Value (`tt {Γ})

        -- lists
        V-[] : {Γ : Context} {A : Type}
            → Value {Γ = Γ} (`[] {A = A})

        V-∷ : {Γ : Context} {A : Type} {L : Γ ⊢ A} {N : Γ ⊢ `List A}
            → Value L
            → Value N
            → Value {Γ = Γ} (L `∷ N)

    infix 2 _—→_

    data _—→_ : ∀ {Γ A} → (Γ ⊢ A) → (Γ ⊢ A) → Set where

        -- functions

        ξ-·₁ : ∀ {Γ A B} {L L′ : Γ ⊢ A ⇒ B} {M : Γ ⊢ A}
            → L —→ L′
            ---------------
            → L · M —→ L′ · M

        ξ-·₂ : ∀ {Γ A B} {V : Γ ⊢ A ⇒ B} {M M′ : Γ ⊢ A}
            → Value V
            → M —→ M′
            ---------------
            → V · M —→ V · M′

        β-ƛ : ∀ {Γ A B} {N : Γ , A ⊢ B} {V : Γ ⊢ A}
            → Value V
            --------------------
            → (ƛ N) · V —→ N [ V ]

        -- naturals

        ξ-suc : ∀ {Γ} {M M′ : Γ ⊢ `ℕ}
            → M —→ M′
            -----------------
            → `suc M —→ `suc M′

        ξ-case : ∀ {Γ A} {L L′ : Γ ⊢ `ℕ} {M : Γ ⊢ A} {N : Γ , `ℕ ⊢ A}
            → L —→ L′
            -------------------------
            → case L M N —→ case L′ M N

        β-zero :  ∀ {Γ A} {M : Γ ⊢ A} {N : Γ , `ℕ ⊢ A}
            -------------------
            → case `zero M N —→ M

        β-suc : ∀ {Γ A} {V : Γ ⊢ `ℕ} {M : Γ ⊢ A} {N : Γ , `ℕ ⊢ A}
            → Value V
            ----------------------------
            → case (`suc V) M N —→ N [ V ]

        -- fixpoint

        β-μ : ∀ {Γ A} {N : Γ , A ⊢ A}
            ----------------
            → μ N —→ N [ μ N ]

        -- primitive numbers

        ξ-*₁ : ∀ {Γ} {L L′ M : Γ ⊢ Nat}
            → L —→ L′
            -----------------
            → L `* M —→ L′ `* M

        ξ-*₂ : ∀ {Γ} {V M M′ : Γ ⊢ Nat}
            → Value V
            → M —→ M′
            -----------------
            → V `* M —→ V `* M′

        δ-* : ∀ {Γ c d}
            ---------------------------------
            → con {Γ} c `* con d —→ con (c * d)

        -- let

        ξ-let : ∀ {Γ A B} {M M′ : Γ ⊢ A} {N : Γ , A ⊢ B}
            → M —→ M′
            ---------------------
            → `let M N —→ `let M′ N

        β-let : ∀ {Γ A B} {V : Γ ⊢ A} {N : Γ , A ⊢ B}
            → Value V
            -------------------
            → `let V N —→ N [ V ]

        -- products

        ξ-⟨,⟩₁ : ∀ {Γ A B} {M M′ : Γ ⊢ A} {N : Γ ⊢ B}
            → M —→ M′
            -------------------------
            → `⟨ M , N ⟩ —→ `⟨ M′ , N ⟩

        ξ-⟨,⟩₂ : ∀ {Γ A B} {V : Γ ⊢ A} {N N′ : Γ ⊢ B}
            → Value V
            → N —→ N′
            -------------------------
            → `⟨ V , N ⟩ —→ `⟨ V , N′ ⟩

        ξ-proj₁ : ∀ {Γ A B} {L L′ : Γ ⊢ A `× B}
            → L —→ L′
            ---------------------
            → `proj₁ L —→ `proj₁ L′

        ξ-proj₂ : ∀ {Γ A B} {L L′ : Γ ⊢ A `× B}
            → L —→ L′
            ---------------------
            → `proj₂ L —→ `proj₂ L′

        β-proj₁ : ∀ {Γ A B} {V : Γ ⊢ A} {W : Γ ⊢ B}
            → Value V
            → Value W
            ----------------------
            → `proj₁ `⟨ V , W ⟩ —→ V

        β-proj₂ : ∀ {Γ A B} {V : Γ ⊢ A} {W : Γ ⊢ B}
            → Value V
            → Value W
            ----------------------
            → `proj₂ `⟨ V , W ⟩ —→ W

        -- alternative formulation of products

        ξ-case× : ∀ {Γ A B C} {L L′ : Γ ⊢ A `× B} {M : Γ , A , B ⊢ C}
            → L —→ L′
            -----------------------
            → case× L M —→ case× L′ M

        β-case× : ∀ {Γ A B C} {V : Γ ⊢ A} {W : Γ ⊢ B} {M : Γ , A , B ⊢ C}
            → Value V
            → Value W
            ----------------------------------
            → case× `⟨ V , W ⟩ M —→ M [ V ][ W ]
        
        -- sums

        ξ-inj₁ : {Γ : Context} {A B : Type} {M M` : Γ ⊢ A}
            → M —→ M`
            → `inj₁ {B = B} M —→ `inj₁ M`

        ξ-inj₂ : {Γ : Context} {A B : Type} {M M` : Γ ⊢ B}
            → M —→ M`
            → `inj₂ {A = A} M —→ `inj₂ M`

        ξ-case⊎ : {Γ : Context} {A B C : Type} {L L` : Γ ⊢ A `⊎ B} {M : Γ , A ⊢ C} {N : Γ , B ⊢ C}
            → L —→ L`
            → case⊎ L M N  —→ case⊎ L` M N

        β-inj₁ : {Γ : Context} {A B C : Type} {V : Γ ⊢ A} {M : Γ , A ⊢ C} {N : Γ , B ⊢ C}
            → Value V
            → case⊎ (`inj₁ V) M N —→ M [ V ]

        β-inj₂ : {Γ : Context} {A B C : Type} {V : Γ ⊢ B} {M : Γ , A ⊢ C} {N : Γ , B ⊢ C}
            → Value V
            → case⊎ (`inj₂ V) M N —→ N [ V ]

        -- unit
        ξ-case⊤ : {Γ : Context} {A : Type} {L L` : Γ ⊢ `⊤} {M : Γ ⊢ A} 
            → L —→ L`
            → case⊤ L M —→ case⊤ L` M

        β-case⊤ : {Γ : Context} {A : Type} {L : Γ ⊢ `⊤} {M : Γ ⊢ A}
            → Value L
            → case⊤ L M —→ M

        -- empty
        ξ-case⊥ : {Γ : Context} {A : Type} {L L` : Γ ⊢ `⊥}
            → L —→ L`
            → case⊥ {A = A} L —→ case⊥ {A = A} L`

        -- lists
        ξ-∷₁ : {Γ : Context} {A : Type} {L L` : Γ ⊢ A} {M : Γ ⊢ `List A}
            → L —→ L`
            → L `∷ M —→ L` `∷ M

        ξ-∷₂ : {Γ : Context} {A : Type} {L : Γ ⊢ A} {M M` : Γ ⊢ `List A}
            → Value L
            → M —→ M`
            → L `∷ M —→ L `∷ M`     

        ξ-caseL : {Γ : Context} {A B : Type} {L L` : Γ ⊢ `List A} {M : Γ  ⊢ B} {N : Γ , A , `List A ⊢ B}
            → L —→ L`
            → caseL L M N —→ caseL L` M N

        β-[] : {Γ : Context} {A B : Type} {M : Γ ⊢ B} {N : Γ , A , `List A ⊢ B} 
            → caseL `[] M N —→ M
        
        β-∷ : {Γ : Context} {A B : Type} {L : Γ ⊢ A} {Ls : Γ ⊢ `List A} {M : Γ ⊢ B} {N : Γ , A , `List A ⊢ B}
            → Value L
            → Value Ls
            → caseL (L `∷ Ls) M N —→ N [ L ][ Ls ]


    infix  2 _—↠_
    infixr 2 _—→⟨_⟩_
    infix  3 _∎

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

    V¬—→ : ∀ {Γ A} {M N : Γ ⊢ A}
        → Value M
        ----------
        → ¬ (M —→ N)
    V¬—→ V-ƛ          ()
    V¬—→ V-zero       ()
    V¬—→ (V-suc VM)   (ξ-suc M—→M′)     =  V¬—→ VM M—→M′
    V¬—→ V-con        ()
    V¬—→ V-⟨ VM , _ ⟩ (ξ-⟨,⟩₁ M—→M′)    =  V¬—→ VM M—→M′
    V¬—→ V-⟨ _ , VN ⟩ (ξ-⟨,⟩₂ _ N—→N′)  =  V¬—→ VN N—→N′
    V¬—→ (V-inj₁ V) (ξ-inj₁ V—→V`)      = V¬—→ V V—→V`
    V¬—→ (V-inj₂ V) (ξ-inj₂ V—→V`)      = V¬—→ V V—→V`
    V¬—→ V-tt         ()
    V¬—→ V-[] ()
    V¬—→ (V-∷ V-L _) (ξ-∷₁ L—→L`) = V¬—→ V-L L—→L`
    V¬—→ (V-∷ _ V-N) (ξ-∷₂ _ N—→N`) = V¬—→ V-N N—→N`

    data Progress {A} (M : ∅ ⊢ A) : Set where

        step : ∀ {N : ∅ ⊢ A}
            → M —→ N
            ----------
            → Progress M

        done :
            Value M
            ----------
            → Progress M

    progress : ∀ {A}
        → (M : ∅ ⊢ A)
        -----------
        → Progress M
    progress (ƛ N) = done V-ƛ
    progress (L · M) with progress L
    ... | step L—→N = step (ξ-·₁ L—→N)
    ... | done v@V-ƛ with progress M
    ...     | step M—→N = step (ξ-·₂ v M—→N)
    ...     | done V-M = step (β-ƛ V-M)
    progress `zero = done V-zero
    progress (`suc M) with progress M
    ... | step M—→N = step (ξ-suc M—→N)
    ... | done V-M = done (V-suc V-M)
    progress (case L M N) with progress L 
    ... | step L—→L' = step (ξ-case L—→L')
    ... | done V-zero = step β-zero
    ... | done (V-suc V-L) = step (β-suc V-L)
    progress (μ N) = step β-μ
    progress (con n) = done V-con
    progress (L `* M) with progress L
    ... | step L—→L' = step (ξ-*₁ L—→L')
    ... | done v@V-con with progress M
    ...     | step M—→M′ = step (ξ-*₂ v M—→M′)
    ...     | done V-con = step δ-*
    progress (`let M N) with progress M
    ... | step M—→M′ = step (ξ-let M—→M′)
    ... | done V-M = step (β-let V-M)
    progress `⟨ M , N ⟩ with progress M
    ... | step M—→M′ = step (ξ-⟨,⟩₁ M—→M′)
    ... | done V-M with progress N
    ...     | step N—→N′ = step (ξ-⟨,⟩₂ V-M N—→N′)
    ...     | done V-N = done V-⟨ V-M , V-N ⟩
    progress (`proj₁ L) with progress L
    ... | step L—→L' = step (ξ-proj₁ L—→L')
    ... | done V-⟨ V-M , V-N ⟩ = step (β-proj₁ V-M V-N)
    progress (`proj₂ L) with progress L
    ... | step L—→L' = step (ξ-proj₂ L—→L')
    ... | done V-⟨ V-M , V-N ⟩ = step (β-proj₂ V-M V-N)
    progress (case× L M) with progress L
    ... | step L—→L' = step (ξ-case× L—→L')
    ... | done V-⟨ L₁ , L₂ ⟩ = step (β-case× L₁ L₂)
    progress (`inj₁ N) with progress N
    ... | step N—→N` = step (ξ-inj₁ N—→N`)
    ... | done V-N = done (V-inj₁ V-N)
    progress (`inj₂ N) with progress N
    ... | step N—→N` = step (ξ-inj₂ N—→N`)
    ... | done V-N = done (V-inj₂ V-N)
    progress (case⊎ L M N) with progress L
    ... | step L—→L` = step (ξ-case⊎ L—→L`)
    ... | done (V-inj₁ V-L) = step (β-inj₁ V-L)
    ... | done (V-inj₂ V-L) = step (β-inj₂ V-L)
    progress `tt = done V-tt
    progress (case⊤ L M) with progress L
    ... | step L—→L` = step (ξ-case⊤ L—→L`)
    ... | done V-L = step (β-case⊤ V-L)
    progress (case⊥ L) with progress L
    ... | step L—→L` = step (ξ-case⊥ L—→L`)
    progress `[] = done V-[]
    progress (L `∷ N) with progress L
    ... | step L—→L` = step (ξ-∷₁ L—→L`)
    ... | done V-L with progress N
    ...     | step N—→N` = step (ξ-∷₂ V-L N—→N`)
    ...     | done V-N = done (V-∷ V-L V-N)
    progress (caseL L M N) with progress L
    ... | step L—→L` = step (ξ-caseL L—→L`)
    ... | done V-[] = step β-[]
    ... | done (V-∷ V-L V-N) = step (β-∷ V-L V-N)
    

    record Gas : Set where
        constructor gas
        field
            amount : ℕ

    data Finished {Γ : Context} {A : Type} (N : Γ ⊢ A) : Set where
        
        done : Value N
            → Finished N

        out-of-gas :
            Finished N

    data Steps {A} : (∅ ⊢ A) → Set where

        steps : {L N : ∅ ⊢ A}
            → L —↠ N
            → Finished N
            → Steps L

    eval : {A : Type}
        → Gas
        → (L : ∅ ⊢ A)
        → Steps L
    eval (gas zero) L = steps (L ∎) out-of-gas
    eval (gas (suc amount)) L with progress L
    ... | done V-L = steps (L ∎) (done V-L)
    ... | step {N} L—→N with eval (gas amount) N 
    ...     | steps N—↠N` fin-N` = steps (_ —→⟨ L—→N ⟩ N—↠N`) fin-N`

    eval-result : {A : Type}
        → Gas
        → (L : ∅ ⊢ A)
        → ∃[ L ] (Finished L)
    eval-result g L with eval g L
    ... | steps _ (finished) = _ Data.Product., finished

    cube : ∅ ⊢ Nat ⇒ Nat
    cube = ƛ (# 0 `* # 0 `* # 0)

    swap× : ∀ {A B} → ∅ ⊢ A `× B ⇒ B `× A
    swap× = ƛ `⟨ (`proj₂ (# 0)) , (`proj₁ (# 0)) ⟩

    swap⊎ : {A B : Type}
        → ∅ ⊢ A `⊎ B ⇒ B `⊎ A
    swap⊎ = ƛ (case⊎ (# 0)
                    (`inj₂ (# 0))
                    (`inj₁ (# 0)))

    _ = eval (gas 100) (swap⊎ {`⊤} · (`inj₂ (con 4)))
  
    to×⊤ : {A : Type}
        → ∅ ⊢ A ⇒ A `× `⊤
    to×⊤ = ƛ `⟨ (# 0) , `tt ⟩

    _ = eval (gas 100) (case× (to×⊤ · (con 5)) ((# 1)))

    from×⊤ : {A : Type}
        → ∅ ⊢ A `× `⊤ ⇒ A
    from×⊤ = ƛ `proj₁ (# 0)

    _ = eval (gas 100) (from×⊤ · (to×⊤ · (con 5)))

    to⊎⊥ : {A : Type} 
        → ∅ ⊢ A ⇒ A `⊎ `⊥
    to⊎⊥ = ƛ `inj₁ (# 0)

    from⊎⊥ : {A : Type} 
        → ∅ ⊢ A `⊎ `⊥ ⇒ A
    from⊎⊥ = ƛ case⊎ (# 0) (# 0) (case⊥ (# 0))

    _ = eval (gas 100) (from⊎⊥ · (to⊎⊥ · (con 2)))

    mapL : {Γ : Context} {A B : Type}
        → ∅ ⊢ (A ⇒ B) ⇒ `List A ⇒ `List B
    mapL = μ ƛ ƛ
            (caseL (# 0)
                `[]
                (((# 3) · (# 1)) `∷ (((# 4) · (# 3)) · (# 0))))

    _ : eval-result (gas 100) (mapL {∅} · (ƛ (# 0) `* (# 0)) · ((con 5) `∷ `[])) 
            ≡ (((con 25) `∷ `[]) Data.Product., _)
    _ = refl

    open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡) renaming (_∎ to _≡∎)

    _⇒ₛ_ : Context → Context → Set
    Γ ⇒ₛ Δ = ∀ {A} → Γ ∋ A → Δ ⊢ A

    _,,_ : Context → Context → Context
    Γ ,, ∅ = Γ
    Γ ,, (Δ , t) = (Γ ,, Δ) , t

    exts* : ∀ {Γ₁ Γ₂ : Context} (Δ : Context) 
        → Γ₁ ⇒ₛ Γ₂
        → (Γ₁ ,, Δ) ⇒ₛ (Γ₂ ,, Δ)
    exts* ∅ σ = σ
    exts* (Δ , t) σ = exts (exts* Δ σ)

    double-subst' :
        ∀ {Γ A B C } (Γ' : Context) (V : Γ ⊢ A) (W : Γ ⊢ B) (N : (Γ , A , B) ,, Γ' ⊢ C) 
        → subst (exts* Γ' (substZeroOne V W)) N ≡ 
          subst (exts* Γ' (substZero V)) (subst (exts* Γ' (substZero (rename S_ W))) N) 
    -- TODO: Check the submitted code for variable case
    double-subst' Γ' V W (` x) = {!   !}
    -- All other cases are just inductive cases
    double-subst' Γ' V W (ƛ N) = cong ƛ_ (double-subst' (Γ' , _) V W N)
    double-subst' Γ' V W (N₁ · N₂) = {!   !}
    double-subst' Γ' V W `zero = {!   !}
    double-subst' Γ' V W (`suc N) = {!   !}
    double-subst' Γ' V W (case N N₁ N₂) = {!   !}
    double-subst' Γ' V W (μ N) = {!   !}
    double-subst' Γ' V W (con x) = {!   !}
    double-subst' Γ' V W (N `* N₁) = {!   !}
    double-subst' Γ' V W (`let N N₁) = {!   !}
    double-subst' Γ' V W `⟨ N , N₁ ⟩ = {!   !}
    double-subst' Γ' V W (`proj₁ N) = {!   !}
    double-subst' Γ' V W (`proj₂ N) = {!   !}
    double-subst' Γ' V W (case× N N₁) = {!   !}
    double-subst' Γ' V W (`inj₁ N) = {!   !}
    double-subst' Γ' V W (`inj₂ N) = {!   !}
    double-subst' Γ' V W (case⊎ N N₁ N₂) = {!   !}
    double-subst' Γ' V W `tt = {!   !}
    double-subst' Γ' V W (case⊤ N N₁) = {!   !}
    double-subst' Γ' V W (case⊥ N) = {!   !}
    double-subst' Γ' V W `[] = {!   !}
    double-subst' Γ' V W (N `∷ N₁) = {!   !}
    double-subst' Γ' V W (caseL N N₁ N₂) = {!   !}

    -- TODO: Prove a generalized version of this where the context is expanded arbitrarily
    -- and use it here
    double-subst :
        ∀ {Γ A B C} {V : Γ ⊢ A} {W : Γ ⊢ B} {N : Γ , A , B ⊢ C} 
        → N [ V ][ W ] ≡ (N [ rename S_ W ]) [ V ]
    double-subst {V = V} {W = W} {N = N} = 
        begin 
            (N [ V ][ W ]) 
        ≡⟨⟩
            subst (substZeroOne V W) N 
        ≡⟨ double-subst' ∅ V W N ⟩
            subst (substZero V) (subst (substZero (rename S_ W)) N) 
        ≡⟨⟩ 
            ((N [ rename S_ W ]) [ V ]) 
        ≡∎
  