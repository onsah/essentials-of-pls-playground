open import More
open import Relation.Nullary.Decidable
open import Relation.Nullary using (Dec; yes; no)
open import Data.Unit
open import Data.Empty
open import Data.Product renaming (_,_ to ⟨_,_⟩)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)

-- Notes:
-- 1. Why not use lambda-let directly in _†?

module Bisimulation where

    module Exercise1 where

        infix  4 _~_
        infix  5 ~ƛ_
        infix  7 _~·_

        data _~_ : ∀ {Γ A} → (Γ ⊢ A) → (Γ ⊢ A) → Set where

            ~` : ∀ {Γ A} {x : Γ ∋ A}
                ---------
                → ` x ~ ` x

            ~ƛ_ : ∀ {Γ A B} {N N† : Γ , A ⊢ B}
                → N ~ N†
                ----------
                → ƛ N ~ ƛ N†

            _~·_ : ∀ {Γ A B} {L L† : Γ ⊢ A ⇒ B} {M M† : Γ ⊢ A}
                → L ~ L†
                → M ~ M†
                ---------------
                → L · M ~ L† · M†

            ~let : ∀ {Γ A B} {M M† : Γ ⊢ A} {N N† : Γ , A ⊢ B}
                → M ~ M†
                → N ~ N†
                ----------------------
                → `let M N ~ (ƛ N†) · M†

        module WithReflectionTrick where
        
            Relevant : {Γ : Context} {A : Type}
                → (Γ ⊢ A) 
                → Set
            Relevant (` M) = ⊤
            Relevant (ƛ M) = Relevant M
            Relevant (M · N) = (Relevant M) × (Relevant N)
            Relevant `zero = ⊥
            Relevant (`suc _) = ⊥
            Relevant (case _ _ _) = ⊥
            Relevant (μ _) = ⊥
            Relevant (con _) = ⊥
            Relevant (_ `* _) = ⊥
            Relevant (`let M N) = Relevant M × Relevant N
            Relevant `⟨ _ , _ ⟩ = ⊥
            Relevant (`proj₁ _) = ⊥
            Relevant (`proj₂ _) = ⊥
            Relevant (case× _ _) = ⊥
            Relevant (`inj₁ _) = ⊥
            Relevant (`inj₂ _) = ⊥
            Relevant (case⊎ _ _ _) = ⊥
            Relevant `tt = ⊥
            Relevant (case⊤ _ _) = ⊥
            Relevant (case⊥ _) = ⊥
            Relevant `[] = ⊥
            Relevant (_ `∷ _) = ⊥
            Relevant (caseL _ _ _) = ⊥
            
            Relevant? : {Γ : Context} {A : Type}
                → (M : Γ ⊢ A) 
                → Dec (Relevant M)
            Relevant? (` _) = yes tt
            Relevant? (ƛ M) with Relevant? M
            ... | yes rel-M = yes rel-M
            ... | no ¬rel-M = no (λ rel-M → ¬rel-M rel-M)
            Relevant? (M · N) with Relevant? M | Relevant? N
            ... | yes rel-M | yes rel-N = yes ⟨ rel-M , rel-N ⟩
            ... | _ | no ¬rel-N = no (λ{ ⟨ _ , rel-N ⟩ → ¬rel-N rel-N})
            ... | no ¬rel-M  | _ = no (λ{ ⟨ rel-M , _ ⟩ → ¬rel-M rel-M})
            Relevant? `zero = no (λ x → x)
            Relevant? (`suc _) = no λ x → x
            Relevant? (case _ _ _) = no (λ x → x)
            Relevant? (μ _) = no (λ x → x)
            Relevant? (con _) = no (λ x → x)
            Relevant? (_ `* _) = no (λ x → x)
            Relevant? (`let M N) with Relevant? M | Relevant? N
            ... | yes  rel-M | yes rel-N    = yes ⟨ rel-M , rel-N ⟩
            ... | no  ¬rel-M | _            = no (λ{ ⟨ rel-M , _ ⟩ → ¬rel-M rel-M})
            ... |          _ | no ¬rel-N    = no (λ{ ⟨ _ , rel-N ⟩ → ¬rel-N rel-N})
            Relevant? `⟨ _ , _ ⟩ = no (λ x → x)
            Relevant? (`proj₁ _) = no (λ x → x)
            Relevant? (`proj₂ _) = no (λ x → x)
            Relevant? (case× _ _) = no (λ x → x)
            Relevant? (`inj₁ _) = no (λ x → x)
            Relevant? (`inj₂ _) = no (λ x → x)
            Relevant? (case⊎ _ _ _) = no (λ x → x)
            Relevant? `tt = no (λ x → x)
            Relevant? (case⊤ _ _) = no (λ x → x)
            Relevant? (case⊥ _) = no (λ x → x)
            Relevant? `[] = no (λ x → x)
            Relevant? (_ `∷ _) = no (λ x → x)
            Relevant? (caseL _ _ _) = no (λ x → x)

            _† : {Γ : Context} {A : Type}
                → (M : Γ ⊢ A)
                → {True (Relevant? M)}
                → (Γ ⊢ A)
            (M †) {rel?} = †` M (toWitness rel?)
                where
                †` : {Γ : Context} {A : Type}
                    → (M : Γ ⊢ A)
                    → (Relevant M)
                    → (Γ ⊢ A)
                †` (` x) rel = ` x
                †` (ƛ M) rel = ƛ (†` M rel)
                †` (L · M) ⟨ rel-L , rel-M ⟩ = (†` L rel-L) · (†` M rel-M)
                †` (`let L M) ⟨ rel-L , rel-M ⟩ = (ƛ (†` M rel-M)) · †` L rel-L

        module WithoutReflectionTrick where

            data Relevant : {Γ : Context} {A : Type} 
                        → (Γ ⊢ A) → Set 
                        where
                
                rel-` : {Γ : Context} {A : Type} {M : Γ ∋ A}
                    → Relevant (` M)

                rel-ƛ : {Γ : Context} {A B : Type} {N : Γ , A ⊢ B}
                    → Relevant N
                    → Relevant (ƛ N)

                rel-· : {Γ : Context} {A B : Type} {N : Γ ⊢ A ⇒ B} {M : Γ ⊢ A}
                    → Relevant N
                    → Relevant M
                    → Relevant (N · M)

                rel-let : {Γ : Context} {A B : Type} {N : Γ , A ⊢ B} {M : Γ ⊢ A}
                        → Relevant M
                        → Relevant N
                        → Relevant (`let M N)

            _⊢ᵣ_ : Context → Type → Set
            Γ ⊢ᵣ t = Σ[ M ∈ Γ ⊢ t ] Relevant M

            _† : {Γ : Context} {A : Type} 
                → Γ ⊢ᵣ A
                → Γ ⊢ A
            ⟨ ` x , rel-M ⟩ † = ` x
            ⟨ ƛ M , rel-ƛ rel-M ⟩ † = ƛ (⟨ M , rel-M ⟩ †)
            ⟨ L · M , rel-· rel-L rel-M ⟩ † = (⟨ L , rel-L ⟩ †) · (⟨ M , rel-M ⟩ †)
            ⟨ `let L M , rel-let rel-L rel-M ⟩ † = (ƛ (⟨ M , rel-M ⟩ †)) · (⟨ L , rel-L ⟩ †)

        open WithoutReflectionTrick

        term : {Γ : Context} {A : Type}
             → Γ ⊢ᵣ A
             → Γ ⊢ A
        term = proj₁

        †→~ : {Γ : Context} {A : Type} {M : Γ ⊢ᵣ A} {N : Γ ⊢ A}
            → (M †) ≡ N
            → (term M) ~ N
        †→~ {M = ⟨ .(` _) , rel-` ⟩} {N = .(⟨ ` _ , rel-` ⟩ †)} refl = ~`
        †→~ {M = ⟨ .(ƛ _) , rel-ƛ rel-N ⟩} {N = .(⟨ ƛ _ , rel-ƛ rel-N ⟩ †)} refl = ~ƛ (†→~ refl)
        †→~ {M = ⟨ .(_ · _) , rel-· L M ⟩} {N = .(⟨ _ · _ , rel-· L M ⟩ †)} refl = (†→~ refl) ~· (†→~ refl)
        †→~ {M = ⟨ .(`let _ _) , rel-let L M ⟩} {N = .(⟨ `let _ _ , rel-let L M ⟩ †)} refl = ~let (†→~ refl) (†→~ refl)

    module Exercise2 where
        open Exercise1

        ~val : {Γ : Context} {A : Type} {M M† : Γ ⊢ A}
            → M ~ M†
            → Value M
            --------
            → Value M†
        ~val ~`           ()
        ~val (~ƛ ~N)      V-ƛ  =  V-ƛ
        ~val (~L ~· ~M)   ()
        ~val (~let ~M ~N) ()

        ~val⁻¹ : {Γ : Context} {A : Type} {M M† : Γ ⊢ A}
            → M ~ M†
            → Value M†
            --------
            → Value M
        ~val⁻¹ (~ƛ ~N) V-ƛ = V-ƛ

    module Exercise3 where

        open Exercise1

        open Exercise2 using (~val)

        ~rename : ∀ {Γ Δ}
            → (ρ : ∀ {A} → Γ ∋ A → Δ ∋ A)
            ----------------------------------------------------------
            → (∀ {A} {M M† : Γ ⊢ A} → M ~ M† → rename ρ M ~ rename ρ M†)
        ~rename ρ (~`)          =  ~`
        ~rename ρ (~ƛ ~N)       =  ~ƛ (~rename (ext ρ) ~N)
        ~rename ρ (~L ~· ~M)    =  (~rename ρ ~L) ~· (~rename ρ ~M)
        ~rename ρ (~let ~M ~N)  =  ~let (~rename ρ ~M) (~rename (ext ρ) ~N)

        _~ₛ_ : ∀ {Γ Δ} → (Γ ⇒ₛ Δ) → (Γ ⇒ₛ Δ) → Set
        _~ₛ_ {Γ} {Δ} σ σ† = ∀ {A} → (x : Γ ∋ A) → σ x ~ σ† x

        ~exts : ∀ {Γ Δ A}
            → {σ  : Γ ⇒ₛ Δ}
            → {σ† : Γ ⇒ₛ Δ}
            → (σ ~ₛ σ†)
            --------------------------------------------------
            → ((exts σ {A = A}) ~ₛ (exts σ† {A = A}))
        ~exts ~σ Z      =  ~`
        ~exts ~σ (S x)  =  ~rename S_ (~σ x)

        ~subst : ∀ {Γ Δ}
            → {σ  : ∀ {A} → Γ ∋ A → Δ ⊢ A}
            → {σ† : ∀ {A} → Γ ∋ A → Δ ⊢ A}
            → (∀ {A} → (x : Γ ∋ A) → σ x ~ σ† x)
            ---------------------------------------------------------
            → (∀ {A} {M M† : Γ ⊢ A} → M ~ M† → subst σ M ~ subst σ† M†)
        ~subst ~σ (~` {x = x}) = ~σ x
        ~subst ~σ (~ƛ N~N†) = ~ƛ ~subst (~exts ~σ) N~N†
        ~subst ~σ (L~L† ~· M~M†) = (~subst ~σ L~L†) ~· (~subst ~σ M~M†)
        ~subst ~σ (~let L~L† N~N†) = ~let (~subst ~σ L~L†) (~subst (~exts ~σ) N~N†)

        ~sub : ∀ {Γ A B} {N N† : Γ , B ⊢ A} {M M† : Γ ⊢ B}
            → N ~ N†
            → M ~ M†
            -----------------------
            → (N [ M ]) ~ (N† [ M† ])
        ~sub {Γ} {A} {B} ~N ~M = ~subst {Γ , B} {Γ} ~σ {A} ~N
            where
            ~σ : ∀ {A} → (x : Γ , B ∋ A) → _ ~ _
            ~σ Z      =  ~M
            ~σ (S x)  =  ~`

        data Leg {Γ : Context} {A : Type} (M† N : Γ ⊢ A) : Set where
            
            leg : {N† : Γ ⊢ A}
                → N ~ N†
                → M† —→ N†
                → Leg M† N

        sim : {Γ : Context} {A : Type} {M† M N : Γ ⊢ A}
            → M ~ M†
            → M —→ N
            → Leg M† N
        sim (L~L† ~· M~M†) (ξ-·₁ L—→L`) with sim L~L† L—→L`
        ... | leg L`~L`† L†—→L`† = leg (L`~L`† ~· M~M†) (ξ-·₁ L†—→L`†)
        sim (L~L† ~· M~M†) (ξ-·₂ V-L M—→M`) with sim M~M† M—→M`
        ... | leg M`~M`† M†—→M′† = leg (L~L† ~· M`~M`†) (ξ-·₂ (~val L~L† V-L) M†—→M′†)
        sim ((~ƛ L~L†) ~· M~M†) (β-ƛ V-M) = leg (~sub L~L† M~M†) (β-ƛ (~val M~M† V-M))
        sim (~let M~M† N~N†) (ξ-let M—→M`) with sim M~M† M—→M`
        ... | leg M`~M`† M†—→M`† = leg (~let M`~M`† N~N†) (ξ-·₂ V-ƛ M†—→M`†)
        sim (~let M~M† N~N†) (β-let V-M) = leg (~sub N~N† M~M†) (β-ƛ (~val M~M† V-M))

        data Arm {Γ : Context} {A : Type} (M N† : Γ ⊢ A) : Set where

            arm : {N : Γ ⊢ A}
                → N ~ N†
                → M —→ N
                → Arm M N†

        ~val⁻¹ : {Γ : Context} {A : Type} {M M† : Γ ⊢ A}
            → M ~ M†
            → Value M†
            --------
            → Value M
        ~val⁻¹ (~ƛ M~M†) V-M† = V-ƛ

        sim⁻¹ : {Γ : Context} {A : Type} {M M† N† : Γ ⊢ A}
              → M ~ M†
              → M† —→ N†
              → Arm M N†
        sim⁻¹ (L~L† ~· M~M†) (ξ-·₁ L†—→L`†) with sim⁻¹ L~L† L†—→L`†
        ... | arm L`~L`† L—→L` = arm (L`~L`† ~· M~M†) (ξ-·₁ L—→L`)
        sim⁻¹ (L~L† ~· M~M†) (ξ-·₂ V-L† M†—→M`†) with sim⁻¹ M~M† M†—→M`†
        ... | arm M`~M`† M—→M` = arm (L~L† ~· M`~M`†) (ξ-·₂ (~val⁻¹ L~L† V-L†) M—→M`)
        sim⁻¹ ((~ƛ L~L†) ~· M~M†) (β-ƛ V-M†) = arm (~sub L~L† M~M†) (β-ƛ (~val⁻¹ M~M† V-M†))
        sim⁻¹ (~let L~L† M~M†) (ξ-·₂ V-M† L†—→L`†) with sim⁻¹ L~L† L†—→L`†
        ... | arm L`~L`† L—→L` = arm (~let L`~L`† M~M†) (ξ-let L—→L`)
        sim⁻¹ (~let L~L† M~M†) (β-ƛ V-L†) = arm (~sub M~M† L~L†) (β-let (~val⁻¹ L~L† V-L†))

    module Exercise4 where

        weaken : {Γ : Context} {A B : Type}
               → Γ ⊢ B
               → Γ , A ⊢ B
        weaken t = rename S_ t

        infix  4 _~_
        infix  5 ~ƛ_
        infix  7 _~·_

        data _~_ : ∀ {Γ A} → (Γ ⊢ A) → (Γ ⊢ A) → Set where

            ~` : ∀ {Γ A} {x : Γ ∋ A}
                ---------
                → ` x ~ ` x

            ~ƛ_ : ∀ {Γ A B} {N N† : Γ , A ⊢ B}
                → N ~ N†
                ----------
                → ƛ N ~ ƛ N†

            _~·_ : ∀ {Γ A B} {L L† : Γ ⊢ A ⇒ B} {M M† : Γ ⊢ A}
                → L ~ L†
                → M ~ M†
                ---------------
                → L · M ~ L† · M†

            ~⟨_,_⟩ : {Γ : Context} {A B : Type} {L L† : Γ ⊢ A} {M M† : Γ ⊢ B}
                   → L ~ L†
                   → M ~ M†
                   → `⟨ L , M ⟩ ~ `⟨ L† , M† ⟩

            ~proj₁ : {Γ : Context} {A B : Type} {L L† : Γ ⊢ A `× B}
                   → L ~ L†   
                   → `proj₁ L ~ case× L† (# 1)
                   
            ~proj₂ : {Γ : Context} {A B : Type} {L L† : Γ ⊢ A `× B}
                   → L ~ L†   
                   → `proj₂ L ~ case× L† (# 0)
            
        _⇒ᵣ_ : Context → Context → Set
        Γ ⇒ᵣ Δ = ∀ {A} → Γ ∋ A → Δ ∋ A

        _~ₛ_ : ∀ {Γ Δ} → Γ ⇒ₛ Δ → Γ ⇒ₛ Δ → Set
        σ ~ₛ σ† = ∀ {A} (x : _ ∋ A) → σ x ~ σ† x
        
        ~rename : ∀ {Γ Δ}
            → (ρ : ∀ {A} → Γ ∋ A → Δ ∋ A)
            ----------------------------------------------------------
            → (∀ {A} {M M† : Γ ⊢ A} → M ~ M† → rename ρ M ~ rename ρ M†)
        ~rename σ ~` = ~`
        ~rename σ (~ƛ N~N†) = ~ƛ (~rename (ext σ) N~N†)
        ~rename σ (L~L† ~· M~M†) = (~rename σ L~L†) ~· (~rename σ M~M†)
        ~rename σ ~⟨ L~L† , M~M† ⟩ = ~⟨ (~rename σ L~L†) , (~rename σ M~M†) ⟩
        ~rename σ (~proj₁ L~L†) = ~proj₁ (~rename σ L~L†)
        ~rename σ (~proj₂ L~L†) = ~proj₂ (~rename σ L~L†)

        ~exts : ∀ {Γ Δ A} {σ σ† : Γ ⇒ₛ Δ}
            → σ ~ₛ σ†
            -----------------
            → exts σ {A = A} ~ₛ exts σ† {A = A}
        ~exts σ~σ† Z = ~`
        ~exts σ~σ† (S ∋x) = ~rename S_ (σ~σ† ∋x)

        ~subst : ∀ {Γ Δ A} {M M† : Γ ⊢ A} {σ σ† : Γ ⇒ₛ Δ}
            → σ ~ₛ σ†
            → M ~ M†
                ------------------------
            → subst σ M ~ subst σ† M†
        ~subst σ~σ† (~` {x = x}) = σ~σ† x
        ~subst σ~σ† (~ƛ M~M†) = ~ƛ (~subst (~exts σ~σ†) M~M†)
        ~subst σ~σ† (L~L† ~· M~M†) = (~subst σ~σ† L~L†) ~· ~subst σ~σ† M~M†
        ~subst σ~σ† ~⟨ L~L† , M~M† ⟩ = ~⟨ (~subst σ~σ† L~L†) , (~subst σ~σ† M~M†) ⟩
        ~subst σ~σ† (~proj₁ M~M†) = ~proj₁ (~subst σ~σ† M~M†)
        ~subst σ~σ† (~proj₂ M~M†) = ~proj₂ (~subst σ~σ† M~M†)

        ~substZero : ∀ {Γ A} {M M† : Γ ⊢ A}
            → M ~ M†
            → substZero M ~ₛ substZero M†
        ~substZero M~M† Z = M~M†
        ~substZero M~M† (S ∋x) = ~`

        ~sub : ∀ {Γ A B} {N N† : Γ , B ⊢ A} {M M† : Γ ⊢ B}
            → N ~ N†
            → M ~ M†
            -----------------------
            → (N [ M ]) ~ (N† [ M† ])
        ~sub N~N† M~M† = ~subst (~substZero M~M†) N~N†

        ~val : ∀ {Γ A} {M M† : Γ ⊢ A}
            → M ~ M†
            → Value M
            --------
            → Value M†
        ~val (~ƛ M~M†)            val-M                 = V-ƛ
        ~val ~⟨ M₁~M₁† , M₂~M₂† ⟩ V-⟨ val-M₁ , val-M₂ ⟩ = V-⟨ ~val M₁~M₁† val-M₁ , ~val M₂~M₂† val-M₂ ⟩

        sim : ∀ {Γ A} {M M† M` : Γ ⊢ A}
            → M ~ M†
            → M —→ M`
            -----------------------------
            → ∃[ M`† ] (M` ~ M`†) × (M† —→ M`†)
        sim (L~L† ~· M~M†) (ξ-·₁ L—→L`) with sim L~L† L—→L`
        ... | ⟨ M`† , ⟨ L`~L`† , L†—→L`† ⟩ ⟩ = 
            ⟨ _ , ⟨ ((L`~L`† ~· M~M†)) , ((ξ-·₁ L†—→L`†)) ⟩ ⟩
        sim (L~L† ~· M~M†) (ξ-·₂ V-L M—→M`) with sim M~M† M—→M`
        ... | ⟨ _ , ⟨ M`~M`† , M†—→M′† ⟩ ⟩ = 
            ⟨ _ , ⟨ L~L† ~· M`~M`† , (ξ-·₂ (~val L~L† V-L) M†—→M′†) ⟩ ⟩
        sim ((~ƛ L~L†) ~· M~M†) (β-ƛ V-M) = 
            ⟨ _ , ⟨ (~sub L~L† M~M†) , (β-ƛ (~val M~M† V-M)) ⟩ ⟩ 
        sim ~⟨ L~L† , M~M† ⟩ (ξ-⟨,⟩₁ L—→L`) with sim L~L† L—→L`
        ... | ⟨ _ , ⟨ L`~L`† , L†—→L`† ⟩ ⟩ = 
            ⟨ _ , ⟨ ~⟨ L`~L`† , M~M† ⟩ , ξ-⟨,⟩₁ L†—→L`† ⟩ ⟩
        sim ~⟨ L~L† , M~M† ⟩ (ξ-⟨,⟩₂ V-L M—→M`) with sim M~M† M—→M`
        ... | ⟨ _ , ⟨ M`~M`† , M†—→M`† ⟩ ⟩ = 
            ⟨ _ , ⟨ ~⟨ L~L† , M`~M`† ⟩ , ξ-⟨,⟩₂ (~val L~L† V-L) M†—→M`† ⟩ ⟩
        sim (~proj₁ L~L†) (ξ-proj₁ L—→L`) with sim L~L† L—→L`
        ... | ⟨ _ , ⟨ L`~L`† , L†—→L`† ⟩ ⟩ = 
            ⟨ _ , ⟨ (~proj₁ L`~L`†) , ξ-case× L†—→L`† ⟩ ⟩
        sim (~proj₁ ~⟨ L~L† , M~M† ⟩) (β-proj₁ V-L V-M) =
            ⟨ _ , ⟨ L~L† , β-case× (~val L~L† V-L) (~val M~M† V-M) ⟩ ⟩
        sim (~proj₂ L~L†) (ξ-proj₂ L—→L`) with sim L~L† L—→L`
        ... | ⟨ _ , ⟨ L`~L`† , L†—→L`† ⟩ ⟩ = 
            ⟨ _ , ⟨ (~proj₂ L`~L`†) , (ξ-case× L†—→L`†) ⟩ ⟩
        sim (~proj₂ ~⟨ L~L† , M~M† ⟩) (β-proj₂ V-L V-M) = 
            ⟨ _ , ⟨ M~M† , (β-case× ((~val L~L† V-L)) ((~val M~M† V-M))) ⟩ ⟩

        ~val⁻¹ : ∀ {Γ A} {M M† : Γ ⊢ A}
            → M ~ M†
            → Value M†
            --------
            → Value M
        ~val⁻¹ (~ƛ M~M†)            val-M†                  = V-ƛ
        ~val⁻¹ ~⟨ M₁~M₁† , M₂~M₂† ⟩ V-⟨ val-M₁† , val-M₂† ⟩ = V-⟨ ~val⁻¹ M₁~M₁† val-M₁† , ~val⁻¹ M₂~M₂† val-M₂† ⟩

        sim⁻¹ : ∀ {Γ A} {M M† M′† : Γ ⊢ A}
            → M ~ M†
            → M† —→ M′†
            → ∃[ M′ ] (M′ ~ M′†) × (M —→ M′)
        sim⁻¹ (L~L† ~· M~M†) (ξ-·₁ L†—→L`†) with sim⁻¹ L~L† L†—→L`†
        ... | ⟨ _ , ⟨ L`~L`† , L—→L` ⟩ ⟩ = 
            ⟨ _ , ⟨ ((L`~L`† ~· M~M†)) , ((ξ-·₁ L—→L`)) ⟩ ⟩
        sim⁻¹ (L~L† ~· M~M†) (ξ-·₂ V-L† M†—→M`†) with sim⁻¹ M~M† M†—→M`†
        ... | ⟨ _ , ⟨ M`~M`† , M—→M` ⟩ ⟩ = 
            ⟨ _ , ⟨ ((L~L† ~· M`~M`†)) , ((ξ-·₂ (~val⁻¹ L~L† V-L†) M—→M`)) ⟩ ⟩
        sim⁻¹ ((~ƛ L~L†) ~· M~M†) (β-ƛ V-M†) = 
            ⟨ _ , ⟨ (~sub L~L† M~M†) , (β-ƛ (~val⁻¹ M~M† V-M†)) ⟩ ⟩
        -- TODO: rename
        sim⁻¹ ~⟨ L~L† , M~M† ⟩ (ξ-⟨,⟩₁ L—→L`) with sim⁻¹ L~L† L—→L`
        ... | ⟨ _ , ⟨ L`~L`† , L†—→L`† ⟩ ⟩ = 
            ⟨ _ , ⟨ ~⟨ L`~L`† , M~M† ⟩ , (ξ-⟨,⟩₁ L†—→L`†) ⟩ ⟩
        sim⁻¹ ~⟨ L~L† , M~M† ⟩ (ξ-⟨,⟩₂ V-L† M†—→M`†) with sim⁻¹ M~M† M†—→M`†
        ... | ⟨ _ , ⟨ M`~M`† , M—→M` ⟩ ⟩ = 
            ⟨ _ , ⟨ ~⟨ L~L† , M`~M`† ⟩ , (ξ-⟨,⟩₂ (~val⁻¹ L~L† V-L†) M—→M`) ⟩ ⟩
        sim⁻¹ (~proj₁ L~L†) (ξ-case× L†—→L`†) with sim⁻¹ L~L† L†—→L`†
        ... | ⟨ _ , ⟨ L`~L`† , L—→L` ⟩ ⟩ = 
            ⟨ _ , ⟨ ~proj₁ L`~L`† , ξ-proj₁ L—→L` ⟩ ⟩
        sim⁻¹ (~proj₁ ~⟨ L~L† , M~M† ⟩) (β-case× V-L V-M) = 
            ⟨ _ , ⟨ L~L† , (β-proj₁ (~val⁻¹ L~L† V-L) (~val⁻¹ M~M† V-M)) ⟩ ⟩
        sim⁻¹ (~proj₂ L~L†) (ξ-case× L†—→L`†) with sim⁻¹ L~L† L†—→L`†
        ... | ⟨ _ , ⟨ L`~L`† , L—→L` ⟩ ⟩ = 
            ⟨ _ , ⟨ (~proj₂ L`~L`†) , (ξ-proj₂ L—→L`) ⟩ ⟩
        sim⁻¹ (~proj₂ ~⟨ L~L† , M~M† ⟩) (β-case× V-L V-M) = 
            ⟨ _ , ⟨ M~M† , (β-proj₂ (~val⁻¹ L~L† V-L) (~val⁻¹ M~M† V-M)) ⟩ ⟩
        
