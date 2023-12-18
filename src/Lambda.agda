open import Data.Bool using (Bool; true; false; T; not)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; _∷_; [])
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (∃-syntax; _×_; _,_)
open import Data.String using (String; _≟_)
open import Data.Unit using (tt)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Nullary.Decidable using (False; toWitnessFalse)
open import Relation.Nullary.Negation using (¬?)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong)
open import Isomorphism using (_≃_; _∘_)
open Isomorphism.≃-Reasoning

module Lambda where
    Id : Set
    Id = String

    infix  5  ƛ_⇒_
    infix  5  μ_⇒_
    infixl 7  _·_
    infix  8  `suc_
    infix  9  `_

    data Term : Set where
        `_                      :  Id → Term
        ƛ_⇒_                    :  Id → Term → Term
        _·_                     :  Term → Term → Term
        `zero                   :  Term
        `suc_                   :  Term → Term
        case_[zero⇒_|suc_⇒_]    :  Term → Term → Id → Term → Term
        μ_⇒_                    :  Id → Term → Term

    two : Term
    two = `suc `suc `zero

    plus : Term
    plus = μ "+" ⇒ ƛ "m" ⇒ ƛ "n" ⇒
                case ` "m"
                    [zero⇒ ` "n"
                    |suc "m" ⇒ `suc ( ` "+" · ` "m" · ` "n" ) ]

    twoᶜ : Term
    twoᶜ = ƛ "s" ⇒ ƛ "z" ⇒ ` "s" · (` "s" · ` "z")
    
    plusᶜ : Term
    plusᶜ = ƛ "m" ⇒ ƛ "n" ⇒
            ƛ "s" ⇒ ƛ "z" ⇒
                ` "m" · ` "s" · (` "n" · ` "s" · ` "z") 

    mul : Term
    mul = μ "x" ⇒
          ƛ "m" ⇒ ƛ "n" ⇒
            case ` "m"
                [zero⇒ `zero
                |suc "m" ⇒ plus · (` "n") · (` "x" · ` "m" · ` "n")  ]

    mulᶜ : Term
    mulᶜ = μ "x" ⇒
           ƛ "m" ⇒ ƛ "n" ⇒
           ƛ "s" ⇒ ƛ "z" ⇒
            ` "m" · (` "n" · ` "s") · ` "z" 

    data Value : Term → Set where
        V-ƛ : ∀ {x N}
            ---------------
            → Value (ƛ x ⇒ N)

        V-zero :
            -----------
            Value `zero

        V-suc : ∀ {V}
            → Value V
            --------------
            → Value (`suc V)

    infix 9 _[_:=_]

    _[_:=_] : Term → Id → Term → Term
    (` x) [ y := V ] with x ≟ y
    ... | no  _ = ` x
    ... | yes refl = V
    (ƛ x ⇒ N) [ y := V ] with x ≟ y
    ... | yes _         = ƛ x ⇒ N
    ... | no  _         = ƛ x ⇒ N [ y := V ]
    (L · M) [ y := V ]  = L [ y := V ] · M [ y := V ]
    (`zero) [ y := V ]  = `zero
    (`suc M) [ y := V ] = `suc M [ y := V ]
    (case L [zero⇒ M |suc x ⇒ N ]) [ y := V ] with x ≟ y
    ... | yes _         = case L [ y := V ] [zero⇒ M [ y := V ] |suc x ⇒ N ]
    ... | no  _         = case L [ y := V ] [zero⇒ M [ y := V ] |suc x ⇒ N [ y := V ] ]
    (μ x ⇒ N) [ y := V ] with x ≟ y
    ... | yes _         = μ x ⇒ N
    ... | no  _         = μ x ⇒ N [ y := V ]

    infix 4 _—→_

    data _—→_ : Term → Term → Set where
        ξ-·₁ : ∀ {L L` M}
            → L —→ L`
            → L · M —→ L` · M

        ξ-·₂ : ∀ {V M M`}
            → Value V
            → M —→ M`
            → V · M —→ V · M`

        β-ƛ : ∀ {x N V}
            → Value V
            → (ƛ x ⇒ N) · V —→ N [ x := V ]

        ξ-suc : ∀ {M M`}
            → M —→ M`
            → `suc M —→ `suc M` 

        ξ-case : ∀ {M M` s Z S}
            → M —→ M`
            → case M [zero⇒ Z |suc s ⇒ S ] —→ case M` [zero⇒ Z |suc s ⇒ S ]

        β-zero : ∀ {s Z S}
            → case `zero [zero⇒ Z |suc s ⇒ S ] —→ Z

        β-suc : ∀ {Vs s Z S}
            → Value Vs
            → case `suc Vs [zero⇒ Z |suc s ⇒ S ] —→ S [ s := Vs ]

        β-μ : ∀ {x M}
            → μ x ⇒ M —→ M [ x := μ x ⇒ M ]

    infix  2 _—↠_
    infix  1 begin_
    infixr 2 _—→⟨_⟩_
    infix  3 _∎

    data _—↠_ : Term → Term → Set where
        _∎ : ∀ M
            → M —↠ M

        step—→ : ∀ L {M N}
            → M —↠ N
            → L —→ M
            → L —↠ N

    pattern _—→⟨_⟩_ L L—→M M—↠N = step—→ L M—↠N L—→M
    
    begin_ : ∀ {M N}
        → M —↠ N
        → M —↠ N
    begin M—↠N = M—↠N

    step—↠ : {l m n : Term}
        → l —↠ m
        → m —↠ n
        → l —↠ n
    step—↠ (_ ∎) m—↠n = m—↠n
    step—↠ (_ —→⟨ l—→x ⟩ x—↠m) m—↠n = _ —→⟨ l—→x ⟩ step—↠ x—↠m m—↠n
    
    data _—↠′_ : Term → Term → Set where

        step′ : {m n : Term}
            → m —→ n
            -------
            → m —↠′ n

        refl′ : {m : Term}
            -------
            → m —↠′ m
            
        trans′ : {l m n : Term}
            → l —↠′ m
            → m —↠′ n
            -------
            → l —↠′ n

    open import Isomorphism using (_≲_; extensionality)

    —↠→—↠′ : ∀ {M N}
        → M —↠ N → M —↠′ N
    —↠→—↠′ (_ ∎) = refl′
    —↠→—↠′ (l —→⟨ L—→M ⟩ M—↠N) = trans′ (step′ L—→M) (—↠→—↠′ M—↠N)

    —↠′→—↠ : {m n : Term}
        → m —↠′ n → m —↠ n
    —↠′→—↠ refl′ = _ ∎
    —↠′→—↠ {m = m} {n = n} (step′ m—→n) = m —→⟨ m—→n ⟩ n ∎
    —↠′→—↠ (trans′ l—↠′m m—↠′n) = step—↠ (—↠′→—↠ l—↠′m) (—↠′→—↠ m—↠′n)

    —↠-from∘to-—↠′ : ∀ {m n : Term}
        → (m—↠n : m —↠ n)
        → (—↠′→—↠ ( —↠→—↠′ m—↠n)) ≡ m—↠n
    —↠-from∘to-—↠′ (_ ∎) = refl
    —↠-from∘to-—↠′ (_ —→⟨ m—→m₁ ⟩ m₁—↠n) = 
        let
            ind = —↠-from∘to-—↠′ m₁—↠n
        in
            cong (λ x → _ —→⟨ m—→m₁ ⟩ x) ind

    —↠≲—↠′ : {m n : Term} 
        → m —↠ n ≲ m —↠′ n
    —↠≲—↠′ {m = m} {n = n} = 
        record { 
            to = —↠→—↠′; 
            from = —↠′→—↠ ; 
            from∘to = —↠-from∘to-—↠′
        }
    
    postulate
        confluence : ∀ {l m n}
            → ((l —↠ m) × (l —↠ n))
            --------------------
            → ∃[ p ] ((m —↠ p) × (n —↠ p))

        diamond : ∀ {l m n}
            → ((l —→ m) × (l —→ n))
            --------------------
            → ∃[ p ] ((m —↠ p) × (n —↠ p))

    postulate
        deterministic : ∀ {l m n}
            → l —→ m
            → l —→ n
            ------
            → m ≡ n

    one : Term
    one = `suc `zero

    _ : plus · one · one —↠ `suc `suc `zero
    _ = begin 
            plus · one · one 
        —→⟨ ξ-·₁ (ξ-·₁ β-μ) ⟩ 
            (ƛ "m" ⇒ ƛ "n" ⇒
                case ` "m"
                    [zero⇒ ` "n"
                    |suc "m" ⇒ `suc ( plus · ` "m" · ` "n" ) ] ) 
                · one 
                · one
        —→⟨ ξ-·₁ (β-ƛ (V-suc V-zero)) ⟩ 
            (ƛ "n" ⇒
                case (`suc `zero)
                    [zero⇒ ` "n"
                    |suc "m" ⇒ `suc ( plus · ` "m" · ` "n" ) ] ) 
                · one
        —→⟨ β-ƛ (V-suc V-zero) ⟩ 
            case (`suc `zero)
                [zero⇒ (`suc `zero)
                |suc "m" ⇒ `suc ( plus · ` "m" · (`suc `zero) ) ] 
        —→⟨ β-suc V-zero ⟩ 
            `suc ( plus · `zero · (`suc `zero) )
        —→⟨ ξ-suc (ξ-·₁ (ξ-·₁ β-μ)) ⟩ 
            `suc ( 
                (ƛ "m" ⇒ ƛ "n" ⇒
                    case ` "m"
                        [zero⇒ ` "n"
                        |suc "m" ⇒ `suc ( plus · ` "m" · ` "n" ) ] )
                · `zero 
                · (`suc `zero) )
        —→⟨ ξ-suc (ξ-·₁ (β-ƛ V-zero)) ⟩ 
            `suc ( 
                (ƛ "n" ⇒
                    case `zero
                        [zero⇒ ` "n"
                        |suc "m" ⇒ `suc ( plus · ` "m" · ` "n" ) ] )
                · (`suc `zero) )
        —→⟨ ξ-suc (β-ƛ (V-suc V-zero)) ⟩ 
            `suc ( 
                (case `zero
                        [zero⇒ (`suc `zero)
                        |suc "m" ⇒ `suc ( plus · ` "m" · (`suc `zero) ) ] ))
        —→⟨ ξ-suc β-zero ⟩ 
            `suc (`suc `zero) 
        ∎

    infixr 7 _⇒_

    data Type : Set where
        _⇒_ : Type → Type → Type
        `ℕ : Type

    infixl 5  _,_⦂_

    data Context : Set where
        ∅     : Context
        _,_⦂_ : Context → Id → Type → Context
    
    infix  4  _∋_⦂_

    Context→List_Id×Type_ : Context → List (Id × Type)
    Context→List_Id×Type_ ∅ = []
    Context→List_Id×Type_ (context , x ⦂ t) = 
        (x , t) ∷ (Context→List_Id×Type_ context) 

    List_Id×Type_→Context : List (Id × Type) → Context
    List_Id×Type_→Context [] = ∅
    List_Id×Type_→Context ((x , t) ∷ list) = 
        (List_Id×Type_→Context list), x ⦂ t

    Context_from∘to_List_Id×Type_ : (x : Context) 
        → ((List_Id×Type_→Context ∘ Context→List_Id×Type_) x) ≡ x
    Context_from∘to_List_Id×Type_ ∅ = refl
    Context_from∘to_List_Id×Type_ (context , x ⦂ t) = 
        let
            ind = Context_from∘to_List_Id×Type_ context
        in 
            cong (λ context → context , x ⦂ t) ind

    Context_to∘from_List_Id×Type_ : (list : List (Id × Type))
        → ((Context→List_Id×Type_ ∘ List_Id×Type_→Context) list) ≡ list
    Context_to∘from_List_Id×Type_ [] = refl
    Context_to∘from_List_Id×Type_ ((x , t) ∷ list) = 
        let
            ind = Context_to∘from_List_Id×Type_ list
        in
            cong (λ list → (x , t) ∷ list) ind

    Context-≃ : Context ≃ List (Id × Type)
    Context-≃ = 
        record { 
            to = Context→List_Id×Type_; 
            from = List_Id×Type_→Context; 
            from∘to = Context_from∘to_List_Id×Type_; 
            to∘from = Context_to∘from_List_Id×Type_ 
        }

    data _∋_⦂_ : Context → Id → Type → Set where

        Z : ∀ {Γ x A}
            ------------------
            → (Γ , x ⦂ A) ∋ x ⦂ A

        S : ∀ {Γ x y A B}
            → x ≢ y
            → Γ ∋ x ⦂ A
            ------------------
            → (Γ , y ⦂ B) ∋ x ⦂ A

    infix  4  _⊢_⦂_

    data _⊢_⦂_ : Context → Term → Type → Set where

        -- Axiom
        ⊢` : ∀ {Γ x A}
            → Γ ∋ x ⦂ A
            -----------
            → Γ ⊢ ` x ⦂ A

        -- ⇒-I
        ⊢ƛ : ∀ {Γ x N A B}
            → Γ , x ⦂ A ⊢ N ⦂ B
            -------------------
            → Γ ⊢ ƛ x ⇒ N ⦂ A ⇒ B

        -- ⇒-E
        _·_ : ∀ {Γ L M A B}
            → Γ ⊢ L ⦂ A ⇒ B
            → Γ ⊢ M ⦂ A
            -------------
            → Γ ⊢ L · M ⦂ B

        -- ℕ-I₁
        ⊢zero : ∀ {Γ}
            --------------
            → Γ ⊢ `zero ⦂ `ℕ

        -- ℕ-I₂
        ⊢suc : ∀ {Γ M}
            → Γ ⊢ M ⦂ `ℕ
            ---------------
            → Γ ⊢ `suc M ⦂ `ℕ

        -- ℕ-E
        ⊢case : ∀ {Γ L M x N A}
            → Γ ⊢ L ⦂ `ℕ
            → Γ ⊢ M ⦂ A
            → Γ , x ⦂ `ℕ ⊢ N ⦂ A
            -------------------------------------
            → Γ ⊢ case L [zero⇒ M |suc x ⇒ N ] ⦂ A

        ⊢μ : ∀ {Γ x M A}
            → Γ , x ⦂ A ⊢ M ⦂ A
            -----------------
            → Γ ⊢ (μ x ⇒ M) ⦂ A
    