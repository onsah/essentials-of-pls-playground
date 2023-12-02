module Language where
    open import Data.Nat
    open import Data.Bool
    
    infixr 3 _`+_

    data Expr : Set where
        bool : Bool → Expr
        nat : ℕ → Expr
        _`+_ : Expr → Expr → Expr
        _`==_ : Expr → Expr → Expr

        {- example : Expr
        example = nat 5 `+ nat 3 -}

    data Type : Set where
        `Nat : Type
        `Bool : Type

    data _`:_ : Expr → Type → Set where
        T-nat : ∀ {n} → nat n `: `Nat
        T-+ : ∀ {a b}
            → (a `+ b) `: `Nat

        T-bool : ∀ {b} → bool b `: `Bool
        T-== : ∀ {a b t}
            → a `: t
            → b `: t
            → (a `== b) `: `Bool
     