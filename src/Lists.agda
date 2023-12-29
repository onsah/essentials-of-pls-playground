import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong; cong-app)
open Eq.≡-Reasoning
open import Data.Bool using (Bool; true; false; T; _∧_; _∨_; not)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _≤_; s≤s; z≤n)
open import Data.Nat.Properties using
  (+-assoc; +-identityˡ; +-identityʳ; *-assoc; *-identityˡ; *-identityʳ; *-distribʳ-+; *-distribˡ-∸; +-∸-assoc; m≤m*n; +-comm; *-monoʳ-≤; *-comm; +-∸-comm; ≤-refl; n∸n≡0)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Data.Product using (_×_; ∃; ∃-syntax) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function using (_∘_)
open import Level using (Level)
open import Isomorphism using (_≃_; _⇔_; extensionality)

module Lists where
  data List (A : Set) : Set where
    [] : List A
    _::_ : A → List A → List A

  infixr 5 _::_
    
  _++_ : ∀ {A : Set} → List A → List A → List A
  [] ++ ys = ys
  (x :: xs) ++ ys = x :: (xs ++ ys)

  infixr 5 _++_

  ++-assoc : ∀ {A : Set} (xs ys zs : List A) 
    → (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
  ++-assoc [] ys zs = refl
  ++-assoc (x :: xs) ys zs = 
    begin 
      (x :: xs ++ ys) ++ zs
    ≡⟨⟩ 
      x :: ((xs ++ ys) ++ zs)
    ≡⟨ cong (x ::_) (++-assoc xs ys zs) ⟩
      x :: xs ++ (ys ++ zs)
    ≡⟨⟩
      (x :: xs) ++ (ys ++ zs) 
    ∎

  ++-identityˡ : ∀ {A : Set} (xs : List A) 
    → [] ++ xs ≡ xs
  ++-identityˡ [] = refl
  ++-identityˡ (x :: xs) = refl

  ++-identityʳ : ∀ {A : Set} (xs : List A)
    → xs ++ [] ≡ xs
  ++-identityʳ [] = refl
  ++-identityʳ (x :: xs) = cong (x ::_) (++-identityʳ xs)

  length : {A : Set} → List A → ℕ
  length []        = zero
  length (_ :: xs) = suc (length xs)

  length-++ : {A : Set} (xs ys : List A)
    → length (xs ++ ys) ≡ (length xs) + (length ys)
  length-++ [] ys = refl
  length-++ (x :: xs) ys = cong suc (length-++ xs ys)

  reverse : ∀ {A : Set} → List A → List A
  reverse [] = []
  reverse (x :: xs) = (reverse xs) ++ (x :: [])

  reverse-++-distrib : {A : Set} (xs ys : List A)
    → reverse (xs ++ ys) ≡ reverse ys ++ reverse xs
  reverse-++-distrib [] ys = sym (++-identityʳ (reverse ys)) 
  reverse-++-distrib (x :: xs) ys = 
    begin 
      reverse (xs ++ ys) ++ x :: [] 
    ≡⟨ cong (_++ (x :: [])) (reverse-++-distrib xs ys) ⟩
      (reverse ys ++ reverse xs) ++ x :: []
    ≡⟨ ++-assoc  (reverse ys) (reverse xs) (x :: []) ⟩ 
      reverse ys ++ reverse (x :: xs)
    ∎

  reverse-1 : {A : Set} (x : A)
    → reverse (x :: []) ≡ (x :: [])
  reverse-1 x with reverse (x :: [])
  ... | x::[] = refl

  reverse-involute : {A : Set} (xs : List A) 
    → reverse (reverse xs) ≡ xs
  reverse-involute [] = refl
  reverse-involute (x :: xs) = 
    begin
      reverse (reverse xs ++ x :: [])
    ≡⟨ reverse-++-distrib (reverse xs) (x :: []) ⟩
      (x :: []) ++ (reverse (reverse xs))
    ≡⟨ cong ((x :: []) ++_) (reverse-involute (xs)) ⟩ 
      x :: xs
    ∎

  shunt : ∀ {A : Set} → List A → List A → List A
  shunt [] ys = ys
  shunt (x :: xs) ys = shunt xs (x :: ys)

  shunt-reverse : ∀ {A : Set} (xs ys : List A)
    → shunt xs ys ≡ reverse xs ++ ys
  shunt-reverse [] ys = refl
  shunt-reverse (x :: xs) ys = begin
      shunt (x :: xs) ys
    ≡⟨⟩
      shunt xs (x :: ys)
    ≡⟨ shunt-reverse xs (x :: ys) ⟩
      reverse xs ++ (x :: ys)
    ≡⟨⟩
      reverse xs ++ ((x :: []) ++ ys)
    ≡⟨ sym (++-assoc (reverse xs) (x :: []) ys) ⟩
      ((reverse xs) ++ (x :: [])) ++ ys
    ≡⟨⟩
      (reverse (x :: xs)) ++ ys 
    ∎

  reverse` : ∀ {A : Set} → List A → List A
  reverse` xs = shunt xs []

  reverses : ∀ {A : Set} (xs : List A)
    → reverse` xs ≡ reverse xs
  reverses xs =
    begin
      reverse` xs
    ≡⟨⟩
      shunt xs []
    ≡⟨ shunt-reverse xs [] ⟩
      reverse xs ++ []
    ≡⟨ ++-identityʳ (reverse xs) ⟩
      reverse xs
    ∎

  map : ∀ {A B : Set} → (f : A → B) → List A → List B
  map f [] = []
  map f (x :: xs) = (f x) :: (map f xs)

  ::-≡ : {A : Set} {xs ys : List A} (a : A)
    → xs ≡ ys
    → (a :: xs) ≡ (a :: ys)
  ::-≡ a refl = refl

  map-compose-helper : {A B C : Set}
    → (f : A → B)
    → (g : B → C) 
    → (xs : List A)
    → map (g ∘ f) xs ≡ ((map g) ∘ (map f)) xs
  map-compose-helper f g [] = refl
  map-compose-helper f g (x :: xs) =  begin
                                        (g ∘ f) x :: map (g ∘ f) xs
                                      ≡⟨ 
                                        (let
                                          ind = map-compose-helper f g xs
                                        in
                                          ::-≡ ((g ∘ f) x) ind)
                                      ⟩
                                        (g ∘ f) x :: (((map g) ∘ (map f)) xs)
                                      ≡⟨⟩ 
                                        (map (g ∘ f)) (x :: []) ++ (((map g) ∘ (map f)) xs)
                                      ≡⟨⟩
                                        ((map g) ∘ (map f)) (x :: []) ++ (((map g) ∘ (map f)) xs)
                                      ≡⟨⟩
                                        ((map g) ∘ (map f)) (x :: xs) 
                                      ∎

  map-compose : {A B C : Set} 
    → (f : A → B)
    → (g : B → C) 
    → map (g ∘ f) ≡ (map g) ∘ (map f)
  map-compose f g = extensionality (λ xs → map-compose-helper f g xs)

  data Tree (A B : Set) : Set where
    leaf : A → Tree A B
    node : Tree A B → B → Tree A B → Tree A B

  map-Tree : ∀ {A B C D : Set} 
    → (A → C) → (B → D) 
    → Tree A B
    → Tree C D
  map-Tree f _ (leaf a) = leaf (f a)
  map-Tree f g (node left b right) = let
      b = g b
      left` = map-Tree f g left
      right` = map-Tree f g right
    in
      node left` b right`

  foldr : ∀ {A B : Set} 
    → (A → B → B) 
    → B 
    → List A 
    → B
  foldr _ acc [] = acc
  foldr _op_ acc (x :: xs) = 
    x op (foldr _op_ acc xs)

  sum : List ℕ → ℕ
  sum = foldr _+_ 0

  product : List ℕ → ℕ
  product = foldr _*_ 1

  foldr-++ : {A : Set} 
    → (b : A) 
    → (op : A → A → A)
    → (xs ys : List A)
    → foldr op b (xs ++ ys) ≡ foldr op (foldr op b ys) xs
  foldr-++ b _op_ xs [] rewrite (++-identityʳ xs) = refl
  foldr-++ b _op_ [] ys = refl
  foldr-++ b _op_ (x :: xs) ys = 
    let
      ind = foldr-++ b _op_ xs ys
    in
      cong (x op_) ind

  foldr-:: : {A : Set}
    → (xs : List A)
    → foldr _::_ [] xs ≡ xs
  foldr-:: [] = refl 
  foldr-:: (x :: xs) = cong (x ::_) (foldr-:: xs)

  map-is-foldr : {A B : Set}
    → (f : A → B)
    → map f ≡ foldr (λ x xs → f x :: xs) []
  map-is-foldr f = 
    extensionality (λ xs → map-is-foldr-helper f xs)
    where
      map-is-foldr-helper : {A B : Set}
        → (f : A → B)
        → (xs : List A)
        → map f xs ≡ foldr (λ x xs → f x :: xs) [] xs
      map-is-foldr-helper f [] = refl
      map-is-foldr-helper f (x :: xs) = 
        let
          ind = map-is-foldr-helper f xs
        in
          cong ((f x) ::_) ind

  fold-Tree : ∀ {A B C : Set}
    → (A → C)
    → (C → B → C → C)
    → Tree A B
    → C
  fold-Tree f _ (leaf a) = f a
  fold-Tree f g (node left b right) = 
    let
      left` = fold-Tree f g left
      right` = fold-Tree f g right
    in
      g left` b right`

  map-is-fold-Tree : {A B C : Set}
    → (f : A → C)
    → (g : B → C)
    → map-Tree f g ≡ fold-Tree (λ a → leaf (f a)) λ left b right → node left (g b) right
  map-is-fold-Tree f g = 
    extensionality (λ tree → map-is-fold-Tree-helper f g tree)
    where
      map-is-fold-Tree-helper : {A B C : Set}
        → (f : A → C)
        → (g : B → C)
        → (tree : Tree A B)
        → map-Tree f g tree ≡ fold-Tree (λ a → leaf (f a)) (λ left b right → node left (g b) right) tree
      map-is-fold-Tree-helper f g (leaf a) = refl
      map-is-fold-Tree-helper f g (node left b right) 
        rewrite (map-is-fold-Tree-helper f g left) 
              | (map-is-fold-Tree-helper f g right) =
        refl

  downFrom : ℕ → List ℕ
  downFrom zero = []
  downFrom (suc n) = n :: downFrom n

  n≤n² : (n : ℕ) → (n * 1) ≤ (n * n)
  n≤n² zero = z≤n
  n≤n² (suc n) = s≤s {! n≤n² n  !}

  sum-downFrom : (n : ℕ) 
    → sum (downFrom n) * 2 ≡ n * (n ∸ 1)
  sum-downFrom zero = refl
  sum-downFrom (suc n) = 
    begin 
      sum (n :: downFrom n) * 2 
    ≡⟨⟩ 
      (n + (sum (downFrom n))) * 2 
    ≡⟨ *-distribʳ-+ 2 n (sum (downFrom n)) ⟩ 
      (n * 2) + ((sum (downFrom n)) * 2) 
    ≡⟨ cong ((n * 2) +_) (sum-downFrom n) ⟩ 
      (n * 2) + n * (n ∸ 1) 
    ≡⟨ cong ((n * 2) +_) (*-distribˡ-∸ n n 1) ⟩ 
      (n * 2) + ((n * n) ∸ (n * 1)) 
    ≡⟨ sym (+-∸-assoc (n * 2) (n≤n² n) ) ⟩ 
      ((n * 2) + (n * n)) ∸ (n * 1) 
    ≡⟨ cong (_∸ (n * 1)) (+-comm (n * 2) (n * n)) ⟩ 
      ((n * n) + (n * 2)) ∸ (n * 1) 
    ≡⟨ +-∸-assoc (n * n) (*-monoʳ-≤ n (s≤s z≤n)) ⟩ 
      (n * n) + ((n * 2) ∸ (n * 1)) 
    ≡⟨ cong (λ x → (n * n) + (x ∸ (n * 1))) (*-comm n 2) ⟩ 
      (n * n) + ((2 * n) ∸ (n * 1))
    ≡⟨⟩ 
      (n * n) + ((n + (1 * n)) ∸ (n * 1))
    ≡⟨⟩ 
      (n * n) + ((n + (n + (0 * n))) ∸ (n * 1)) 
    ≡⟨⟩ 
      (n * n) + ((n + (n + 0)) ∸ (n * 1)) 
    ≡⟨ cong (λ x → (n * n) + ((n + x) ∸ (n * 1))) (+-comm n 0) ⟩ 
      (n * n) + ((n + n) ∸ (n * 1)) 
    ≡⟨ cong (λ x → (n * n) + ((n + n) ∸ x)) (*-comm n 1) ⟩ 
      (n * n) + ((n + n) ∸ (1 * n)) 
    ≡⟨⟩ 
      (n * n) + ((n + n) ∸ (n + (0 * n))) 
    ≡⟨⟩ 
      (n * n) + ((n + n) ∸ (n + 0)) 
    ≡⟨ cong (λ x →  (n * n) + ((n + n) ∸ x)) (+-comm n 0) ⟩ 
      (n * n) + ((n + n) ∸ n) 
    ≡⟨ cong ((n * n) +_) (+-∸-comm n (≤-refl {n})) ⟩ 
      (n * n) + ((n ∸ n) + n) 
    ≡⟨ cong (λ x → (n * n) + (x + n)) (n∸n≡0 n) ⟩ 
      (n * n) + n 
    ≡⟨ +-comm (n * n) n ⟩ 
      n + (n * n) 
    ∎

  record IsMonoid {A : Set} (_op_ : A → A → A) (id : A) : Set where
    field
      assoc : ∀ (x y z : A) → (x op y) op z ≡ x op (y op z)
      identityˡ : ∀ (x : A) → (id op x ≡ x)
      identityʳ : ∀ (x : A) → (x op id ≡ x)

  open IsMonoid

  +-monoid : IsMonoid _+_ 0
  +-monoid = 
    record { 
      assoc = +-assoc ; 
      identityˡ = +-identityˡ ; 
      identityʳ = +-identityʳ 
    }

  foldl : ∀ {A B : Set} 
    → (B → A → B) 
    → B 
    → List A 
    → B
  foldl _ b [] = b
  foldl _op_ b (a :: as) = 
    foldl _op_ (b op a) as
    
  foldl-++ : {A : Set}
    → (op : A → A → A)
    → (a : A)
    → (xs ys : List A)
    → foldl op a (xs ++ ys) ≡ foldl op (foldl op a xs) ys
  foldl-++ _op_ a xs [] rewrite (++-identityʳ xs) = refl
  foldl-++ _op_ a [] ys = refl
  foldl-++ _op_ a (x :: xs) ys =
    foldl-++ _op_ (a op x) xs ys

  foldr-monoid : ∀ {A : Set} (_⊗_ : A → A → A) (e : A) → IsMonoid _⊗_ e →
    ∀ (xs : List A) (y : A) → foldr _⊗_ y xs ≡ foldr _⊗_ e xs ⊗ y
  foldr-monoid _⊗_ e ⊗-monoid [] y =
    begin
      foldr _⊗_ y []
    ≡⟨⟩
      y
    ≡⟨ sym (identityˡ ⊗-monoid y) ⟩
      (e ⊗ y)
    ≡⟨⟩
      foldr _⊗_ e [] ⊗ y
    ∎
  foldr-monoid _⊗_ e ⊗-monoid (x :: xs) y =
    begin
      foldr _⊗_ y (x :: xs)
    ≡⟨⟩
      x ⊗ (foldr _⊗_ y xs)
    ≡⟨ cong (x ⊗_) (foldr-monoid _⊗_ e ⊗-monoid xs y) ⟩
      x ⊗ (foldr _⊗_ e xs ⊗ y)
    ≡⟨ sym (assoc ⊗-monoid x (foldr _⊗_ e xs) y) ⟩
      (x ⊗ foldr _⊗_ e xs) ⊗ y
    ≡⟨⟩
      foldr _⊗_ e (x :: xs) ⊗ y
    ∎

  foldr-monoid-++ : ∀ {A : Set} (_⊗_ : A → A → A) (e : A) → IsMonoid _⊗_ e →
    ∀ (xs ys : List A) 
    → foldr _⊗_ e (xs ++ ys) ≡ foldr _⊗_ e xs ⊗ foldr _⊗_ e ys
  foldr-monoid-++ _⊗_ e monoid-⊗ xs ys =
    begin
      foldr _⊗_ e (xs ++ ys)
    ≡⟨ foldr-++ e _⊗_ xs ys ⟩
      foldr _⊗_ (foldr _⊗_ e ys) xs
    ≡⟨ foldr-monoid _⊗_ e monoid-⊗ xs (foldr _⊗_ e ys) ⟩
      foldr _⊗_ e xs ⊗ foldr _⊗_ e ys
    ∎

  foldl-monoid : ∀ {A : Set} (_⊗_ : A → A → A) (e : A) → IsMonoid _⊗_ e →
    ∀ (xs : List A) (y : A) 
    → foldl _⊗_ y xs ≡ y ⊗ foldl _⊗_ e xs
  foldl-monoid _ _ monoid [] y = sym (identityʳ monoid y)
  foldl-monoid _op_ e monoid (x :: xs) y = 
    begin 
      foldl _op_ (y op x) xs 
    ≡⟨ foldl-monoid _op_ e monoid xs (y op x) ⟩ 
      ((y op x) op (foldl _op_ e xs)) 
    ≡⟨ (assoc monoid) y x (foldl _op_ e xs) ⟩ 
      (y op (x op (foldl _op_ e xs))) 
    ≡⟨ cong (y op_) (sym (foldl-monoid _op_ e monoid xs x)) ⟩ 
      (y op (foldl _op_ x xs)) 
    ≡⟨ cong (λ xx → y op (foldl _op_ xx xs)) (sym ((identityˡ monoid) x)) ⟩ 
      (y op (foldl _op_ (e op x) xs)) 
    ∎

  foldl-monoid-++ : ∀ {A : Set} (_⊗_ : A → A → A) (e : A) → IsMonoid _⊗_ e →
    ∀ (xs ys : List A) 
    → foldl _⊗_ e (xs ++ ys) ≡ foldl _⊗_ e xs ⊗ foldl _⊗_ e ys
  foldl-monoid-++ _op_ e monoid xs ys = 
    begin
      foldl _op_ e (xs ++ ys)
    ≡⟨ foldl-++ _op_ e xs ys ⟩
      foldl _op_ (foldl _op_ e xs) ys
    ≡⟨ foldl-monoid _op_ e monoid ys (foldl _op_ e xs) ⟩
      ((foldl _op_ e xs) op (foldl _op_ e ys)) 
    ∎
  
  foldr-monoid-foldl : {A : Set}
    → (_op_ : A → A → A)
    → (e : A)
    → IsMonoid _op_ e
    → foldr _op_ e ≡ foldl _op_ e
  foldr-monoid-foldl {A} _op_ e monoid = 
    extensionality (λ as → foldr-monoid-foldl-helper as)
    where 
      foldr-monoid-foldl-helper : (as : List A)
        → foldr _op_ e as ≡ foldl _op_ e as
      foldr-monoid-foldl-helper [] = refl
      foldr-monoid-foldl-helper (a :: as) = 
        let 
          foldr-monoid-foldl-as = foldr-monoid-foldl-helper as 
        in 
          begin 
            foldr _op_ e (a :: as) 
          ≡⟨⟩ 
            foldr _op_ e ((a :: []) ++ as)
          ≡⟨ foldr-monoid-++  _op_ e monoid (a :: []) as ⟩ 
            ((foldr _op_ e (a :: [])) op (foldr _op_ e as))
          ≡⟨ cong ((foldr _op_ e (a :: [])) op_) foldr-monoid-foldl-as ⟩ 
            ((foldr _op_ e (a :: [])) op (foldl _op_ e as)) 
          ≡⟨⟩ 
            ((a op (foldr _op_ e ([]))) op  (foldl _op_ e as)) 
          ≡⟨⟩ 
            ((a op e) op (foldl _op_ e as)) 
          ≡⟨ cong (_op  (foldl _op_ e as)) (identityʳ monoid a) ⟩ 
            (a op  (foldl _op_ e as)) 
          ≡⟨ cong (_op  (foldl _op_ e as)) (sym (identityˡ monoid a)) ⟩ 
            (((e op a) op (foldl _op_ e as))) 
          ≡⟨⟩ 
            (((((foldl _op_ e []) op a) op (foldl _op_ e as)))) 
          ≡⟨⟩ 
            (((((foldl _op_ e (a :: [])) op (foldl _op_ e as))))) 
          ≡⟨ sym (foldl-monoid-++ _op_ e monoid (a :: []) as) ⟩ 
            foldl _op_ e ((a :: []) ++ as) 
          ≡⟨⟩ 
            foldl _op_ e (a :: ([] ++ as)) 
          ≡⟨⟩ 
            foldl _op_ e (a :: as) 
          ∎
 
  data All {A : Set} (P : A → Set) : List A → Set where
    [] : All P []
    _::_ : ∀ {x : A} {xs : List A} → P x → All P xs → All P (x :: xs)
  
  data Any {A : Set} (P : A → Set) : List A → Set where
    here : ∀ {x : A} {xs : List A} → P x → Any P (x :: xs)
    there : ∀ {x : A} {xs : List A} → Any P xs → Any P (x :: xs)

  infix 4 _∈_ _∉_

  _∈_ : ∀ {A : Set} (a : A) (as : List A) → Set
  a ∈ as = Any (a ≡_) as

  _∉_ : ∀ {A : Set} (a : A) (as : List A) → Set
  a ∉ as = ¬ (a ∈ as)
  
  not-in : 3 ∉ (2 :: 1 :: [])
  not-in (here ())
  not-in (there (here ()))
  not-in (there (there ()))
  
  All-++-⇔ : {A : Set} {P : A → Set} (xs ys : List A)
    → All P (xs ++ ys) ⇔ (All P xs × All P ys)
  All-++-⇔ xs ys = 
    record { 
      to = to xs ys; 
      from = from xs ys 
    }
    where
      to : ∀ {A : Set} {P : A → Set} (xs ys : List A)
        → All P (xs ++ ys) 
        → (All P xs × All P ys)
      to [] ys Pys = ⟨ [] , Pys ⟩
      to (x :: xs) ys (Px :: Pxs++ys) =
        let ⟨ Pxs , Pys ⟩ = (to xs ys Pxs++ys)
        in 
          ⟨ Px :: Pxs , Pys ⟩
          
      from : ∀ {A : Set} {P : A → Set} (xs ys : List A)
        → (All P xs × All P ys)
        → All P (xs ++ ys) 
      from [] ys ⟨ [] , Pys ⟩ = Pys 
      from (x :: xs) ys ⟨ Px :: Pxs , Pys ⟩ =
        let Pxs++ys = (from xs ys ⟨ Pxs , Pys ⟩)
        in 
          Px :: Pxs++ys

  Any-++-⇔ : {A : Set} {P : A → Set} (xs ys : List A)
    → Any P (xs ++ ys) ⇔ ((Any P xs) ⊎ (Any P ys))
  Any-++-⇔ xs ys = 
    record { 
      to = to xs ys ; 
      from = from xs ys 
    }
    where
      to : ∀ {A : Set} {P : A → Set} (xs ys : List A)
        → Any P (xs ++ ys) 
        → ((Any P xs) ⊎ (Any P ys))
      to [] ys AnyPys = inj₂ AnyPys
      to (x :: xs) ys (here AnyPx) = inj₁ (here AnyPx)
      to (x :: xs) ys (there AnyPxs++ys) with (to xs ys AnyPxs++ys)
      ... | inj₁ AnyPxs = inj₁ (there AnyPxs)
      ... | inj₂ AnyPys = inj₂ AnyPys

      from : ∀ {A : Set} {P : A → Set} (xs ys : List A)
        → ((Any P xs) ⊎ (Any P ys))
        → Any P (xs ++ ys) 
      from (x :: xs) ys (inj₁ (here Px)) = here Px
      from (x :: xs) ys (inj₁ (there AnyPxs)) =
        let AnyPxs++ys = (from xs ys (inj₁ AnyPxs))
        in there AnyPxs++ys
      from [] ys (inj₂ AnyPys) = AnyPys
      from (x :: xs) ys (inj₂ AnyPys) = 
        let AnyPxs++ys = (from xs ys (inj₂ AnyPys))
        in (there AnyPxs++ys)

  ¬Any⇔All¬ : {A : Set} {P : A → Set} (xs : List A)
    → (¬_ ∘ Any P) xs ⇔ All (¬_ ∘ P) xs
  ¬Any⇔All¬ xs = 
    record { 
      to = to xs ; 
      from = from xs 
    }
    where
      to : {A : Set} {P : A → Set} (xs : List A)
        → (¬_ ∘ Any P) xs
        →  All (¬_ ∘ P) xs
      to [] _ = []
      to (x :: xs) ¬AnyPx::xs = (λ Px → ¬AnyPx::xs (here Px)) :: to xs (λ AnyPxs → ¬AnyPx::xs (there AnyPxs))

      from : {A : Set} {P : A → Set} (xs : List A)
        → All (¬_ ∘ P) xs
        → (¬_ ∘ Any P) xs 
      from [] [] ()
      from (x :: xs) (¬Px :: _) (here Px) = ¬Px Px
      from (x :: xs) (_ :: All¬Pxs) (there AnyPxs) = 
        let ¬AnyPxs = from xs All¬Pxs
        in ¬AnyPxs AnyPxs

  all : ∀ {A : Set} → (A → Bool) → List A → Bool
  all p = foldr (λ x → (p x) ∧_) true
