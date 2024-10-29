module nats where

    data Bool : Set where
        tt : Bool
        ff : Bool

    data Nat : Set where
        O : Nat
        S : Nat → Nat
        
    not : Bool → Bool
    not tt = ff
    not ff = tt

    _&&_ : Bool → Bool → Bool
    tt && x₁ = x₁
    ff && x₁ = ff

    _||_ : Bool → Bool → Bool
    tt || y = tt
    ff || y = y

    if_then_else_ : ∀  {A : Set} → Bool → A → A → A
    if_then_else_ tt x y = x
    if_then_else_ ff x y = y

    xor : Bool → Bool → Bool
    xor tt y = not y
    xor ff y = y

    _＋_ : Nat → Nat → Nat
    O ＋ y = y
    S x ＋ y = S (x ＋ y)

    data _≡_ {A : Set} : A → A → Set where
        refl : {x : A} → x ≡ x

    {-# BUILTIN EQUALITY _≡_ #-}

    bool-refl : ∀ (b : Bool) → b ≡ b
    bool-refl b = refl

    double-negation : ∀ (b : Bool) → not (not b) ≡ b
    double-negation tt = refl 
    double-negation ff = refl

    bAndb : ∀ (b : Bool) → (b && b) ≡ b
    bAndb tt = refl
    bAndb ff = refl

    bOrb : ∀ (b : Bool) → (b || b) ≡ b
    bOrb tt = refl
    bOrb ff = refl

    ||≡ff₁ : ∀ {b1 b2} → (b1 || b2) ≡ ff → b1 ≡ ff
    ||≡ff₁ {ff} p = refl
    ||≡ff₁ {tt} p  = p  

    orConm : ∀ {b1 b2} → (b1 || b2) ≡ (b2 || b1)
    orConm {tt} {tt} = refl
    orConm {tt} {ff} = refl  
    orConm {ff} {tt} = refl 
    orConm {ff} {ff} = refl
    
    orCongr : ∀ { b1 b1' b2} → b1 ≡ b1' → (b1 || b2) ≡ (b1' || b2)
    orCongr refl = refl  

    -- nat
    zero+ : ∀ (n : Nat) → (O ＋ n) ≡ n
    zero+ n = refl
    
    asocSuma : ∀ (a b c : Nat) → ((a ＋ b) ＋ c) ≡ (a ＋ (b ＋ c))
    asocSuma O b c = refl
    asocSuma (S a') b c rewrite asocSuma a' b c = refl  -- paso inductivo: a = S a'

    +0 : ∀ (n : Nat) → (n ＋ O) ≡ n
    +0 O = refl 
    +0 (S x) rewrite +0 x = refl

    +suc : ∀ (a b : Nat) → (a ＋ S b) ≡ S (a ＋ b)
    +suc O b = refl
    +suc (S a) b rewrite +suc a b = refl

    lema1 : ∀ (a b : Nat) → (a ＋ S b) ≡ S (a ＋ b)
    lema1 O b = refl
    lema1 (S a) b  rewrite lema1 a b = refl

    +conm : ∀ (a b : Nat) → (a ＋ b) ≡ (b ＋ a)
    +conm O y  rewrite +0 y = refl
    +conm (S x) y rewrite +suc y x |  +conm x y = refl

    sym : ∀ {A : Set} {a b : A } → a ≡ b → b ≡ a
    sym refl = refl

    +conm2 : ∀ (a b : Nat) → (a ＋ b) ≡ (b ＋ a)
    +conm2 O b rewrite +0 b = refl
    +conm2 (S a) b  rewrite lema1 b a |  +conm a b  = refl

    cong : ∀ {A B : Set} {x y : A} → (f : A → B) → x ≡ y → f x ≡ f y
    cong f refl = refl 


    _*_ : Nat → Nat → Nat
    O * y = O
    S x * y = y ＋ (x * y)

    _<_ : Nat → Nat → Bool
    O < O = ff
    O < (S y) = tt
    (S x) < O = ff
    (S x) < (S y) = x < y

    _>_ : Nat → Nat → Bool
    O > y = ff
    S x > O = tt
    S x > S y = x > y

    _≤_ : Nat → Nat → Bool
    O ≤ y = tt
    S x ≤ O = ff
    S x ≤ S y = x ≤ y

    O<n : ∀ (n : Nat) → (O < S n) ≡ tt
    O<n n = refl
