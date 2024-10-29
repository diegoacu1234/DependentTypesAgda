module bools where 
    data Bool : Set where
        tt : Bool
        ff : Bool

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

    data _≡_ {A : Set} : A → A → Set where
        refl : {x : A} → x ≡ x

    -- para que funcione el rewrite
    {-# BUILTIN EQUALITY _≡_ #-}

    -- Pruebas y propiedades
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
