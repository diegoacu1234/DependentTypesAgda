module dependentLists where
    data Nat : Set where
        O : Nat
        S : Nat -> Nat

    _+_ : Nat -> Nat -> Nat
    O + n = n
    (S m) + n = S (m + n)

    data _≡_ {A : Set} : A -> A -> Set where
        refl : {x : A} -> x ≡ x

    data Vec (A : Set) : (n : Nat) -> Set where -- depends on the length of the list/vector
        [] : Vec A O
        _::_ : {n : Nat} -> A -> Vec A n -> Vec A (S n)

    -- ejemplos:
    l0 : Vec Nat O
    l0 = []
    
    l1 : Vec Nat (S O)
    l1 = O :: []

    l2 : Vec Nat (S (S O))
    l2 = S O :: (O :: [])

    {-# BUILTIN EQUALITY _≡_ #-}

    cong : ∀ {A B : Set} {x y : A} → x ≡ y → (f : A → B) → f x ≡ f y
    cong refl f = refl

    -- concatenation of vectors
    _++_ : {A : Set} -> {n m : Nat} -> Vec A n -> Vec A m -> Vec A (n + m)
    [] ++ l2 = l2
    (x :: l3) ++ l2 = x :: (l3 ++ l2 )

    length : {A : Set} -> {n : Nat} -> Vec A n -> Nat
    length [] = O
    length (x :: x₁) = S (length x₁)  
    
    lengthProof : {A : Set} -> {n : Nat} -> (l : Vec A n) -> (length l) ≡ n
    lengthProof {A} {.O} ([]) = refl
    lengthProof {A} {.(S _)} (x :: l) = let hi = lengthProof l in cong hi S 

    length' : {A : Set} -> {n : Nat} -> Vec A n -> Nat
    length' {A} {n} l = n

    lengthEq : {A : Set} -> {n : Nat} -> (l : Vec A n) -> (length' l) ≡ n
    lengthEq {A} {n} l = refl

    