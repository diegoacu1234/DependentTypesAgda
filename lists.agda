module lists where
    data Nat : Set where
        O : Nat
        S : Nat -> Nat

    data _≡_ {A : Set} : A -> A -> Set where
        refl : {x : A} -> x ≡ x
    infix 10 _≡_

    cong : ∀ {A B : Set} {x y : A} → x ≡ y → (f : A → B) → f x ≡ f y
    cong refl f = refl

    sym : {A : Set} -> {x y : A} -> x ≡ y -> y ≡ x
    sym refl = refl
    
    _+_ : Nat -> Nat -> Nat
    O + n = n
    (S m) + n = S (m + n)
    
    x+0 : ∀ (x : Nat) -> x + O ≡ x
    x+0 O = refl
    x+0 (S x) = let hi = x+0 x
                in cong hi S

    {-# BUILTIN EQUALITY _≡_ #-}


    x+Sy : ∀ (x y : Nat) -> x + (S y) ≡ S (x + y)
    x+Sy O y = refl
    x+Sy (S x) y = let hi = x+Sy x y
                    in cong hi S

    Sx+y : ∀ (x y : Nat) -> S (x + y) ≡ x + S y
    Sx+y O y = refl
    Sx+y (S x) y rewrite x+Sy x y = refl 


    +comm : ∀ (x y : Nat) -> x + y ≡ y + x
    +comm O y rewrite x+0 y = refl
    +comm (S x) y rewrite  +comm x y | Sx+y y x  = refl

    +assoc : ∀ (x y z : Nat) -> x + (y + z) ≡ (x + y) + z
    +assoc O y z = refl 
    +assoc (S x) y z rewrite +assoc x y z = refl

    data List (A : Set) : Set where
        [] : List A
        _::_ : A -> List A -> List A

    _++_ : {A : Set} -> List A -> List A -> List A
    [] ++ l2 = l2
    (x :: l1) ++ l2 = x :: (l1 ++ l2)

    []++l : {A : Set} -> ∀ (l : List A) -> ([] ++ l) ≡ l
    []++l l = refl
    
    l++[] : {A : Set} -> ∀ (l : List A) -> (l ++ []) ≡ l
    l++[] [] = refl 
    l++[] (x :: l) rewrite l++[] l = refl

    reverse : {A : Set} -> List A -> List A
    reverse [] = []
    reverse (x :: l) = (reverse l) ++ (x :: [])

    lemaRev : {A : Set } -> ∀ (l : List A) ->  ∀ (x : A) ->  ((reverse l) ++ (x :: [])) ≡ reverse (x :: l )
    lemaRev {A} [] c = refl
    lemaRev {A} (x :: xs) c rewrite lemaRev xs c = refl
    
    rev1Elem : {A : Set} -> ∀ (x : A) -> reverse (x :: []) ≡ x :: []
    rev1Elem x = refl

    length : {A : Set} -> (l : List A) -> Nat
    length [] = O
    length (x :: l) = S (length l) 

    assoc++ : {A : Set} -> ∀ (l1 l2 l3 : List A ) -> l1 ++ (l2 ++ l3) ≡ (l1 ++ l2) ++ l3
    assoc++ [] l2 l3 = refl
    assoc++ (x :: l1) l2 l3 rewrite assoc++ l1 l2 l3 = refl

    rev++ : {A : Set} -> ∀ (l1 l2 : List A) -> reverse (l1 ++ l2) ≡ (reverse l2) ++ (reverse l1)
    rev++ [] l2 rewrite l++[] (reverse l2) = refl
    rev++ (x :: l1) l2 rewrite rev++ l1 l2 | assoc++ (reverse l2) (reverse l1) (x :: [] ) = refl


    rev-rev : {A : Set} -> ∀ (l : List A) -> reverse (reverse l) ≡ l
    rev-rev [] = refl    
    rev-rev (x :: l) rewrite rev-rev l | rev++ (reverse l) (x :: []) | rev-rev l   = refl

    data Bool : Set
        where False : Bool
              True : Bool

    if_then_else_ : ∀  {A : Set} → Bool → A → A → A
    if_then_else_ True x y = x
    if_then_else_ False x y = y

    

    filter : {A : Set } -> (p : A -> Bool ) -> ( l : List A) -> List A
    filter p [] = []
    filter p (x :: xs)  with p x
    ... | True = x :: (filter p xs)
    ... | False = filter p xs

    filter-filter : {A : Set} -> ∀ (p : A -> Bool ) ->  ∀ ( l : List A) -> filter p (filter p l) ≡ filter p l
    filter-filter p [] = refl
    filter-filter p (x :: l) with p x in eq 
    ... | False = filter-filter p l
    ... | True rewrite eq | filter-filter p l = refl

    case_of_ : ∀ {a b} {A : Set a} {B : Set b} → A → (A → B) → B
    case x of f = f x 

    filter' : {A : Set} -> (A -> Bool) -> List A -> List A
    filter' p [] = []
    filter' p (x :: l) = 
        case p x of 
        λ {
            True -> x :: (filter' p l);
            False -> filter' p l
        }

    filter'-filter' : {A : Set} -> ∀ (p : A -> Bool ) ->  ∀ ( l : List A) -> filter' p (filter' p l) ≡ filter' p l
    filter'-filter' p [] = refl
    filter'-filter' p (x :: l) with p x in eq 
    ... | True rewrite eq | filter'-filter' p l = refl
    ... | False rewrite eq | filter'-filter' p l = refl 

    _≤_ : Nat -> Nat -> Bool
    O ≤ y = True
    S x ≤ O = False
    S x ≤ S y = x ≤ y 

    map :  {A : Set} {B : Set} → (A → B) → List A → List B
    map f [] = []
    map f (x :: xs) = f x :: map f xs
    
    length-map : {A : Set} {B : Set} -> ∀ (f : A -> B) -> ∀ (l : List A) -> length (map f l) ≡ length l
    length-map f [] = refl 
    length-map f (x :: l) rewrite length-map f l  = refl  