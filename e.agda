module e where

  -- Natural numbers
  data Nat : Set where
    zero : Nat
    suc  : Nat → Nat

  data Bool : Set where
    true  : Bool
    false : Bool


  _&&_ : Bool -> Bool -> Bool
  true && y = y
  false && y = false

   
  -- Addition
  _+_ : Nat → Nat → Nat
  zero + n = n
  suc m + n = suc (m + n)

  -- Subtraction
  _-_ : Nat → Nat → Nat
  n     - zero  = n
  zero  - suc m = zero
  suc n - suc m = n - m
  

  -- Multiplication
  _*_ : Nat → Nat → Nat
  zero  * m = zero
  suc n * m = (n * m) + m
  

  -- Equality comparison
  _==_ : Nat → Nat → Bool
  zero  == zero  = true
  suc n == suc m = n == m
  _     == _     = false
  

  -- Less-than comparison
  _<_ : Nat → Nat → Bool
  _     < zero  = false
  zero  < suc _ = true
  suc n < suc m = n < m
  
  _<=_ : Nat → Nat → Bool
  zero <= _     = true
  suc n <= suc m = n <= m
  suc _ <= zero = false

  -- Division helper function
  div-helper : Nat → Nat → Nat → Nat → Nat
  div-helper k m  zero    j      = k
  div-helper k m (suc n)  zero   = div-helper (suc k) m n m
  div-helper k m (suc n) (suc j) = div-helper k m n j
  

  -- Modulo helper function
  mod-helper : Nat → Nat → Nat → Nat → Nat
  mod-helper k m  zero    j      = k
  mod-helper k m (suc n)  zero   = mod-helper zero m n m
  mod-helper k m (suc n) (suc j) = mod-helper (suc k) m n j

  -- Infix operators for multiplication and addition
  infixl 30 _*_
  infixl 20 _+_

  -- Division
  div : Nat → Nat → Nat
  div n (suc m) = div-helper zero m n m
  div n zero    = zero

  -- Modulo
  mod : Nat → Nat → Nat
  mod n (suc m) = mod-helper zero m n m
  mod n zero    = zero

  uno : Nat
  uno = suc zero

  dos : Nat
  dos = suc uno

  tres : Nat
  tres = suc dos

  cuatro : Nat
  cuatro = suc tres

  ocho : Nat
  ocho = suc (suc (suc (suc (suc (suc (suc (suc zero)))))))

  diez : Nat
  diez = suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))

  if_then_else_ : {A : Set} → Bool → A → A → A
  if true  then x else y = x  
  if false then x else y = y
  
  data List (A : Set) : Set where
    []   : List A
    _∷_  : A → List A → List A

  infixr 5 _∷_

  -- List concatenation
  _++_ : {a : Set} -> List a → List a → List a
  [] ++ ys = ys
  (x ∷ xs) ++ ys = x ∷ (xs ++ ys)

  length : {a : Set} -> List a → Nat
  length [] = zero
  length (x ∷ xs) = suc (length xs)


  -- Interval function (from and to)
  interval : Nat → Nat → List Nat
  interval zero zero = zero ∷ []
  interval (suc n) zero = []
  interval n (suc m) with n == suc m
  ... | true = n ∷ []
  ... | false =  (interval n m) ++ (suc m ∷ [])


  -- Helper function to calculate divisors
  divisors' : Nat → Nat → List Nat
  divisors' n zero = []
  divisors' n (suc d) with mod n (suc d) == zero
  ... | true = suc d ∷ divisors' n d
  ... | false = divisors' n d 
    
 -- Divisor function
  divisors : Nat → List Nat 
  divisors n = divisors' n n

  isPrime : Nat → Bool
  isPrime n = length (divisors n) == dos

  filter : {a : Set} → (a → Bool) → List a → List a
  filter p [] = []
  filter p (x ∷ xs) with p x
  ... | true = x ∷ filter p xs
  ... | false = filter p xs

  primeFactors : Nat → List Nat
  primeFactors n = filter isPrime (divisors n)

  repeat : {a : Set} → a → Nat → List a
  repeat x zero = []
  repeat x (suc n) = x ∷ repeat x n

  map : {a b : Set} → (a → b) → List a → List b
  map f [] = []
  map f (x ∷ xs) = f x ∷ map f xs

  foldl : {a b : Set} → (a → b → b) → b → List a → b
  foldl f b [] = b
  foldl f b (x ∷ xs) = foldl f (f x b) xs

  primeHelper : Nat -> List Nat -> List Nat
  primeHelper n [] = []
  primeHelper n (x ∷ xs) = (repeat x n) ++ primeHelper n xs

  allPosiblePrimeFactors : Nat → (List Nat)
  allPosiblePrimeFactors n = primeHelper n (primeFactors n)

  
  decompose' : Nat -> List Nat -> List Nat
  decompose' n [] = []
  decompose' n (x ∷ xs) with mod n x == zero 
  ... | true = x ∷ (decompose' (div n x) xs)
  ... | false = decompose' n xs

  decompose : Nat → List Nat
  decompose n = decompose' n (allPosiblePrimeFactors n)
 

  prodl : List Nat -> Nat
  prodl []  = suc zero
  prodl (x ∷ xs) = x * (prodl xs)

  primel : List Nat -> Bool
  primel [] = true
  primel (x ∷ xs) with isPrime x
  ... | true = primel xs
  ... | false = false

  data _≡_ {A : Set} : A -> A -> Set where
    refl : {x : A} -> x ≡ x 
  infix 10 _≡_

  {-# BUILTIN EQUALITY _≡_ #-}


  -- descomponer devuelve todos primos y el producto de descomponer es x

  -- producto
  existencia : ∀ (n : Nat) -> primel (decompose (suc (suc n))) ≡ true
  existencia zero = refl
  existencia (suc n) with (decompose (suc (suc (suc n))))
  ... | [] = refl
  ... | x ∷ xs = {!   !}