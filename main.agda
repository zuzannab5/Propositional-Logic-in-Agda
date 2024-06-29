module main where

open import Data.Bool renaming (_∧_ to _`and`_ ; _∨_ to _`or`_) hiding (_≟_)
open import Data.Fin hiding (_+_ ; _<_ ; _≤_)
open import Data.Fin.Properties hiding (≤-refl) renaming (_≟_ to _F≟_)
open import Data.Empty hiding (⊥-elim ; ⊥)
open import Data.Nat
open import Data.Nat.Properties
open import Relation.Nullary 
open import Relation.Nullary.Decidable
open import Data.Product
open import Function using (_∘_; id)
open import Relation.Binary hiding (_⇒_)
open import Relation.Binary.PropositionalEquality renaming (sym to _⁻¹; trans to _◾_)
open import Function

-- repozytorium: https://github.com/zuzannab5/Propositional-Logic-in-Agda

-- We use the following notational conventions:
    -- Γ contexts
    -- φi, ψ, χ, η propositions
    -- pi propositional atoms
    -- ρ valuation
    -- σ, σi, δ proof trees

-- datatype Fin n is the type of natural numbers less than n.

n : ℕ
n = 0

infix  10 ~_
infixr 9 _∧_
infixr 8 _∨_
infixr 7 _⇒_
infixl 6 _∙_
infix  5 _⊢_
--   A propositional formula
--           is a string of indivisible propositional atoms and logical connective

data Props (n : ℕ) : Set where
  ⊥ ⊤         : Props n  -- false and true
  patom       : Fin n → Props n -- propositional atom
  ~_          : Props n → Props n
  _∨_ _∧_ _⇒_ : Props n → Props n → Props n


-- p₀ ⇒ (p₀ ∨ ∼ p₁) 
example : Props 2
example = patom zero ⇒ (patom zero ∨ ~ patom (suc zero))


--  A context 
--          is defined as a list where one can insert new elements at the end.
data Cxt : ℕ → Set where
    ∅ : Cxt zero
    _∙_ : {l : ℕ} → Cxt l → Props n → Cxt (suc l)
-- It has one natural number index, this carries the length of the context.

data _⊢_ : {l : ℕ} (Γ : Cxt l) (ψ : Props n) → Set where
    var     : ∀ {l} {Γ : Cxt l}{ψ}  → Γ ∙ ψ ⊢ ψ
    weaken  : ∀{l}{Γ : Cxt l}{φ ψ}  → Γ ⊢ ψ
                                    ---------
                                    → Γ ∙ φ ⊢ ψ
    ⊤-i    : ∀{l}{Γ : Cxt l}        → Γ ⊢ ⊤

    ⊥-e    : ∀{l}{Γ : Cxt l}{ψ}     → Γ ⊢ ⊥
                                    -----
                                    → Γ ⊢ ψ
                                    
    ~-i    : ∀{l}{Γ : Cxt l}{ψ}     → Γ ∙ ψ ⊢ ⊥
                                    ---------
                                    → Γ ⊢ ~ ψ    

    ~-e    : ∀{l}{Γ : Cxt l}{ψ}     → Γ ⊢ ψ → Γ ⊢ ~ ψ
                                        ----------------
                                    → Γ ⊢ ⊥

    ⇒-i    : ∀{l}{Γ : Cxt l}{φ ψ}   → Γ ∙ φ ⊢ ψ
                                        ---------
                                    → Γ ⊢ φ ⇒ ψ
                                    
    ⇒-e    : ∀{l}{Γ : Cxt l}{φ ψ}   → Γ ⊢ φ ⇒ ψ → Γ ⊢ φ
                                        -----------------
                                    → Γ ⊢ ψ

    ∧-i    : ∀{l}{Γ : Cxt l}{φ ψ}   → Γ ⊢ φ → Γ ⊢ ψ
                                        -------------
                                    → Γ ⊢ φ ∧ ψ
                                    
    ∧-e₁   : ∀{l}{Γ : Cxt l}{φ ψ}   → Γ ⊢ φ ∧ ψ
                                        ---------
                                    → Γ ⊢ φ
                                    
    ∧-e₂   : ∀{l}{Γ : Cxt l}{φ ψ}   → Γ ⊢ φ ∧ ψ
                                        ---------
                                    → Γ ⊢ ψ

    ∨-i₁   : ∀{l}{Γ : Cxt l}{φ ψ}   → Γ ⊢ φ
                                        ---------
                                    → Γ ⊢ φ ∨ ψ
                                    
    ∨-i₂   : ∀{l}{Γ : Cxt l}{φ ψ}   → Γ ⊢ ψ
                                        ---------
                                    → Γ ⊢ φ ∨ ψ
                                    
    ∨-e    : ∀{l}{Γ : Cxt l}{φ ψ χ} → Γ ⊢ φ ∨ ψ → Γ ∙ φ ⊢ χ → Γ ∙ ψ ⊢ χ
                                        ---------------------------------
                                    → Γ ⊢ χ
    
    lem    : ∀{l}{Γ : Cxt l}{ψ}     → Γ ⊢ ψ ∨ ~ ψ

-- przemienność ∧
example' : {φ ψ : Props n} → ∅ ⊢ φ ∧ ψ ⇒ ψ ∧ φ
example' = ⇒-i
             (∧-i
               (∧-e₂
                 var)
               (∧-e₁
                 var))


-- typ wartościowanie 
Val : Set
Val = Fin n → Bool

-- nadanie znaczenia formułom (przyjmuje formułę i wartościowanie zmiennych i zwraca obliczoną wartość logiczną)
⟦_⟧ : Props n → Val → Bool
⟦ ⊥       ⟧ ρ = false
⟦ ⊤       ⟧ ρ = true
⟦ patom x ⟧ ρ = ρ x
⟦ ~ φ     ⟧ ρ = not (⟦ φ ⟧ ρ)
⟦ φ₁ ∨ φ₂ ⟧ ρ = ⟦ φ₁ ⟧ ρ `or`  ⟦ φ₂ ⟧ ρ
⟦ φ₁ ∧ φ₂ ⟧ ρ = ⟦ φ₁ ⟧ ρ `and` ⟦ φ₂ ⟧ ρ
⟦ φ₁ ⇒ φ₂ ⟧ ρ = not (⟦ φ₁ ⟧ ρ) `or` ⟦ φ₂ ⟧ ρ 

-- The meaning of a context is just the conjuction of the meanings of its formulas.
-- nadanie znaczenia kontekstom - koniunkcja znaczenia ich formuł
⟦_⟧ᶜ : {l : ℕ} → Cxt l → Val → Bool
⟦ ∅      ⟧ᶜ ρ = true
⟦ xs ∙ x ⟧ᶜ ρ = ⟦ xs ⟧ᶜ ρ `and` ⟦ x ⟧ ρ

-- This relation states that for all valuations, 
-- if all formulas in the context evaluate to true
-- then the conclusion also evaluates to true.
_⊨_ : {l : ℕ} → Cxt l → Props n → Set
Γ ⊨ ψ = ∀ ρ → ⟦ Γ ⟧ᶜ ρ ≡ true → ⟦ ψ ⟧ ρ ≡ true

infix 5 _⊨_

---------------
-- zgodność
---------------

-- twierdzenie o zgodności
-- dowód wzorowany na podstawie repozytorium dołączonym do pracy : https://bitbucket.org/Leran/propositional-logic/src/master/Soundness.agda

soundness : ∀ {l}{Γ : Cxt l}{ψ : Props n} → Γ ⊢ ψ → Γ ⊨ ψ
soundness {Γ = Γ ∙ ψ} var ρ x  with ⟦ Γ ⟧ᶜ ρ | ⟦ ψ ⟧ ρ
...         | true | true = refl
...         | true | false = x
...         | false | true = refl
...         | false | false = x

-- σ = Γ ⊢ ψ
soundness {Γ = Γ ∙ ψ} (weaken σ) ρ x with ⟦ Γ ⟧ᶜ ρ | inspect ⟦ Γ ⟧ᶜ ρ
...         | true | [ ⟦Γ⟧≡true ]  = soundness σ ρ ⟦Γ⟧≡true
...         | false | [ ⟦Γ⟧≡false ]  = soundness σ ρ (⟦Γ⟧≡false ◾ x)

soundness ⊤-i = λ ρ _ → refl

soundness  (⊥-e σ) ρ x with soundness σ ρ x
... | ()

soundness {Γ = Γ} {~ ψ} (~-i σ) ρ x
  with ⟦ Γ ⟧ᶜ ρ | inspect ⟦ Γ ⟧ᶜ ρ | ⟦ ψ ⟧ ρ | inspect ⟦ ψ ⟧ ρ
...  | true     | [ ⟦Γ⟧≡true ]     | true    | [ ⟦ψ⟧≡true ]

  = soundness σ ρ (subst₂ (λ ⟦Γ⟧ ⟦ψ⟧ → ⟦Γ⟧ `and` ⟦ψ⟧ ≡ true) (⟦Γ⟧≡true ⁻¹) (⟦ψ⟧≡true ⁻¹) refl)
                          
...  | true     | [ _ ]            | false   | [ _ ] = x

soundness {Γ = Γ} {~ ψ} (~-i σ) ρ () | false | [ _ ] | _ | [ _ ]

-- Γ ⊢ ψ → Γ ⊢ ~ ψ
soundness {Γ = Γ} (~-e {ψ = ψ} σ₁ σ₂) ρ x with ⟦ Γ ⟧ᶜ ρ | inspect ⟦ Γ ⟧ᶜ ρ | ⟦ ψ ⟧ ρ | inspect ⟦ ψ ⟧ ρ
...     | true     | [ ⟦Γ⟧≡true ]     | true    | [ ⟦ψ⟧≡true  ] 
            = cong not (⟦ψ⟧≡true ⁻¹) ◾ soundness σ₂ ρ ⟦Γ⟧≡true

...     | false | [ _ ] | true | [ _ ] = x
...     | true | [ ⟦Γ⟧≡true ] | false | [ ⟦ψ⟧≡false ] = (⟦ψ⟧≡false ⁻¹) ◾ soundness σ₁ ρ ⟦Γ⟧≡true

soundness {Γ = Γ} {φ ⇒ ψ} (⇒-i σ) ρ _
  with ⟦ Γ ⟧ᶜ ρ | inspect ⟦ Γ ⟧ᶜ ρ | ⟦ φ ⟧ ρ | inspect ⟦ φ ⟧ ρ
...  | true     | [ ⟦Γ⟧≡true ]     | true    | [ ⟦ψ⟧≡true ]

  = soundness σ ρ (subst₂ (λ ⟦Γ⟧ ⟦ψ⟧ → ⟦Γ⟧ `and` ⟦ψ⟧ ≡ true) (⟦Γ⟧≡true ⁻¹) (⟦ψ⟧≡true ⁻¹) refl)
  
...  | true     | [ _ ]            | false   | [ _ ] = refl

soundness {Γ = Γ} {φ ⇒ ψ} (⇒-i σ) ρ () | false | [ _ ] | _ | [ _ ]

soundness {ψ = ψ} (⇒-e {φ = φ} σ₁ σ₂) ρ x   with ⟦ ψ ⟧ ρ | inspect ⟦ ψ ⟧ ρ | ⟦ φ ⟧ ρ | inspect ⟦ φ ⟧ ρ 
... | true     | [ ⟦ψ⟧≡true ]     | true    | [ ⟦φ⟧≡true ] = refl
... | false     | [ ⟦ψ⟧≡false ]      | true    | [ ⟦φ⟧≡true ] = subst₂ (λ ⟦φ⟧ ⟦ψ⟧ → not ⟦φ⟧ `or` ⟦ψ⟧ ≡ true) ⟦φ⟧≡true ⟦ψ⟧≡false (soundness σ₁ ρ x)
... | true     | [ ⟦ψ⟧≡true ]     | false    | [ ⟦φ⟧≡false ] = refl
... | false     | [ ⟦ψ⟧≡false ]      | false    | [ ⟦φ⟧≡false ] = (⟦φ⟧≡false ⁻¹) ◾ (soundness σ₂ ρ x)

soundness {ψ = φ₁ ∧ φ₂} (∧-i σ₁ σ₂) ρ x   with ⟦ φ₁ ⟧ ρ | inspect ⟦ φ₁ ⟧ ρ | ⟦ φ₂ ⟧ ρ | inspect ⟦ φ₂ ⟧ ρ
...  | true     | [ _ ]            | true     | [ _ ]          = refl
...  | true     | [ _ ]            | false    | [ ⟦φ₂⟧≡false ] = (⟦φ₂⟧≡false ⁻¹) ◾ soundness σ₂ ρ x
...  | false    | [ ⟦φ₁⟧≡false ]   | _        | [ _ ]          = (⟦φ₁⟧≡false ⁻¹) ◾ soundness σ₁ ρ x

soundness {ψ = φ} (∧-e₁ {ψ = ψ} σ) ρ x  with ⟦ φ ⟧ ρ | inspect ⟦ φ ⟧ ρ
...  | true    | [ _ ]  = refl
...  | false    | [ ⟦φ⟧≡false  ]  = subst (λ ⟦φ⟧ → ⟦φ⟧ `and` ⟦ ψ ⟧ ρ ≡ true) ⟦φ⟧≡false (soundness σ ρ x)

soundness {ψ = ψ} (∧-e₂ {φ = φ} σ) ρ x with ⟦ ψ ⟧ ρ | inspect ⟦ ψ ⟧ ρ | ⟦ φ ⟧ ρ | inspect ⟦ φ ⟧ ρ 
...  | true    | [ _ ]           | _       | [ _ ] = refl
...  | false   | [ ⟦ψ⟧≡false ]   | true    | [ ⟦φ⟧≡true ] = subst₂ (λ ⟦φ⟧ ⟦ψ⟧ → ⟦φ⟧ `and` ⟦ψ⟧ ≡ true) ⟦φ⟧≡true ⟦ψ⟧≡false (soundness σ ρ x)
...  | false   | [ ⟦ψ⟧≡false ]   | false    | [ ⟦φ⟧≡false ] = subst₂ (λ ⟦φ⟧ ⟦ψ⟧ → ⟦φ⟧ `and` ⟦ψ⟧ ≡ true) ⟦φ⟧≡false ⟦ψ⟧≡false (soundness σ ρ x)


soundness {ψ = φ ∨ ψ} (∨-i₁ σ) ρ x with ⟦ φ ⟧ ρ | inspect ⟦ φ ⟧ ρ | ⟦ ψ ⟧ ρ  
... | true  | [ _ ]         | _     = refl
... | false | [ ⟦φ⟧≡false ] | false = (⟦φ⟧≡false ⁻¹) ◾ soundness σ ρ x
... | false | [ ⟦φ⟧≡false ] | true = refl 

soundness {ψ = φ ∨ ψ} (∨-i₂ σ) ρ x with ⟦ φ ⟧ ρ
... | true = refl
... | false = soundness σ ρ x

soundness {ψ = χ} (∨-e {φ = φ} {ψ = ψ} σ₁ σ₂ σ₃) ρ x with ⟦ χ ⟧ ρ | inspect ⟦ χ ⟧ ρ | ⟦ ψ ⟧ ρ | inspect ⟦ ψ ⟧ ρ | ⟦ φ ⟧ ρ | inspect ⟦ φ ⟧ ρ
...   | true   | [ _ ]           | _       | [ _ ]           | _       | [ _ ] = refl
...   | false  | [ ⟦χ⟧≡false ]   | false   | [ ⟦ψ⟧≡false ] | false | [ ⟦φ⟧≡false ] = (subst₂ (λ ⟦φ⟧ ⟦ψ⟧ → ⟦φ⟧ `or` ⟦ψ⟧ ≡ false) (⟦φ⟧≡false ⁻¹)  (⟦ψ⟧≡false ⁻¹) refl  ⁻¹) ◾ soundness σ₁ ρ x
...   | false  | [ ⟦χ⟧≡false ]   | true   | [ ⟦ψ⟧≡true ] | false | [ ⟦φ⟧≡false ] = (⟦χ⟧≡false ⁻¹) ◾ soundness σ₃ ρ (subst₂ (λ ⟦Γ⟧ ⟦ψ⟧ → ⟦Γ⟧ `and` ⟦ψ⟧ ≡ true) (x ⁻¹) (⟦ψ⟧≡true ⁻¹)  refl)
...   | false  | [ ⟦χ⟧≡false ]   | false   | [ ⟦ψ⟧≡false ] | true | [ ⟦φ⟧≡true ] = (⟦χ⟧≡false ⁻¹) ◾ soundness σ₂ ρ (subst₂ (λ ⟦Γ⟧ ⟦φ⟧ → ⟦Γ⟧ `and` ⟦φ⟧ ≡ true) (x ⁻¹) (⟦φ⟧≡true ⁻¹)  refl)
...   | false  | [ ⟦χ⟧≡false ]   | true   | [ ⟦ψ⟧≡true  ] | true | [ ⟦φ⟧≡true ] = (⟦χ⟧≡false ⁻¹) ◾ soundness σ₃ ρ (subst₂ (λ ⟦Γ⟧ ⟦ψ⟧ → ⟦Γ⟧ `and` ⟦ψ⟧ ≡ true) (x ⁻¹) (⟦ψ⟧≡true ⁻¹) refl)

soundness {ψ = φ ∨ (~ .φ)} lem ρ _ with (⟦ φ ⟧ ρ)
... | true  = refl
... | false = refl


-- -------------
-- pełność - jeśli Γ sematycznie implikuje ψ, to istnieje drzewo dow. o kontekście Γ i korzeniu ψ
-- dowody wzorowane na podstawie repozytorium dołączonym do pracy : https://bitbucket.org/Leran/propositional-logic/src/master/Soundness.agda
-- -------------

-- ciąg implikacji kolejnych elementów kontekstu i wniosku
_⇛_ : ∀{l}(Γ : Cxt l)(ψ : Props n) → Props n
∅ ⇛ ψ = ψ
(Γ ∙ x) ⇛ ψ = Γ ⇛ (x ⇒ ψ)

-- lemat1 - jeśli kontekst Γ semantycznie implikuje ψ, to Γ ⇛ ψ jest tautologią
lemat1 : ∀{l}{Γ : Cxt l}{ψ : Props n} → Γ ⊨ ψ → ∅ ⊨ (Γ ⇛ ψ)
lemat1 {Γ = ∅} {ψ = ψ} Γ⊨ψ ρ emptTrue = Γ⊨ψ ρ refl
lemat1 {Γ = Γ ∙ x} {ψ = ψ} Γx⊨ψ ρ emptTrue = lemat1 {Γ = Γ} {ψ = x ⇒ ψ} (λ ρ1 → (Γ⊨x⇒ψ ρ1 (Γx⊨ψ ρ1))) ρ emptTrue
  where
    Γ⊨x⇒ψ : ∀ ρ → (⟦ Γ ∙ x ⟧ᶜ ρ ≡ true → ⟦ ψ ⟧ ρ ≡ true) → (⟦ Γ ⟧ᶜ ρ ≡ true → ⟦ x ⇒ ψ ⟧ ρ ≡ true)
    Γ⊨x⇒ψ ρ Γx⊨ψ gammaTrue with ⟦ x ⟧ ρ | ⟦ ψ ⟧ ρ
    ...  | true | true = refl
    ...  | true | false = Γx⊨ψ (subst (λ x → x `and` true ≡ true) (gammaTrue ⁻¹) refl)
    ...  | false | true = refl
    ...  | false | false = refl 


-- lemat2 - wersja tw. o pełności, gdy kontekst jest pusty - każda tautologia ma dowód

-- funkcja, która bierze pᵢ jeśli w wartościowaniu ρ pᵢ jest prawdziwe, w p.p. bierze ~pᵢ 
p̂ᵢ[ρ] : ∀ (ρ : Val) → Fin n → Props n 
p̂ᵢ[ρ] ρ x with (ρ x)
... | true = patom x
... | false = ~ (patom x)

-- bierzemy pierwszych a el. kontekstu, który składa się z powyższych p̂₀,...,p̂ᵢ,...,p̂ₙ₋_1
Cxt[_] : ∀ ρ {a} → (Data.Nat._≤_ a n) → Cxt a
Cxt[ ρ ] {a = zero} z≤n = ∅
Cxt[ ρ ] {a = suc a} α = (Cxt[ ρ ] (≤⇒pred≤ α)) ∙ (p̂ᵢ[ρ] ρ (fromℕ≤ α))


-- lemat211 i lemat212

-- dla każdego wartościowania ρ, jesli ψ jest prawdziwe, to istnieje drzewo dowodowe o korzeniu ψ i kontekście złożonym z p̂ᵢ
lemat211 : ∀ {ψ} ρ → (⟦ ψ ⟧ ρ ≡ true) → (Cxt[ ρ ] ≤-refl) ⊢ ψ

-- dla każdego wartościowania ρ, jesli ψ jest fałszywe, to istnieje drzewo dowodowe o korzeniu ~ ψ i kontekście złożonym z p̂ᵢ
lemat212 : ∀ {ψ} ρ → (⟦ ψ ⟧ ρ ≡ false) → (Cxt[ ρ ] ≤-refl) ⊢ ~ ψ


-- lemat211

lemat211 {⊤} ρ _ = ⊤-i

lemat211 {⊥} ρ ()

lemat211 {~ ψ₁} ρ _
  with ⟦ ψ₁ ⟧ ρ | inspect ⟦ ψ₁ ⟧ ρ
lemat211 {~ ψ₁} ρ () | true | [ _ ]
lemat211 {~ ψ₁} ρ _ | false | [ ψ₁≡false ] = lemat212 ρ ψ₁≡false 

lemat211 {ψ₁ ∨ ψ₂} ρ _
  with ⟦ ψ₁ ⟧ ρ | inspect ⟦ ψ₁ ⟧ ρ | ⟦ ψ₂ ⟧ ρ | inspect ⟦ ψ₂ ⟧ ρ
lemat211 {ψ₁ ∨ ψ₂} ρ () | false | [ _ ] | false | [ _ ]
lemat211 {ψ₁ ∨ ψ₂} ρ _ | true | [ ψ₁≡true ] | _ | [ _ ] = ∨-i₁ (lemat211 ρ ψ₁≡true)
lemat211 {ψ₁ ∨ ψ₂} ρ _ | false | [ _ ] | true | [ ψ₂≡true ] =  ∨-i₂ (lemat211 ρ ψ₂≡true)

lemat211 {ψ₁ ∧ ψ₂} ρ _
  with ⟦ ψ₁ ⟧ ρ | inspect ⟦ ψ₁ ⟧ ρ | ⟦ ψ₂ ⟧ ρ | inspect ⟦ ψ₂ ⟧ ρ
lemat211 {ψ₁ ∧ ψ₂} ρ _ | true | [ ψ₁≡true ] | true | [ ψ₂≡true ] = ∧-i (lemat211 ρ ψ₁≡true) (lemat211 ρ ψ₂≡true)
lemat211 {ψ₁ ∧ ψ₂} ρ () | true | [ _ ] | false | [ _ ]
lemat211 {ψ₁ ∧ ψ₂} ρ () | false | [ _ ] | _ | [ _ ]

lemat211 {ψ₁ ⇒ ψ₂} ρ _
  with ⟦ ψ₁ ⟧ ρ | inspect ⟦ ψ₁ ⟧ ρ | ⟦ ψ₂ ⟧ ρ | inspect ⟦ ψ₂ ⟧ ρ
lemat211 {ψ₁ ⇒ ψ₂} ρ _ | false | [ ψ₁≡false ] | false | [ ψ₂≡false ] = ⇒-i (⊥-e (~-e var (weaken (lemat212 ρ ψ₁≡false))))
lemat211 {ψ₁ ⇒ ψ₂} ρ _ | _ | [ _ ] | true | [ ψ₂≡true ] = ⇒-i (weaken (lemat211 ρ ψ₂≡true))
lemat211 {ψ₁ ⇒ ψ₂} ρ () | true | [ _ ] | false | [ _ ]


-- lemat212

lemat212 {⊥} ρ _ = ~-i var

lemat212 {⊤} ρ ()

lemat212 {~ ψ₁} ρ _
  with ⟦ ψ₁ ⟧ ρ | inspect ⟦ ψ₁ ⟧ ρ
lemat212 {~ ψ₁} ρ _ | true | [ ψ₁≡true ] = ~-i (~-e (weaken (lemat211 ρ ψ₁≡true)) var)
lemat212 {~ ψ₁} ρ () | false | [ _ ]

lemat212 {ψ₁ ∨ ψ₂} ρ _
  with ⟦ ψ₁ ⟧ ρ | inspect ⟦ ψ₁ ⟧ ρ | ⟦ ψ₂ ⟧ ρ | inspect ⟦ ψ₂ ⟧ ρ
lemat212 {ψ₁ ∨ ψ₂} ρ _ | false | [ ψ₁≡false ] | false | [ ψ₂≡false ] = ~-i (∨-e var (~-e var (weaken (weaken (lemat212 ρ ψ₁≡false)))) (~-e var (weaken (weaken (lemat212 ρ ψ₂≡false)))))
lemat212 {ψ₁ ∨ ψ₂} ρ () | true | [ _ ] | _ | [ _ ]
lemat212 {ψ₁ ∨ ψ₂} ρ () | false | [ _ ] | true | [ _ ]

lemat212 {ψ₁ ∧ ψ₂} ρ _
  with ⟦ ψ₁ ⟧ ρ | inspect ⟦ ψ₁ ⟧ ρ | ⟦ ψ₂ ⟧ ρ | inspect ⟦ ψ₂ ⟧ ρ
lemat212 {ψ₁ ∧ ψ₂} ρ () | true | [ _ ] | true | [ _ ]
lemat212 {ψ₁ ∧ ψ₂} ρ _ | true | [ _ ] | false | [ ψ₂≡false ] = ~-i (~-e (∧-e₂ var) (weaken (lemat212 ρ ψ₂≡false)))
lemat212 {ψ₁ ∧ ψ₂} ρ _ | false | [ ψ₁≡false ] | _ | [ _ ] = ~-i (~-e (∧-e₁ var) (weaken (lemat212 ρ ψ₁≡false)))

lemat212 {ψ₁ ⇒ ψ₂} ρ _
  with ⟦ ψ₁ ⟧ ρ | inspect ⟦ ψ₁ ⟧ ρ | ⟦ ψ₂ ⟧ ρ | inspect ⟦ ψ₂ ⟧ ρ
lemat212 {ψ₁ ⇒ ψ₂} ρ () | false | [ _ ] | _ | [ _ ]
lemat212 {ψ₁ ⇒ ψ₂} ρ () | true | [ _ ] | true | [ _ ]
lemat212 {ψ₁ ⇒ ψ₂} ρ _ | true | [ ψ₁≡true ] | false | [ ψ₂≡false ] = ~-i (~-e (⇒-e var (weaken (lemat211 ρ ψ₁≡true))) (weaken (lemat212 ρ ψ₂≡false)))


-- lemat21 - jeśli η jest tautologią, to dla każdego wartościowania ρ, istnieje drzewo dowodowe
-- o korzeniu η, którego kontekst składa się z p̂ᵢ
lemat21 : ∀ {η : Props n} → ∅ ⊨ η → (∀ ρ → ((Cxt[ ρ ] ≤-refl) ⊢ η))
lemat21 ∅⊨η ρ = lemat211 ρ (∅⊨η ρ refl)


-- lemat221 i lemat222

-- uogólnienie lematu22 - jeśli dla każdego wartościowania z kontekstu składającego się z p̂ᵢ o pewnej dł. da się udowodnić η,
-- to dla każdego wartościowania można to zrobić z krótszego kontekstu
postulate lemat221 : ∀ {η} {a b} {an : Data.Nat._≤_ a n} {bn : Data.Nat._≤_ b n} (ba : Data.Nat._≤_ b a) → (∀ ρ → Cxt[ ρ ] an ⊢ η) → (∀ ρ → Cxt[ ρ ] bn ⊢ η)

-- skrócenie długości kontekstu o jeden
lemat222 : ∀ {a} {α : Data.Nat._<_ a n} {η : Props n} → (∀ ρ → Cxt[ ρ ] {suc a} α ⊢ η) → (∀ ρ → Cxt[ ρ ] {a} (≤⇒pred≤ α) ⊢ η)


-- lemat221 - dowód z pracy - kod nie działa

-- lemat221 {a = a} {b = b} ba σ ρ with Data.Nat._≟_ a b
-- lemat221 ba σ ρ | yes refl = subst (λ z → Cxt[ ρ ] z ⊢ _) (≤-unique _ _) (σ ρ)
-- lemat221 {a = zero} z≤n σ ρ | no ¬p = subst (λ x → Cxt[ ρ ] x ⊢ _) ( ≤-unique _ _) (σ ρ)
-- lemat221 {a = suc a} ba σ ρ | no ¬p = lemat221 (lemma-≤2 ba (¬p ◦ _⁻¹)) (lemat222 σ) ρ


-- lemat222

lemat222 {a = a} {α} {η} σ ρ = ∨-e (lem {ψ = patom (fromℕ≤ α)}) (subst (λ z → z ⊢ η) (lemma-Cxt ρ α) (σ (ρ [ α ↦ true ]))) (subst (λ z → z ⊢ η) (lemma-Cxt ρ α) (σ (ρ [ α ↦ false ])))

  where
  -- wymuszone wartościowanie b na ostatnim elemencie
    _[_↦_] : Val → {a : ℕ} → Data.Nat._<_ a n → Bool → Val
    (ρ [ α ↦ b ]) x with fromℕ≤ α F≟ x
    ... | yes p = b
    ... | no ¬p = ρ x

    ~? : Bool → Props n → Props n
    ~? true φ = φ
    ~? false φ = ~ φ

    postulate lemma-Cxt : ∀ ρ {a} (α : Data.Nat._<_ a n) {c : Bool} → Cxt[ ρ [ α ↦ c ] ] α ≡ Cxt[ ρ ] (≤⇒pred≤ α) ∙ ~? c (patom (fromℕ≤ α))
    

-- lemat22 - jeśli dla każdego wartościowania ρ istnieje drzewo dowodowe o korzeniu η, którego
-- kontekst składa się z p̂ᵢ, to η da się udowodnić bez żadnych dodatkowych przesłanek
lemat22 : ∀ {η : Props n} → (∀ ρ → Cxt[ ρ ] ≤-refl ⊢ η) → ∅ ⊢ η
lemat22 σ = lemat221 {bn = z≤n} z≤n σ (λ _ → true)


-- lemat2 - każda tautologia ma dowód
lemat2 : ∀{η : Props n} → ∅ ⊨ η → ∅ ⊢ η
lemat2 = lemat22 ∘ lemat21


-- lemat3 -- jeśli istn. drzewo dowodowe o korzeniu Γ ⇛ ψ i pustym kontekście,
-- to istnieje drzewo dowodowe o korzeniu ψ i kontekście Γ
lemat3 : ∀{l}{Γ : Cxt l}{ψ : Props n} → ∅ ⊢ (Γ ⇛ ψ) → Γ ⊢ ψ
lemat3 {Γ = ∅} {ψ = ψ} δ = δ
lemat3 {Γ = Γ ∙ x} {ψ = ψ} δ = ⇒-e (weaken (lemat3 {Γ = Γ} δ)) var

-- tw. o pełności - jeśli Γ sematycznie implikuje ψ, to istnieje drzewo dow. o kontekście Γ i korzeniu ψ
completeness : ∀{l}{Γ : Cxt l}{ψ : Props n} → Γ ⊨ ψ → Γ ⊢ ψ 
completeness {Γ = Γ} = lemat3 ∘ lemat2 ∘ lemat1 {Γ = Γ}


-- -------------
-- zupełność - Γ sematycznie implikuje ψ wtw., gdy istnieje drzewo dowodowe o kontekście Γ i korzeniu ψ
-- ------------- 
 
-- twierdzenie o zupełności

theorem : ∀{l}{Γ : Cxt l}{φ : Props n} → Γ ⊢ φ → Γ ⊢ φ
theorem = completeness ∘ soundness
   