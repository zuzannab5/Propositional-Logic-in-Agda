module main where

open import Data.Bool renaming (_∧_ to _`and`_ ; _∨_ to _`or`_)
open import Data.Fin hiding (_+_;_<_ ; _≤_)
open import Data.Fin hiding (_<_ ; _≤_)
open import Data.Nat
open import Data.Product
open import Function using (_∘_; id)
open import Relation.Binary.PropositionalEquality renaming (sym to _⁻¹; trans to _◾_)

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

-- nadanie znaczenia formułom (przyjmuje formułę i wartościowanie zmiennych zwraca obliczoną wartość logiczną)
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
-- zupełność
-- -------------

-- twierdzenie o zupełności

postulate _⇛_          : ∀{l}(Γ : Cxt l)(ψ : Props n) → Props n

postulate lemat1       : ∀{l}{Γ : Cxt l}{ψ : Props n} → Γ ⊨ ψ → ∅ ⊨ Γ ⇛ ψ

postulate lemat2       : ∀{η : Props n} → ∅ ⊨ η → ∅ ⊢ η

postulate lemat3       : ∀{l}{Γ : Cxt l}{ψ : Props n} → ∅ ⊢ (Γ ⇛ ψ) → Γ ⊢ ψ

completeness : ∀{l}{Γ : Cxt l}{φ : Props n} → Γ ⊨ φ → Γ ⊢ φ
completeness = lemat3 ∘ lemat2 ∘ lemat1


