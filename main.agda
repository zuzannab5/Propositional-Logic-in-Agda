module main where

open import Data.Bool renaming (_∧_ to _`and`_ ; _∨_ to _`or`_)
open import Data.Fin hiding (_+_)
open import Data.Nat
open import Data.Product
open import Function using (_∘_; id)
open import Relation.Binary.PropositionalEquality

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

