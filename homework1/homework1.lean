/-
  Dependent types

  In class, I presented "vector α n" and "matrix α m n" as examples of
  dependent types. Make up some operations on these types -- like
  "vector_add" or "vector_reverse" -- and declare constants of the
  right type to describe them. Use implicit arguments for parameters
  that can be inferred. Then use "check" to make sure they work.

  You can make up other dependent types if you would like. Don't
  worry about the definitions; just declare constants with the right
  types.
-/

universe variable u

constant vector : Type u → ℕ → Type u
constant matrix : Type u → ℕ → ℕ → Type u

section
  variable α : Type u
  variables m n : ℕ

  check vector α n
  check matrix α m n

  variables v₁ v₂ : vector α n
  variables v₃ v₄ : vector α m
end

/-
  Propositional logic

  Do at least five of these, and satisfy the following constraints:
  - make sure you use introduction and elimination rules for all the
    connectives
  - do at least one that requires classical logic
  - prove ¬(p ↔ ¬p) without using classical logic
-/

section
  open classical

  variables p q r s : Prop

  -- commutativity of ∧ and ∨
  example : p ∧ q ↔ q ∧ p := sorry
  example : p ∨ q ↔ q ∨ p := sorry

  -- associativity of ∧ and ∨
  example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) := sorry
  example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) := sorry

  -- distributivity
  -- this next one is in *Theorem Proving in Lean*
  -- example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := sorry
  example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := sorry

  -- other properties
  example : (p → (q → r)) ↔ (p ∧ q → r) := sorry
  example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) := sorry
  example : ¬(p ∨ q) ↔ ¬p ∧ ¬q := sorry
  example : ¬p ∨ ¬q → ¬(p ∧ q) := sorry
  example : ¬(p ∧ ¬ p) := sorry
  example : p ∧ ¬q → ¬(p → q) := sorry
  example : ¬p → (p → q) := sorry
  example : (¬p ∨ q) → (p → q) := sorry
  example : p ∨ false ↔ p := sorry
  example : p ∧ false ↔ false := sorry
  example : ¬(p ↔ ¬p) := sorry
  example : (p → q) → (¬q → ¬p) := sorry

  -- these require classical reasoning
  example : (p → r ∨ s) → ((p → r) ∨ (p → s)) := sorry
  example : ¬(p ∧ q) → ¬p ∨ ¬q := sorry
  example : ¬(p → q) → p ∧ ¬q := sorry
  example : (p → q) → (¬p ∨ q) := sorry
  example : (¬q → ¬p) → (p → q) := sorry
  example : p ∨ ¬p := sorry
  example : (((p → q) → p) → p) := sorry
end

/-
  Writing mathematical assertions

  I put the definitions of "divides" and "pow" in a funny namespace
  here, to avoid conflicts with similarly-named definitions elsewhere
  in the library (though at the moment though would not pose any such
  conflicts). Don't worry about the recursive definition of pow or the
  "instance" declaration -- we will discuss those later.

  Fill in the definitions and statements indicated; you can use
  Wikipedia to look them up.
-/

namespace experiment

def divides (m n : ℕ) : Prop := ∃ k, m * k = n

instance : has_dvd nat := ⟨divides⟩

def pow (m : ℕ) : ℕ → ℕ
| 0     := 1
| (n+1) := m * pow n

infix `^` := pow

section
  variables m n : ℕ

  check m ∣ n     -- use \| to type the divides symbol
  check dvd m n   -- this is equivalent
  check m^n
  check pow m n

  vm_eval 2^10
  vm_eval 2^100
  vm_eval 10^2
end

def even (n : ℕ) : Prop := 2 ∣ n

def prime (n : ℕ) : Prop := sorry

-- Without any parameters, an expression of type Prop is an
-- assertion. The next one should be the statement that there are
-- infinitely many primes. You can say this by asserting that for
-- every natural number n, there is a prime number bigger than n.
def infinitely_many_primes : Prop := sorry

def Fermat_prime (n : ℕ) : Prop := sorry

def infinitely_many_Fermat_primes : Prop := sorry

def goldbach_conjecture : Prop := sorry

-- This is the statement that every odd number greater than 5 is the
-- sum of three primes.
def Goldbach's_weak_conjecture : Prop := sorry

def Fermat's_last_theorem : Prop := sorry

end experiment

/-
  Reasoning with quantifiers:

  Do at least three of these, including
  - at least one involving the universal quantifier
  - at least one involving the existential quantifier
  - at least one that requires classical logic
-/

section

variable  α : Type
variables (p q : α → Prop) (r : Prop)
variable  a : α

example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) := sorry
example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) := sorry
example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x := sorry

example : (∃ x : α, r) → r := sorry
example : r → (∃ x : α, r) := sorry
example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r := sorry
-- in *Theorem Proving in Lean*
-- example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) := sorry

example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) := sorry
example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) := sorry
example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) := sorry
example : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) := sorry

example : (∀ x, p x → r) ↔ (∃ x, p x) → r := sorry
-- in *Theorem Proving in Lean*
-- example : (∃ x, p x → r) ↔ (∀ x, p x) → r := sorry
example : (∃ x, r → p x) ↔ (r → ∃ x, p x) := sorry

end
