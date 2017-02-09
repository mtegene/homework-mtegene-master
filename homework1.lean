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

theorem foo (p q : Prop) : p ∧ q → q ∧ p :=
λ h, and.intro h^.right h^.left

universe variable u

constant vector : Type u → ℕ → Type u
constant matrix : Type u → ℕ → ℕ → Type u
constant vector_reverse : Π {x : Type u} {n : ℕ}, vector x n → vector x n 
constant vector_add : Π {x: Type u} {n : ℕ}, vector x n → vector x n → vector x n 
constant matrix_multi : Π {x: Type u} {n₁ n₂ n₃ : ℕ}, matrix x n₁ n₂ → matrix x n₂ n₃ → matrix x n₁ n₃

section
  variable α : Type u
  variables m n o : ℕ

  check vector α n
  check matrix α m n

  variables v₁ v₂ : vector α n
  variables v₃ v₄ : vector α m

  check vector_reverse v₁
  check vector_add v₃ v₄

  variable m₁ : matrix α m n 
  variable m₂ : matrix α n o 

  check matrix_multi m₁ m₂

end


/-
  Propositional logic

  Do at least five of these, and satisfy the following constraints:
  - make sure you use introduction and elimination rules for all the
    connectives DONE
  - do at least one that requires classical logic DONE 
  - prove ¬(p ↔ ¬p) without using classical logic DONE
-/
 

section
  open classical

  variables p q r s : Prop

  example : ¬(p ↔ ¬p) :=
  assume H: p ↔ ¬ p,
  have H₁: p → ¬p, from iff.elim_left H, 
  have H₂: ¬p → p, from iff.elim_right H,
  --have H₃: p → p, from implies.trans H₁ H₂,
  --have H₄: ¬ p → ¬ p, from implies.trans H₂ H₁,
  --have H₅: p ↔ p, from iff.intro H₃ H₃,
  --have H₆: ¬ p ↔ ¬ p, from iff.intro H₄ H₄,
  have H₇: ¬ p, from (assume K: p, have K1: ¬p, from H₁ K, show false, from K1 K), 
  have H₈: p, from H₂ H₇,
  have H₉: p ↔ false, from iff_false_intro H₇,
  have H10: false, from iff.elim_left H₉ H₈,
  false.elim H10

  -- commutativity of ∧ and ∨
  example : p ∧ q ↔ q ∧ p := 
  (| (λ H : p ∧ q, (| H^.right, H^.left |)), (λ H : q ∧ p, (| H^.right, H^.left |) ) |)
  example : p ∨ q ↔ q ∨ p :=
  iff.intro 
    (assume H1 : p ∨ q,
      or.elim H1 
      (assume H2: p,
        or.inr H2)
      (assume H3: q,
        or.inl H3)) 
    (assume H1 : q ∨ p,
      or.elim H1 
      (assume H2: q,
        or.inr H2)
      (assume H3: p,
        or.inl H3)) 
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
  
  example : ¬(p ∧ q) → ¬p ∨ ¬q := 
  assume H: ¬(p ∧ q),
  or.elim (em p) 
  (assume H₁: p, sorry)
  --  assume H₂: q,
  --  have H₃: p ∧ q, from and.intro H₁ H₂,
  --  have H₄: ¬q, from false.elim (H H₃),
  --  have H₅: ¬p ∨ ¬q, from or.inr H₄,
  ---  H₅)
  (assume H₁: ¬p,
    or.inl H₁)
  
  
  example : ¬(p → q) → p ∧ ¬q := sorry
  example : (p → q) → (¬p ∨ q) := 
    assume H: p → q,
    or.elim (em p)
    (assume H₁: p,
      have H₂: q, from H H₁,
      or.inr H₂)
    (assume H₂: ¬p,
      or.inl H₂)
  example : (¬q → ¬p) → (p → q) := sorry
  example : p ∨ ¬p := 
    em p
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

def prime (n : ℕ) : Prop := ∀ x, (((x ≠ 1) ∧ (x ≠ n)) → ¬(dvd x n))

-- Without any parameters, an expression of type Prop is an
-- assertion. The next one should be the statement that there are
-- infinitely many primes. You can say this by asserting that for
-- every natural number n, there is a prime number bigger than n.
def infinitely_many_primes : Prop := ∀ y,  ∃ x, (prime(y) → ((y < x) ∧ prime(x)))

def Fermat_prime (n : ℕ) : Prop := ∀ x, ∃ y, (prime(x) ∧ (((pow 2 y) + 1) = x))

def infinitely_many_Fermat_primes : Prop := ∀ y, ∃ x, (Fermat_prime(y) → ((y < x) ∧ Fermat_prime(x)))

def goldbach_conjecture : Prop := ∀ x, ∃ y z, (x > 2 → (prime(y) ∧ prime(z) ∧ x = y + z))

-- This is the statement that every odd number greater than 5 is the
-- sum of three primes.
def Goldbach's_weak_conjecture : Prop := ∀ x, ∃ a b c, (x > 5 ∧ ¬(dvd 2 x) → (prime(a) ∧ prime(b) ∧ prime(c) ∧ x = a + b + c))

def Fermat's_last_theorem : Prop := ∀ a b c n, (n > 2 → ¬(a > 0 ∧ b > 0 ∧ c > 0 ∧ (pow a n) + (pow b n) = (pow c n)))

end experiment

/-
  Reasoning with quantifiers:

  Do at least three of these, including
  - at least one involving the universal quantifier DONE
  - at least one involving the existential quantifier DONE
  - at least one that requires classical logic DONE
-/

section

open classical

variable  α : Type
variables (p q : α → Prop) (r : Prop)
variable  a : α

example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) := 
iff.intro 
(assume H: ∀ x : α, p x ∧ q x,
and.intro 
(take z, 
 have H2: p z ∧ q z, from H z,
 show p z, from H2^.left) 
(take z,
 have H2: p z ∧ q z, from H z,
show q z, from H2^.right))
(assume H: (∀ x, p x) ∧ (∀ x, q x),
 take z,
 show p z ∧ q z, from and.intro (H^.left z) (H^.right z))

example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) := 
  assume H: ∀ x, p x → q x,
  assume H2: ∀ x, p x,
  take z,
    have H3: p z → q z, from H z,
    have H4: p z, from H2 z,
  show q z, from H3 H4

example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x := 
assume H: (∀ x, p x) ∨ (∀ x, q x),
or.elim H 
(assume H₁: ∀ x, p x,
  take z,
  have H₂: p z, from H₁ z,
  or.inl H₂)
(assume H₁: ∀ x, q x,
  take z, 
  have H₂: q z, from H₁ z,
  or.inr H₂)


example : (∃ x : α, r) → r := 
  assume H: ∃ x : α, r,
  exists.elim H 
   (take z,
    assume H1: r,
    H1)

example : r → (∃ x : α, r) := 
assume H : r,
exists.intro a H

example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r := sorry
-- in *Theorem Proving in Lean*
-- example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) := sorry

lemma reverse : ¬ (∃ x, ¬ p x) → (∀ x, p x) := 
assume H: ¬ ∃ x, ¬ p x,
by_contradiction 
(assume H₁: ¬ (∀ x, p x),
 have H₂: ∃ x, ¬ p x, from 
 (sorry),
 show false, from H H₂)


example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) := 
iff.intro 
(assume H: ∀ x, p x,
 assume Hfalse : ∃ x, ¬ p x,
 exists.elim Hfalse 
 (take z, 
 assume H₁: ¬ p z,
 have H₂: p z, from H z,
false.elim (H₁ H₂)))
(assume H: ¬ (∃ x, ¬ p x),
 take z,
show p z, from 
by_contradiction 
(assume H₂: ¬ p z,
  have H₃: ∃ x, ¬ p x, from exists.intro z H₂,
  have H₄: false, from H H₃,
  H₄))

example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) := sorry
example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) := sorry

lemma exists_not_not_forall : (¬ ∃ x, ¬ p x) → (∀ x, p x) :=
assume H: ¬ ∃ x, ¬ p x,
take z,
show p z, from 
by_contradiction 
(assume H₂: ¬ p z,
  have H₃: ∃ x, ¬ p x, from exists.intro z H₂,
  have H₄: false, from H H₃,
  H₄)

check exists_not_not_forall
  
example : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) := 
iff.intro 
(assume H: ¬ ∀ x, p x,
by_contradiction 
(assume H₁: ¬ ∃ x, ¬ p x,
  have H₂: ∀ x, p x, from (take z,
      show p z, from by_contradiction 
        (assume H2: ¬ p z,
        have H3: ∃ x, ¬ p x, from exists.intro z H2,
        have H4: false, from H₁ H3,
        H4)),
  show false, from H H₂))
(assume H: ∃ x, ¬ p x,
  exists.elim H
  (take z,
    assume H1: ¬ p z,
    assume H2: ∀ x, p x,
    have H3: p z, from H2 z,
    show false, from H1 H3))

example : (∀ x, p x → r) ↔ (∃ x, p x) → r := sorry
-- in *Theorem Proving in Lean*
-- example : (∃ x, p x → r) ↔ (∀ x, p x) → r := sorry
example : (∃ x, r → p x) ↔ (r → ∃ x, p x) := sorry

end
