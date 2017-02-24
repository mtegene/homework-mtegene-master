namespace nat

/-
  Part 1. Summation.
-/
-- define summation up to (but not including) n
def sum_upto (n : ℕ) (f : ℕ → ℕ) : ℕ :=
nat.rec_on n 0 (λ n recval, recval + f n)

-- the computation rules
theorem sum_upto_zero (f : ℕ → ℕ) : sum_upto 0 f = 0 := rfl
theorem sum_upto_succ (f : ℕ → ℕ) (n : ℕ) : sum_upto (succ n) f = sum_upto n f + f n := rfl

-- fill in the next two proofs
theorem sum_upto_mul (n m : ℕ) (f : ℕ → ℕ) : sum_upto n (λ x, m * f x) = m * (sum_upto n f) :=
nat.induction_on n rfl 
(take n,
 assume ih: sum_upto n (λ x, m * f x) = m * (sum_upto n f),
 show sum_upto (succ n) (λ x, m * f x) = m * (sum_upto (succ n) f), from
calc
  sum_upto (succ n) (λ x, m * f x) = sum_upto n (λ x, m * f x) + (λ x, m * f x) n : by rw sum_upto_succ
          ...                      = m * (sum_upto n f) + (λ x, m * f x) n        : by rw ih
          ...                      = m * (sum_upto n f) + m * ((λ x, f x ) n)     : rfl
          ...                      = m * (sum_upto n f + (λ x, f x) n)            : by rw mul_add
          ...                      = m * (sum_upto n f + f n)                     : rfl
          ...                      = m * (sum_upto (succ n) f)                    : by rw sum_upto_succ)

theorem sum_upto_id (n : ℕ) : 2 * sum_upto (succ n) id = n * (n + 1) :=
nat.induction_on n rfl
(take n,
  assume ih: 2 * sum_upto (succ n) id = n * (n + 1),
  show 2 * sum_upto (succ (succ n)) id = (succ n) * ((succ n) + 1), from
  calc 
    2 * sum_upto (succ (succ n)) id = 2 * (sum_upto (succ n) id + id (succ n)) : by rw sum_upto_succ
            ...                     = 2 * (sum_upto (succ n) id) + 2 * id(succ n) : by rw mul_add
            ...                     = n * (n + 1) + 2 * id (succ n)          : by rw ih
            ...                     = n * (n + 1) + 2 * (succ n)             : rfl
            ...                     = n * (succ n) + 2 * (succ n)            : rfl
            ...                     = (succ n) * n + 2 * (succ n)            : by rw mul_comm
            ...                     = (succ n) * n + (succ n) * 2            : by simp --by rw mul_comm
            ...                     = (succ n) * (n + 2)                     : by rw mul_add 
            ...                     = (succ n) * (n + 1 + 1)                 : rfl
            ...                     = (succ n) * ((succ n) + 1)              : rfl)

/-
   Part 2. Exponentiation on nat.
-/

-- the definition
def pow : ℕ → ℕ → ℕ
| m 0 := 1
| m (succ n) := m * pow m n

-- declare the notation
infix ^ := pow

-- the computation rules
theorem pow_zero (m : ℕ) : m ^ 0 = 1 := rfl
theorem pow_succ (m n : ℕ) : m ^ (succ n) = m * m ^ n := rfl

-- fill in the next four proofs
theorem zero_pow_succ (n : ℕ) : 0^(succ n) = 0 := 
nat.induction_on n rfl 
( take n,
  assume ih,
  show 0^(succ (succ n)) = 0, from 
  calc
      0^(succ (succ n)) = 0 * 0^(succ n)  : by rw pow_succ
          ...           = 0 * 0           : by rw ih
          ...           = 0               : by rw mul_zero)

theorem pow_add (m n k : ℕ) : m ^ (n + k) = m ^ n * m ^ k :=
nat.induction_on n 
  (calc 
      m ^ (0 + k) = m ^ k         : by rw zero_add
          ...     = 1 * m ^ k     : by rw one_mul
          ...     = m ^ 0 * m ^ k : rfl) 
  (take n,
    assume ih,
    show m ^ ((succ n) + k) = m ^ (succ n) * m ^ k, from 
    calc
     m ^ ((succ n) + k) = m ^ ((n + 1) + k)    : rfl
          ...          = m ^ (k + (n + 1))    : by rw add_comm
          ...          = m ^ ((k + n) + 1)    : by rw add_assoc
          ...          = m ^ ((n + k) + 1)    : by simp
          ...          = m ^ (succ (n + k))   : rfl
          ...          = m * m ^ (n + k)      : by rw pow_succ
          ...          = m * (m ^ n * m ^ k)  : by rw ih
          ...          = (m * m ^ n) * m ^ k  : by rw mul_assoc
          ...          = m ^ (succ n) * m ^ k : by rw pow_succ)


theorem pow_mul (m n k : ℕ) : m ^ (n * k) = (m ^ n) ^ k :=
nat.induction_on k 
(calc
  m ^ (n * 0) = m ^ (0)     : by rw mul_zero
      ...     = 1           : by rw pow_zero
      ...     = (m ^ n) ^ 0 : by rw pow_zero) 
(take k,
 assume ih,
 show  m ^ (n * (succ k)) = (m ^ n) ^ (succ k), from 
 calc
      m ^ (n * (succ k)) = m ^ (n * (k + 1))      : rfl
            ...          = m ^ (n * k + n * 1)    : by rw mul_add
            ...          = m ^ (n * k) * m ^ (n * 1) : sorry
            ...          = (m ^ n) ^ k * m ^ (n * 1) : by rw ih
            ...          = (m ^ n) ^ k * (m ^ n) : by rw mul_one
            ...          = (m ^ n) * (m ^ n) ^ k : by rw mul_comm
            ...          = (m ^ n) ^ (succ k)     : by rw pow_succ)

check zero_lt_one
check @mul_pos

theorem pow_pos {m : ℕ} (h : m > 0) {n : ℕ} : m^n > 0 :=
nat.induction_on n 
( have H1: m^0 = 1, from rfl, 
  show m^0 > 0, from zero_lt_one)
( take n,
  assume ih,
  have H1: m^ (succ n) = m * m^n, from rfl,
  show m^(succ n) > 0, from mul_pos h ih)

/- The last one is pow_le, below. It is not easy, so just give it your best
   shot. The next few examples might be helpful. -/

-- By the way, this is a useful trick. I will explain it in class.
example : 3 < 7 := dec_trivial

check @mul_le_mul
check @mul_le_mul_left
check @nat.zero_le

example (m : ℕ) (h : m > 0) : m ≥ 1 := succ_le_of_lt h
-- actually, on ℕ, x < y is defined to mean succ x < y
example (m : ℕ) (h : m > 0) : m ≥ 1 := h

example (m n : ℕ) (h : m ≤ n) : ∃ k, m + k = n := le.dest h

lemma le_mul_self (m n : ℕ) (h : m = 0 ∨ n > 0) : m ≤ m * n :=
or.elim h
  (suppose m = 0,
    begin simp [this] end)
  (suppose n > 0,
    have m * 1 ≤ m * n,
      from mul_le_mul_left _ this,
    begin
      rw mul_one at this, exact this
    end)
check @mul_le_mul_left
-- Be careful! The following theorem is false without the hypotheses m > 0 (why?)
theorem pow_le (m : ℕ) {n k : ℕ} (h : n ≤ k) (mpos : m > 0) : m^n ≤ m^k :=
have H1: m*n ≤ m*k, from (mul_le_mul_left m h),
sorry
--Are you supposed to use induction? Because I couldn't figure out what I 
--was supposed to induct on.
--Without induction, I do not know how to expand m ^ n since ^ is defined for
--m ^ succ n


check le_of_eq

/-
  Part 3. Division on the Natural Numbers.

  These have nothing to do with inductive types (except for the fact that
  the existential quantifier is really an inductive type).
-/

protected def dvd (m n : ℕ) : Prop := ∃ k, n = m * k

instance : has_dvd nat := ⟨nat.dvd⟩

-- type "dvd" with \|

theorem dvd_rfl (m : ℕ) : m ∣ m :=
exists.intro 1 (by rw [(mul_one m)])

theorem dvd_trans : ∀ {m n k : ℕ}, m ∣ n → n ∣ k → m ∣ k :=
take m n k,
assume h1 h2,
have H1: ∃ a, n = m * a, from h1,
have H2: ∃ b, k = n * b, from h2,
exists.elim H1
(take a,
  assume H3: n = m * a,
  exists.elim H2 
  (take b,
    assume H4: k = n * b,
    show ∃ c, k = m * c, from 
      (have H5: k = m * a * b, from (by rw [-H3, H4]), 
       have H6: k = m * (a * b), from (by rw [H5, mul_assoc]),
      exists.intro (a * b) H6)))


theorem dvd_mul_left (m n : ℕ) : m ∣ m * n :=
have H1: m ∣ m, from (dvd_rfl m),
have H2: ∃ a, m = m * a, from H1,
exists.elim H2
(take a,
  assume H3: m = m * a,
  have H4: m * n = m * a * n, from (by rw [-H3]),
  have H5: m * n = m * (a * n), from (by rw [H4, mul_assoc]),
  show m ∣ m * n , from exists.intro (a * n) H5)

theorem dvd_mul_right (m n : ℕ) : m ∣ n * m :=
have H1: m ∣ m * n, from (dvd_mul_left m n),
have H2: ∃ a, m * n = m * a, from H1,
exists.elim H2 
(take a,
  assume H3: m * n = m * a,
  have H4: n * m = m * a, from (by rw [-H3, mul_comm]),
  show m ∣ n * m, from exists.intro a H4) 

theorem dvd_add : ∀ {m n k : ℕ}, m ∣ n → m ∣ k → m ∣ (n + k) :=
take m n k,
take h₁ h₂,
have H1: ∃ a, n = m * a, from h₁,
have H2: ∃ b, k = m * b, from h₂,
exists.elim H1
(take a,
  assume H3: n = m * a,
  exists.elim H2 
  (take b,
   assume H4: k = m * b,
   have H5: n + k = m * (a + b), from (by rw [H3, H4, mul_add]),
   show m ∣ (n + k), from exists.intro (a + b) H5))

end nat

/-
  Part 4. The size of a binary tree.

  This one is really optional, for those of you who said you want something
  more challenging.
-/

open nat

inductive btree : Type
| leaf : btree
| node : btree → btree → btree

namespace btree

def size : btree → ℕ
| leaf := 1
| (node b₁ b₂) := size b₁ + size b₂ + 1

theorem size_pos (b : btree) : size b > 0 :=
btree.induction_on b
  dec_trivial
  (take b₁ b₂,
    assume ih₁ ih₂,
     succ_pos _)

def depth : btree → ℕ
| leaf := 1
| (node b₁ b₂) := max (depth b₁) (depth b₂) + 1

-- This is a scandal. I promise, eventually the simplifier will do this.
lemma add_self_eq_two_mul (m : ℕ) : m + m = 2 * m :=
calc
  m + m = (1 + 1) * m : by simp [add_mul, one_mul]
    ... = 2 * m       : rfl

-- these might be useful.
check @nat.sub_add_cancel
check @nat.add_sub_assoc

-- prove this by induction on binary trees
theorem size_le' : ∀ b : btree, size b + 1 ≤ 2 ^ depth b :=
take b,
btree.induction_on b 
dec_trivial 
(take b₁ b₂,
 assume ih₁ ih₂,
 have H1: (size b₁ + 1) + (size b₂ + 1) ≤ (2 ^ depth b₁) + (2 ^ depth b₂), from (add_le_add ih₁ ih₂), 
 have H2: 2 ^ (max (depth b₁) (depth b₂) + 1) = 2 ^ depth (node b₁ b₂), from rfl,
 have H3:  2 ^ (max (depth b₁) (depth b₂) + 1) ≤ 2 ^ depth (node b₁ b₂), from (le_of_eq H2),
 calc
    size (node b₁ b₂) + 1 = (size b₁ + size b₂ + 1) + 1 : rfl
          ...             = (size b₁ + 1) + (size b₂ + 1) : by simp
          ...             ≤ (2 ^ depth b₁) + (2 ^ depth b₂) : H1
          ...             ≤ 2 ^ (max (depth b₁) (depth b₂) + 1) : sorry
          ...             = 2 ^ depth (node b₁ b₂) : rfl
          ...             ≤ 2 ^ depth (node b₁ b₂) : H3)
check @add_le_add


theorem size_le : ∀ b : btree, size b ≤ 2 ^ depth b - 1:=
take b,
have size b = size b + 1 - 1, from rfl,
calc
  size b = size b + 1 - 1 : this
     ... ≤ 2 ^ depth b - 1 : nat.sub_le_sub_right (size_le' b) _

end btree
