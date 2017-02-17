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
sorry

theorem sum_upto_id (n : ℕ) : 2 * sum_upto (succ n) id = n * (n + 1) :=
sorry

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
sorry

theorem pow_add (m n k : ℕ) : m ^ (n + k) = m ^ n * m ^ k :=
sorry

theorem pow_mul (m n k : ℕ) : m ^ (n * k) = (m ^ n) ^ k :=
sorry

check zero_lt_one
check mul_pos

theorem pow_pos {m : ℕ} (h : m > 0) {n : ℕ} : m^n > 0 :=
sorry

/- The last one is pow_le, below. It is not easy, so just give it your best
   shot. The next few examples might be helpful. -/

-- By the way, this is a useful trick. I will explain it in class.
example : 3 < 7 := dec_trivial

check mul_le_mul
check mul_le_mul_left
check nat.zero_le

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

-- Be careful! The following theorem is false without the hypotheses m > 0 (why?)
theorem pow_le (m : ℕ) {n k : ℕ} (h : n ≤ k) (mpos : m > 0) : m^n ≤ m^k :=
sorry

/-
  Part 3. Division on the Natural Numbers.

  These have nothing to do with inductive types (except for the fact that
  the existential quantifier is really an inductive type).
-/

protected def dvd (m n : ℕ) : Prop := ∃ k, n = m * k

instance : has_dvd nat := ⟨nat.dvd⟩

-- type "dvd" with \|

theorem dvd_rfl (m : ℕ) : m ∣ m :=
sorry

theorem dvd_trans : ∀ {m n k : ℕ}, m ∣ n → n ∣ k → m ∣ k :=
sorry

theorem dvd_mul_left (m n : ℕ) : m ∣ m * n :=
sorry

theorem dvd_mul_right (m n : ℕ) : m ∣ n * m :=
sorry

theorem dvd_add : ∀ {m n k : ℕ}, m ∣ n → m ∣ k → m ∣ (n + k) :=
sorry

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
check nat.sub_add_cancel
check nat.add_sub_assoc

-- prove this by induction on binary trees
theorem size_le' : ∀ b : btree, size b + 1 ≤ 2 ^ depth b :=
sorry

theorem size_le : ∀ b : btree, size b ≤ 2 ^ depth b - 1:=
take b,
have size b = size b + 1 - 1, from rfl,
calc
  size b = size b + 1 - 1 : this
     ... ≤ 2 ^ depth b - 1 : nat.sub_le_sub_right (size_le' b) _

end btree
