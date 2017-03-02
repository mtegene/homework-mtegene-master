/-
  The goal of this assignment is to formalize a proof that there are infinitely many
  primes.
-/
import tools.super   -- provides some automation

/-
   The statement
-/

namespace nat

protected def dvd (m n : ℕ) : Prop := ∃ k, n = m * k

instance : has_dvd nat := ⟨nat.dvd⟩

-- remember, type "dvd" with \|
def prime (n : ℕ) : Prop := n ≥ 2 ∧ ∀ m, m ∣ n → m = 1 ∨ m = n

-- this is what you need to prove:
check ∀ n, ∃ p, prime p ∧ p > n

end nat

/-
   Some useful things

   (You can use these also as examples.)
-/

namespace nat

theorem dvd_refl (m : ℕ) : m ∣ m :=
⟨1, by rw mul_one⟩

theorem dvd_trans : ∀ {m n k : ℕ}, m ∣ n → n ∣ k → m ∣ k
| m ._ ._ ⟨u, rfl⟩ ⟨v, rfl⟩ := ⟨u * v, by simp⟩

theorem dvd_mul_left (m n : ℕ) : m ∣ m * n :=
⟨n, rfl⟩

theorem dvd_mul_right (m n : ℕ) : m ∣ n * m :=
⟨n, by simp⟩

theorem dvd_add : ∀ {m n k : ℕ}, m ∣ n → m ∣ k → m ∣ (n + k)
| m ._ ._ ⟨u, rfl⟩ ⟨v, rfl⟩ := ⟨u + v, by simp [mul_add]⟩

theorem eq_sub_of_add_eq {m n k : ℕ} (h : m + n = k) : m = k - n :=
calc
  m = m + n - n : by rw nat.add_sub_cancel
  ... = k - n   : by rw h

theorem mul_sub (n m k : ℕ) : n * (m - k) = n * m - n * k :=
or.elim (le_or_gt m k)
  (assume h : m ≤ k,
    have n * m ≤ n * k, from mul_le_mul_left _ h,
    by simp [sub_eq_zero_of_le h, sub_eq_zero_of_le this])
  (suppose m > k,
    have m ≥ k, from le_of_lt this,
    eq_sub_of_add_eq begin rw [-mul_add, nat.sub_add_cancel this] end)

theorem dvd_sub : ∀ {m n k : ℕ}, m ∣ n → m ∣ k → m ∣ (n - k)
| m ._ ._ ⟨u, rfl⟩ ⟨v, rfl⟩ := begin rw -nat.mul_sub, apply dvd_mul_left end

theorem eq_or_ge_succ_of_ge {n m : ℕ} (h : n ≥ m) : n = m ∨ n ≥ succ m :=
begin
  cases (lt_or_eq_of_le h) with h₁ h₂,
  { right, assumption },
  left, symmetry, assumption
end

theorem eq_zero_or_eq_one_or_ge_2 (n : ℕ) : n = 0 ∨ n = 1 ∨ n ≥ 2 :=
begin
  cases (nat.eq_or_lt_of_le (zero_le n)) with h₀ h₁,
  { left, symmetry, assumption},
  cases (nat.eq_or_lt_of_le h₁) with h₁ h₂,
  { right, left, symmetry, assumption},
  right, right, exact h₂
end

def ge_2_of_prime {p : ℕ} (h : prime p) : p ≥ 2 := h^.left

-- a nice bit of automation!
theorem has_divisor_of_not_prime {n : ℕ} (h₁ : n ≥ 2) (h₂ : ¬ prime n) :
  ∃ m, m ∣ n ∧ m ≠ 1 ∧ m ≠ n :=
by super

def complete_induction_on (n : ℕ) {p : ℕ → Prop} (h : ∀ n, (∀ m < n, p m) → p n) : p n :=
suffices ∀ n, ∀ m < n, p m, from this (succ n) _ (lt_succ_self n),
take n,
nat.induction_on n
  (take m, suppose m < 0, absurd this (not_lt_zero m))
  (take n,
    assume ih : ∀ m < n, p m,
    take m,
    suppose m < succ n,
    or.elim (lt_or_eq_of_le (le_of_lt_succ this))
      (ih m)
      (suppose m = n,
        begin rw this, apply h, exact ih end))

theorem le_of_dvd {m n : ℕ} (h : m ∣ n) (h' : n ≠ 0) : m ≤ n :=
let ⟨k, hk⟩ := h in
have k ≠ 0, begin intro h, rw [h, mul_zero] at hk, contradiction end,
begin
  rw [-(mul_one m), hk], apply mul_le_mul_left,
  cases eq_or_ge_succ_of_ge (zero_le k),
  { contradiction },
  assumption
end

theorem le_or_eq_succ_of_le_succ {m n : ℕ} (h : m ≤ succ n) : m ≤ n ∨ m = succ n :=
begin
  cases m,
  { left, apply zero_le },
  cases lt_or_eq_of_le (le_of_succ_le_succ h),
  { left, assumption },
  right, apply congr_arg, assumption
end

end nat

/-
  Here is an outline of my solution. You do not need to follow it.

  If you succeed and are looking for more to do, try (stating and) proving that there are
  infinitely many primes congruent to 3 modulo 4.
-/

open nat

-- This requires a fair bit of work. I used complete induction on n.
theorem has_prime_divisor (n : ℕ) : n ≥ 2 → ∃ p, prime p ∧ p ∣ n := sorry

def fact : ℕ → ℕ
| 0     := 1
| (n+1) := (n+1) * fact n

theorem fact_ge_1 : ∀ n, fact n ≥ 1 := sorry

theorem fact_ge_self {n : ℕ} (nnz : n ≠ 0) : fact n ≥ n := sorry

theorem dvd_fact_of_le : ∀ n, ∀ m ≤ n, m > 0 → m ∣ fact n := sorry

-- lots of intermediate steps are deleted!
theorem infinitely_many_primes : ∀ n, ∃ p, prime p ∧ p > n :=
suffices h : ∀ n, n ≥ 2 → ∃ p, prime p ∧ p > n, from sorry,
take n,
assume nge2 : n ≥ 2,
have fact n + 1 ≥ 2, from succ_le_succ (fact_ge_1 n),
match has_prime_divisor _ this with
| ⟨p, primep, pdvd⟩ :=
  have p > n, from lt_of_not_ge
    (suppose p ≤ n,
      have p ≤ fact n, from sorry,
      have p > 0, from lt_of_lt_of_le dec_trivial (ge_2_of_prime primep),
      have p ∣ fact n, from sorry,
      have p ∣ fact n + 1 - fact n, from sorry,
      have p ∣ 1, from sorry,
      have p ≤ 1, from sorry,
      have 2 ≤ 1, from sorry,
      show false, from absurd this dec_trivial),
  ⟨p, primep, this⟩
end
