/- Homework 2 -/

/- Part I: tactic proofs -/

/- Do five propositional logic proofs and three quantifier proofs, following the
   same constraints as on the last assignment, but this time using tactics.
   (You can prove the same theorems as on the last assignment!)
-/

section
  open classical

  variables p q r s : Prop

  -- commutativity of ∧ and ∨
  example : p ∧ q ↔ q ∧ p := 
  begin
    apply iff.intro,
    intro h,
      apply and.intro,
        exact (and.elim_right h), 
        exact (and.elim_left h),
    intro h,
      apply and.intro,
        exact (and.elim_right h), 
        exact (and.elim_left h),
  end

  example : p ∨ q ↔ q ∨ p :=
  begin
    apply iff.intro,
    intro h,
      apply or.elim h,
        intro hp,
        exact or.inr hp,
        intro hq,
        exact or.inl hq,
    intro h,
      apply or.elim h,
        intro hp,
        exact or.inr hp,
        intro hq,
        exact or.inl hq,
  end

  -- associativity of ∧ and ∨
  example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) :=
   begin
    apply iff.intro,
    intro h,
      apply and.intro, 
        exact (and.elim_left (and.elim_left h)),
        apply and.intro,
          exact (and.elim_right (and.elim_left h)),
          exact (and.elim_right h),
    intro h,
      apply and.intro,
        apply and.intro,
          exact and.elim_left h,
          exact and.elim_left (and.elim_right h),
        exact and.elim_right (and.elim_right h)
  end


  example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) :=
  begin
    apply iff.intro,
    intro h,
      apply or.elim h,
        intro hpq,
        apply or.elim hpq,
          intro hp,
            exact or.inl hp,
          intro hq,
            exact or.inr (or.inl hq),
        intro hr,
          exact or.inr (or.inr hr),
    intro h,
      apply or.elim h,
        intro hp,
          exact or.inl (or.inl hp),
        intro hqr,
        apply or.elim hqr,
          intro hq,
            exact or.inl (or.inr hq),
          intro hr,
            exact or.inr hr
  end

  -- distributivity
  -- this next one is in *Theorem Proving in Lean*
  -- example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := sorry
  example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) :=
  begin
    apply iff.intro,
      intro h,
        apply or.elim h,
        intro hp,
          exact and.intro (or.inl hp) (or.inl hp),
        intro hqr,
          exact and.intro (or.inr (and.elim_left hqr)) 
                          (or.inr (and.elim_right hqr)),
      intro h,
        apply or.elim (and.elim_left h),
        intro hp,
          exact or.inl hp,
        intro hq,
          apply or.elim (and.elim_right h),
          intro hp,
            exact or.inl hp,
          intro hr,
            exact or.inr (and.intro hq hr)  
  end

  example : (p → q) → (¬p ∨ q) := 
  begin
    intro h,
    apply or.elim (em p),
    intro hp,
      apply or.inr,
      exact h hp,
    intro hnp,
      apply or.inl,
      exact hnp
  end

  example : ¬(p ↔ ¬p) :=
  begin
    intro h,
    apply false.elim,
      apply iff.elim_left,
        apply iff_false_intro,
        exact (assume K: p, have K1: ¬p, from (iff.elim_left h) K, show false, from K1 K),
      exact (iff.elim_right h) (assume K: p, have K1: ¬p, from (iff.elim_left h) K, show false, from K1 K)
  end

end

section

  open classical

  variable  α : Type
  variables (p q : α → Prop) (r : Prop)
  variable  a : α

  example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) :=
  begin
    apply iff.intro,
    intro h,
      apply and.intro,
      intro x,
        exact (and.elim_left (h x)),
      intro x,
        exact (and.elim_right (h x)),
    intro h,
      intro x,
      apply and.intro,
      exact ((and.elim_left h) x),
      exact ((and.elim_right h) x)
  end

  example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) :=
  begin
    intro h,
    intro h2,
    intro x,
    exact ((h x) (h2 x))
  end

  example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x := 
  begin 
    intro h,
    intro x,
      apply or.elim h,
      intro hp,
        exact or.inl (hp x),
      intro hq,
        exact or.inr (hq x),
  end

  example : (∃ x : α, r) → r :=
  begin
    intro h,
    cases h with x r,
    exact r
  end

  example (c : α) : r → (∃ {x : α}, r) := 
  begin
    intro h,
    apply exists.intro,
      exact c,    -- I don't understand why a wouldn't work here
      exact h
  end

  example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r := 
  begin
    apply iff.intro,
    intro h,
      cases h with x px,
      apply and.intro,
        constructor, exact (and.elim_left px),
        exact (and.elim_right px),
    intro h,
      cases h with px r,
        cases px with x p_x,
        constructor, exact (and.intro p_x r)
  end
 
  example : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) := 
  begin
    apply iff.intro,
    intro h,
      apply by_contradiction,
      intro hnp,
      exact (h (take z,
                  show p z, from 
                  by_contradiction 
                  (assume H₂: ¬ p z,
                  have H₃: ∃ x, ¬ p x, from exists.intro z H₂,
                  show false, from hnp H₃))),
    intro h,
    cases h with x npx,
      intro h_to_contradict,
      exact npx (h_to_contradict x)
  end
  
  end


/- Part II: calculations -/

/- The Lean 3 library does not yet have the real numbers. We can fake it with the declarations
   below. -/
section
  variables (real : Type) [ordered_ring real]
  variables (log exp : real → real)
  premise   log_exp_eq : ∀ x, log (exp x) = x
  premise   exp_log_eq : ∀ {x}, x > 0 → exp (log x) = x
  premise   exp_pos    : ∀ x, exp x > 0
  premise   exp_add    : ∀ x y, exp (x + y) = exp x * exp y

  -- this ensures the assumptions are available in tactic proofs
  include log_exp_eq exp_log_eq exp_pos exp_add

  example (x y z : real) : exp (x + y + z) = exp x * exp y * exp z :=
  by rw [exp_add, exp_add]

  example (y : real) (h : y > 0)  : exp (log y) = y := exp_log_eq h

  /- Prove the folowing theorem, using the facts above. -/
  --theorem 
  theorem log_mul {x y : real} (hx : x > 0) (hy : y > 0) : log (x * y) = log x + log y :=
  have H1: exp (log (x * y)) = exp (log x + log y), from 
  (calc
      exp (log (x * y)) = x * y                      : by rw exp_log_eq (mul_pos hx hy)
      ...               = exp (log x) * y            : by rw exp_log_eq (hx)
      ...               = exp (log x) * exp (log y)  : by rw exp_log_eq hy
      ...               = exp (log x + log y)        : by rw exp_add),
  show log (x * y) = log x + log y, from
  (calc
      log (x * y) = log (exp (log(x * y)))           : by rw log_exp_eq
      ...         = log (exp (log x + log y))        : by rw H1
      ...         = log x + log y                    : by rw log_exp_eq
  )
end

/- The following command lets you see the ring axioms in Lean. (We will discuss this when
   we talk about structures.) -/

print fields ring

/- Note that the properties left_distrib and right_distrib are also called mul_add and add_mul,
   respectively. Since x - y is defined to be x + -y, the library proves "sub_self" as follows.
-/

namespace hide

theorem sub_self {α : Type} [ring α] (x : α) : x - x = 0 := add_right_neg x

end hide

/- Similarly, we have mul_sub and sub_mul. The following is a consequence of the ring axioms,
   and can be proved using only a short calculation, using sub_self and mul_sub. Do it!
   Hint: consider x * (1 - 1). -/

example {α : Type} [ring α] (x : α) (h1: 0 = 1 - 1) : x * 0 = 0 :=
calc
  x * 0 = x * (1 - 1)       : by rw [sub_self]
  ...   = (x * 1) - (x * 1) : by rw mul_sub 
  ...   = x - x             : by rw mul_one
  ...   = 0                 : by rw (sub_self x)

/- Part III: inductive definitions -/

open list
variable {α : Type}

/- In the Lean 3 library, the function "concat", which appends an element to the end of a list,
   is defined as follows. -/

namespace hide

def concat : list α → α → list α
| []     a := [a]
| (b::l) a := b :: concat l a

end hide

/- For the next exercise, we will use the following "home-grown" version. Make sure you
   understand how it works. -/

def conc (l : list α) (a : α) : list α :=
list.rec_on l
  [a]
  (λ b l recval, b :: recval)

theorem conc_nil  (a : α) : conc nil a = [a] := rfl
theorem conc_cons (b : α) (l : list α) (a : α) : conc (b :: l) a = b :: conc l a := rfl

vm_eval conc [1, 2, 3] 4

/- We will also use the length function. -/

check conc_cons

check length_nil
check length_cons

example : length [1, 2, 3] = 3 := by refl
example (a : α) (l : list α) : length (a :: l) = length l + 1 := rfl

vm_eval length [1, 2, 3, 4, 5]

/- The following is an example of a proof by induction using these two notions. -/

theorem length_conc (a : α) (l : list α) : length (conc l a) = length l + 1 :=
list.induction_on l
  rfl
  (take b l',
    assume ih : length (conc l' a) = length l' + 1,
    show length (conc (b::l') a) = length (b::l') + 1, from
      calc
        length (conc (b::l') a) = length (b :: (conc l' a)) : rfl
                            ... = length (conc l' a) + 1     : rfl
                            ... = length l' + 1 + 1          : by rw ih
                            ... = length (b::l') + 1         : rfl)

/- Here is a shorter proof. -/

theorem length_conc' (a : α) (l : list α) : length (conc l a) = length l + 1 :=
list.induction_on l rfl (λ b l' ih, by simp [length, conc_cons, ih])

/- Let us define a "list reverse" function and check that it works. -/

def rev (l : list α) : list α :=
list.rec_on l
  []
  (λ b l recval, conc recval b)

theorem rev_nil : rev ([] : list α) = [] := rfl
theorem rev_cons (a : α) (l : list α) : rev (a :: l) = conc (rev l) a := rfl

vm_eval rev [1, 2, 3, 4, 5]

/- Prove the following. -/

theorem length_rev (l : list α) : length (rev l) = length l :=
list.induction_on l
  rfl
  (take b l',
   assume ih: length (rev l') = length l',
   show length (rev (b::l')) = length (b::l'), from 
    calc
      length (rev (b::l')) = length (conc (rev (l')) b) : rfl
      ...                  = length (rev l') + 1    : by rw length_conc
      ...                  = length l' + 1          : by rw ih
      ...                  = length (b::l')         : rfl
  )