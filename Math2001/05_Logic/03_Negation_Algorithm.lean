/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Tactic.Rel
import Library.Tactic.ModEq

math2001_init
set_option pp.funBinderTypes true


example (P Q : Prop) : ¬ (P ∧ Q) ↔ (¬ P ∨ ¬ Q) := by
  constructor
  · intro h
    by_cases hP : P
    · right
      intro hQ
      have hPQ : P ∧ Q := by {
        constructor
        · apply hP
        · apply hQ
      }
      contradiction
    · left
      apply hP
  · intro H
    cases H with
    | inl hnp =>
      intro hpaq
      have: P := hpaq.1
      contradiction
    | inr hnq =>
      intro hpaq
      have: Q := hpaq.2
      contradiction

example :
    ¬(∀ m : ℤ, m ≠ 2 → ∃ n : ℤ, n ^ 2 = m) ↔ ∃ m : ℤ, m ≠ 2 ∧ ∀ n : ℤ, n ^ 2 ≠ m :=
  calc ¬(∀ m : ℤ, m ≠ 2 → ∃ n : ℤ, n ^ 2 = m)
      ↔ ∃ m : ℤ, ¬(m ≠ 2 → ∃ n : ℤ, n ^ 2 = m) := by rel [not_forall]
    _ ↔ ∃ m : ℤ, m ≠ 2 ∧ ¬(∃ n : ℤ, n ^ 2 = m) := by rel [not_imp]
    _ ↔ ∃ m : ℤ, m ≠ 2 ∧ ∀ n : ℤ, n ^ 2 ≠ m := by rel [not_exists]


example : ¬(∀ n : ℤ, ∃ m : ℤ, n ^ 2 < m ∧ m < (n + 1) ^ 2)
    ↔ ∃ n : ℤ, ∀ m : ℤ, n ^ 2 ≥ m ∨ m ≥ (n + 1) ^ 2 := by {
    calc
      ¬(∀ n : ℤ, ∃ m : ℤ, n ^ 2 < m ∧ m < (n + 1) ^ 2)
      ↔ ∃ n: ℤ, ¬(∃ m : ℤ, n ^ 2 < m ∧ m < (n + 1) ^ 2) := by rel[not_forall]
    _ ↔ ∃ n: ℤ, ∀ m: ℤ, ¬(n^2 < m ∧ m < (n + 1) ^ 2) := by rel[not_exists]
    _ ↔ ∃ n: ℤ, ∀ m: ℤ, ¬(n^2 < m) ∨ ¬(m < (n + 1) ^ 2) := by rel[not_and_or]
    _ ↔ ∃ n : ℤ, ∀ m : ℤ, n ^ 2 ≥ m ∨ m ≥ (n + 1)^2 := by norm_num
}

#push_neg ¬(∀ m : ℤ, m ≠ 2 → ∃ n : ℤ, n ^ 2 = m)
  -- ∃ m : ℤ, m ≠ 2 ∧ ∀ (n : ℤ), n ^ 2 ≠ m

#push_neg ¬(∀ n : ℤ, ∃ m : ℤ, n ^ 2 < m ∧ m < (n + 1) ^ 2)
  -- ∃ n : ℤ, ∀ m : ℤ, m ≤ n ^ 2 ∨ (n + 1) ^ 2 ≤ m


#push_neg ¬(∃ m n : ℤ, ∀ t : ℝ, m < t ∧ t < n)
#push_neg ¬(∀ a : ℕ, ∃ x y : ℕ, x * y ∣ a → x ∣ a ∧ y ∣ a)
#push_neg ¬(∀ m : ℤ, m ≠ 2 → ∃ n : ℤ, n ^ 2 = m)


example : ¬ (∃ n : ℕ, n ^ 2 = 2) := by
  push_neg
  intro n
  have hn := le_or_succ_le n 1
  obtain hn | hn := hn
  · apply ne_of_lt
    calc
      n ^ 2 ≤ 1 ^ 2 := by rel [hn]
      _ < 2 := by numbers
  · apply ne_of_gt
    calc
      n^2 >= 2^2 := by rel[hn]
      _ > 2 := by norm_num

/-! # Exercises -/


example (P : Prop) : ¬ (¬ P) ↔ P := by
  constructor
  . intro hnnp
    by_cases hp: P
    . exact hp
    . contradiction
  . intro hp
    intro hcontr
    contradiction

example (P Q : Prop) : ¬ (P → Q) ↔ (P ∧ ¬ Q) := by
  constructor
  . intro h
    constructor
    . by_cases hp: P
      . exact hp
      . have: P → Q := by {
          intro h
          contradiction
        }
        contradiction
    . intro hq
      have: P → Q := by {
        intro _
        exact hq
      }
      contradiction
  . intro h
    intro hptq
    have hp: P := h.1
    have hq: Q := hptq h.1
    have hnq: ¬Q := h.2
    contradiction

example (P : α → Prop) : ¬ (∀ x, P x) ↔ ∃ x, ¬ P x := by
  constructor
  . intro h
    by_cases henp: ∃ (x : α), ¬P x
    . exact henp
    .
      have: ∀ (x: α), P x := by {
        intro x
        by_cases hp: P x
        . exact hp
        . 
          have h : ∃ (x : α), ¬P x := ⟨x, hp⟩ -- get exists statement by providing a `witness`
          contradiction
      }
      contradiction
  . intro ⟨x, hx⟩
    intro hf
    have:= hf x
    contradiction

example : (¬ ∀ a b : ℤ, a * b = 1 → a = 1 ∨ b = 1)
    ↔ ∃ a b : ℤ, a * b = 1 ∧ a ≠ 1 ∧ b ≠ 1 := by {
  calc
    (¬ ∀ a b: ℤ, a * b = 1 → a = 1 ∨ b = 1)
    _ ↔ (∃ (x : ℤ), ¬∀ (b : ℤ), x * b = 1 → x = 1 ∨ b = 1) := by rel[not_forall]
    _ ↔ ∃ (a b: ℤ), ¬(a * b = 1 → a = 1 ∨ b = 1) := by rel[not_forall]
    _ ↔ ∃ (a b: ℤ), a * b = 1 ∧  ¬(a = 1 ∨ b = 1) := by rel[not_imp]
    _ ↔ ∃ (a b: ℤ), a * b = 1 ∧  ¬(a = 1) ∧ ¬(b = 1) := by rel[not_or]
    _ ↔ ∃ a b: ℤ, a * b = 1 ∧ a ≠ 1 ∧ b ≠ 1 := by norm_num
}

example : (¬ ∃ x : ℝ, ∀ y : ℝ, y ≤ x) ↔ (∀ x : ℝ, ∃ y : ℝ, y > x) :=
  calc
    (¬ ∃ x : ℝ, ∀ y : ℝ, y ≤ x)
    _ ↔ ∀ x : ℝ, ¬(∀ y : ℝ, y ≤ x) := by rel[not_exists]
    _ ↔ ∀ x : ℝ, ∃ y : ℝ, ¬(y ≤ x) := by rel[not_forall]
    _ ↔ (∀ x : ℝ, ∃ y : ℝ, y > x) := by norm_num
  
example : ¬ (∃ m : ℤ, ∀ n : ℤ, m = n + 5) ↔ ∀ m : ℤ, ∃ n : ℤ, m ≠ n + 5 :=
  calc
    ¬(∃ m : ℤ, ∀ n : ℤ, m = n + 5)
    _ ↔ ∀ m : ℤ, ¬(∀ n : ℤ, m = n + 5) := by rel[not_exists]
    _ ↔ ∀ m : ℤ, ∃ n : ℤ, ¬(m = n + 5) := by rel[not_forall]
    _ ↔ ∀ m : ℤ, ∃ n : ℤ, m ≠ n + 5 := by norm_num

#push_neg ¬(∀ n : ℕ, n > 0 → ∃ k l : ℕ, k < n ∧ l < n ∧ k ≠ l)
#push_neg ¬(∀ m : ℤ, m ≠ 2 → ∃ n : ℤ, n ^ 2 = m)
#push_neg ¬(∃ x : ℝ, ∀ y : ℝ, ∃ m : ℤ, x < y * m ∧ y * m < m)
#push_neg ¬(∃ x : ℝ, ∀ q : ℝ, q > x → ∃ m : ℕ, q ^ m > x)


example : ¬ (∀ x : ℝ, x ^ 2 ≥ x) := by
  push_neg
  use 0.5
  norm_num

example : ¬ (∃ t : ℝ, t ≤ 4 ∧ t ≥ 5) := by
  push_neg
  intro t
  cases (lt_or_ge t 4.5) with
  | inl hlt4 =>
    right
    calc
      t < 4.5 := hlt4
      _ < 5 := by norm_num
  | inr hge4 =>
    left
    calc
      4 < 4.5 := by norm_num
      _ <= t := by rel[hge4]


example : ¬ Int.Even 7 := by
  dsimp [Int.Even]
  push_neg
  intro h
  intro hf

  have:=
  calc
    1 = 7 - 6 := by ring
    _ = 2*h - 6 := by rw[hf]
    _ = 2*(h - 3) := by ring
    _ ≡ 0 [ZMOD 2] := by extra
  numbers at this

example {p : ℕ} (k : ℕ) (hk1 : k ≠ 1) (hkp : k ≠ p) (hk : k ∣ p) : ¬ Prime p := by
  dsimp [Prime]
  push_neg
  right
  use k
  exact ⟨hk, ⟨hk1, hkp⟩⟩

example : ¬ ∃ a : ℤ, ∀ n : ℤ, 2 * a ^ 3 ≥ n * a + 7 := by
  push_neg
  intro a
  use 2*a^2
  norm_num
  calc
    2*a^3 = 2*a^2 * a := by ring
    _ < 2*a^2 * a + 7 := by norm_num


example {p : ℕ} (hp : ¬ Prime p) (hp2 : 2 ≤ p) : ∃ m, 2 ≤ m ∧ m < p ∧ m ∣ p := by
  have H : ¬ (∀ (m : ℕ), 2 ≤ m → m < p → ¬m ∣ p) := by {
    intro H
    push_neg at hp
    have hcond: ∀ (m : ℕ), 1 < m → m < p → ¬m ∣ p := fun m h1m hmp => H m (Nat.succ_le_iff.mpr h1m) hmp
    have:= prime_test hp2 hcond
    contradiction
  }

  push_neg at H; exact H
