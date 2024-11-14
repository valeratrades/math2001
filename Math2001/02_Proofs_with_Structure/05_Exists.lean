/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init


example {a : ℚ} (h : ∃ b : ℚ, a = b ^ 2 + 1) : a > 0 := by
  obtain ⟨b, hb⟩ := h
  calc
    a = b ^ 2 + 1 := hb
    _ > 0 := by extra

example {t : ℝ} (h : ∃ a : ℝ, a * t < 0) : t ≠ 0 := by
  obtain ⟨x, hxt⟩ := h
  have H := le_or_gt x 0
  match H with
  | Or.inl hxle0 =>
    have hxt': 0 < (-x) * t := by addarith[hxt]
    have hx': 0 ≤ -x := by addarith[hxle0]
    cancel -x at hxt'
    apply ne_of_gt
    apply hxt'
  | Or.inr h0ltx =>
    apply ne_of_lt
    have hw :=
    calc
      0 < -x*t := by addarith[hxt]
      _ = x * (-t) := by ring
    have h0lex: 0 <= x := by addarith[h0ltx]
    cancel x at hw
    addarith[hw]

example : ∃ n : ℤ, 12 * n = 84 := by
  use 7
  numbers


example (x : ℝ) : ∃ y : ℝ, y > x := by
  use x + 1
  extra


example : ∃ m n : ℤ, m ^ 2 - n ^ 2 = 11 := by
  use 6, 5
  ring

example (a : ℤ) : ∃ m n : ℤ, m ^ 2 - n ^ 2 = 2 * a + 1 := by
  use a+1, a
  ring

example {p q : ℝ} (h : p < q) : ∃ x, p < x ∧ x < q := by
  use p + (q-p)/2
  have hdp: q - p > 0 := by addarith[h]

  constructor
  . addarith[hdp]
  . calc
    p + (q - p) / 2 = (q+p)/2 := by ring
    _ < (q + q) / 2 := by rel[h]
    _ = q := by ring

example : ∃ a b c d : ℕ,
    a ^ 3 + b ^ 3 = 1729 ∧ c ^ 3 + d ^ 3 = 1729 ∧ a ≠ c ∧ a ≠ d := by
  use 1, 12, 9, 10
  constructor
  numbers

  constructor
  numbers

  constructor
  numbers
  numbers

/-! # Exercises -/


example : ∃ t : ℚ, t ^ 2 = 1.69 := by
  use 1.3
  ring

example : ∃ m n : ℤ, m ^ 2 + n ^ 2 = 85 := by
  use 6, 7
  ring

example : ∃ x : ℝ, x < 0 ∧ x ^ 2 < 1 := by
  use -0.5
  constructor
  . numbers
  . numbers

example : ∃ a b : ℕ, 2 ^ a = 5 * b + 1 := by
  use 4,3
  ring

example (x : ℚ) : ∃ y : ℚ, y ^ 2 > x := by
  use x+1/2
  calc
    (x + 1/2)^2 = x^2 + x + 1/4 := by ring
    _ >= x + 1/4 := by extra
    _ > x := by extra

example {t : ℝ} (h : ∃ a : ℝ, a * t + 1 < a + t) : t ≠ 1 := by
  sorry

example {m : ℤ} (h : ∃ a, 2 * a = m) : m ≠ 5 := by
  sorry

example {n : ℤ} : ∃ a, 2 * a ^ 3 ≥ n * a + 7 := by
  sorry

example {a b c : ℝ} (ha : a ≤ b + c) (hb : b ≤ a + c) (hc : c ≤ a + b) :
    ∃ x y z, x ≥ 0 ∧ y ≥ 0 ∧ z ≥ 0 ∧ a = y + z ∧ b = x + z ∧ c = x + y := by
  sorry
