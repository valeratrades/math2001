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
  obtain ⟨a, ha⟩ := h

  have h1: a * t - t < a - 1 := by addarith[ha]
  have h2 :=
  calc
    (a - 1) * (t - 1) = (a*t - t) - (a-1) := by ring
    _ < (a-1) - (a-1) := by rel[h1]
    _ = 0 := by ring

  by_contra ht

  have hbot :=
  calc
    0 > (a - 1) * (t - 1) := by addarith[h2]
    _ = (a - 1) * (1 - 1) := by rw[ht]
    _ = 0 := by ring

  exact lt_irrefl 0 hbot


example {m : ℤ} (h : ∃ a, 2 * a = m) : m ≠ 5 := by
  obtain ⟨a, ha⟩ := h
  match (le_or_succ_le a 2) with
  | Or.inl hale2 =>
    apply ne_of_lt
    calc
      m = 2 * a := by addarith[ha]
      _ <= 2 * 2 := by rel[hale2]
      _ < 5 := by numbers 
  | Or.inr h3lea =>
    apply ne_of_gt
    calc
      m = 2 * a := by addarith[ha]
      _ >= 2 * 3 := by rel[h3lea]
      _ > 5 := by numbers

example {n : ℤ} : ∃ a, 2 * a ^ 3 ≥ n * a + 7 := by
  match (le_or_succ_le n 0) with
  | Or.inl hnle0 =>
    use 2
    calc
      2 * (2^3) = 9 + 0*2 + 7 := by ring
      _ >= 9 + n*2 + 7 := by rel[hnle0]
      _ >= n * 2 + 7 := by norm_num
  | Or.inr h1len =>
    use n*2
    calc
      2 * (n * 2)^3 = 2*n^2*n + 2*n^3 * 7 := by ring
      _ >= 2*n^2*1 + 2*1^3 *7 := by rel[h1len]
      _ = 2*n^2 + 14 := by ring
      _ >= 2*n^2 + 7 := by norm_num
      _ = n * (n*2) + 7 := by ring

example {a b c : ℝ} (ha : a ≤ b + c) (hb : b ≤ a + c) (hc : c ≤ a + b) :
    ∃ x y z, x ≥ 0 ∧ y ≥ 0 ∧ z ≥ 0 ∧ a = y + z ∧ b = x + z ∧ c = x + y := by
  let x := (b + c - a) / 2
  let y := (a + c - b) / 2
  let z := (a + b - c) / 2
  use x, y, z
  -- Prove non-negativity
  have hz : z ≥ 0 := by
    calc
      z = (a + b - c) / 2 := rfl
      _ ≥ 0 := by
        have := add_le_add ha hc
        addarith[hc]
  have hy : y ≥ 0 := by
    calc
      y = (a + c - b) / 2 := rfl
      _ ≥ 0 := by
        have := add_le_add ha hb
        addarith[hb]
  have hx : x ≥ 0 := by
    calc
      x = (b + c - a) / 2 := rfl
      _ ≥ 0 := by
        have := add_le_add hb hc
        addarith[ha]
  -- Prove the equations
  have hc_eq : c = x + y := by
    calc
      c = (b + c - a) / 2 + (a + c - b) / 2 := by ring
      _ = x + y := by rfl
  have hb_eq : b = x + z := by
    calc
      b = (b + c - a) / 2 + (a + b - c) / 2 := by ring
      _ = x + z := by rfl
  have ha_eq : a = y + z := by
    calc
      a = (a + c - b) / 2 + (a + b - c) / 2 := by ring
      _ = y + z := by rfl
  -- Combine results
  exact ⟨hx, hy, hz, ha_eq, hb_eq, hc_eq⟩
