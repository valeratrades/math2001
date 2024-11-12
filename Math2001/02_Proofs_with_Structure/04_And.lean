/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init


example {x y : ℤ} (h : 2 * x - y = 4 ∧ y - x + 1 = 2) : x = 5 := by
  obtain ⟨h1, h2⟩ := h
  calc
    x = 2 * x - y + (y - x + 1) - 1 := by ring
    _ = 4 + 2 - 1 := by rw [h1, h2]
    _ = 5 := by ring


example {p : ℚ} (hp : p ^ 2 ≤ 8) : p ≥ -5 := by
  have hp' : -3 ≤ p ∧ p ≤ 3
  · apply abs_le_of_sq_le_sq'
    calc
      p ^ 2 ≤ 9 := by addarith[hp]
      _ = 3 ^ 2 := by numbers
    norm_num

  obtain ⟨hm3le, hle3⟩ := hp'
  addarith[hm3le]

example {a b : ℝ} (h1 : a - 5 * b = 4) (h2 : b + 2 = 3) : a = 9 ∧ b = 1 := by
  constructor
  · calc
      a = 4 + 5 * b := by addarith [h1]
      _ = -6 + 5 * (b + 2) := by ring
      _ = -6 + 5 * 3 := by rw [h2]
      _ = 9 := by ring
  · addarith [h2]


example {a b : ℝ} (h1 : a - 5 * b = 4) (h2 : b + 2 = 3) : a = 9 ∧ b = 1 := by
  have hb : b = 1 := by addarith [h2]
  constructor
  · calc
      a = 4 + 5 * b := by addarith [h1]
      _ = 4 + 5 * 1 := by rw [hb]
      _ = 9 := by ring
  · apply hb


example {a b : ℝ} (h1 : a ^ 2 + b ^ 2 = 0) : a = 0 ∧ b = 0 := by
  have has : a ^ 2 = 0
  · apply le_antisymm
    calc
      a ^ 2 ≤ a ^ 2 + b ^ 2 := by extra
      _ = 0 := by rw [h1]
    extra

  have hbs : b ^ 2 = 0
  · apply le_antisymm
    calc
      b ^ 2 ≤ a ^ 2 + b ^ 2 := by extra
      _ = 0 := by rw [h1]
    extra

  constructor
  . apply pow_eq_zero has
  . apply pow_eq_zero hbs

/-! # Exercises -/


example {a b : ℚ} (H : a ≤ 1 ∧ a + b ≤ 3) : 2 * a + b ≤ 4 := by
  obtain ⟨ha1, hapb3⟩ := H
  calc
    2*a + b = a + (a + b) := by ring
    _ <= 1 + 3 := by rel[ha1, hapb3]
    _ = 4 := by ring

example {r s : ℝ} (H : r + s ≤ 1 ∧ r - s ≤ 5) : 2 * r ≤ 6 := by
  obtain ⟨hrps, hrms⟩ := H
  calc
    2 * r = (r+s) + (r-s) := by ring
    _ <= 1 + 5 := by rel[hrps, hrms]
    _ = 6 := by ring

example {m n : ℤ} (H : n ≤ 8 ∧ m + 5 ≤ n) : m ≤ 3 := by
  obtain ⟨hnle8,hmp5⟩ := H
  calc
    m = m + 5 -5 := by ring
    _ <= n -5 := by rel[hmp5]
    _ <= 8 -5 := by rel[hnle8]
    _ = 3 := by ring

example {p : ℤ} (hp : p + 2 ≥ 9) : p ^ 2 ≥ 49 ∧ 7 ≤ p := by
  constructor
  . calc
    p^2 = (p+2-2)^2 := by ring
    _ >= (9-2)^2 := by rel[hp]
    _ = 49 := by ring
  . addarith[hp]

example {a : ℚ} (h : a - 1 ≥ 5) : a ≥ 6 ∧ 3 * a ≥ 10 := by
  have hge6 : a >= 6 := by addarith[h]
  constructor
  . exact hge6
  . calc
    3 * a >= 3 * 6 := by rel[hge6]
    _ >= 10 := by numbers

example {x y : ℚ} (h : x + y = 5 ∧ x + 2 * y = 7) : x = 3 ∧ y = 2 := by
  obtain ⟨hxpy, hxp2y⟩ := h
  have hx :=
  calc
    x = 2*(x+y) - (x + 2*y) := by ring
    _ = 2*5 - 7 := by rw[hxpy, hxp2y]
    _ = 3 := by ring

  constructor
  exact hx
  calc
    y = x + y - x := by ring
    _ = 5 - 3 := by rw[hxpy, hx]
    _ = 2 := by ring

example {a b : ℝ} (h1 : a * b = a) (h2 : a * b = b) :
    (a = 0 ∧ b = 0) ∨ (a = 1 ∧ b = 1) := by
  have ham :=
  calc
    a * (b-1) = a * b - a := by ring
    _ = a - a := by rw[h1]
    _ = 0 := by ring

  match eq_zero_or_eq_zero_of_mul_eq_zero ham with
  | Or.inl ham0 =>
    left
    constructor
    . exact ham0
    . calc
      b = a * b := by addarith[h2]
      _ = 0 * b := by rw[ham0]
      _ = 0 := by ring

  | Or.inr ham1 =>
    right
    have hbe1: b = 1 := by addarith[ham1]
    have hbea:=
      calc
        b = a * b := by addarith[h2]
        _ = a * 1 := by rw[hbe1]
        _ = a := by ring
    constructor
    . calc
      a = b := by addarith[hbea]
      _ = 1 := by rw[hbe1]
    . exact hbe1
