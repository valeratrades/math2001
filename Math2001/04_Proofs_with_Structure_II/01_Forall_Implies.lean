/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init


example {a : ℝ} (h : ∀ x, a ≤ x ^ 2 - 2 * x) : a ≤ -1 :=
  calc
    a ≤ 1 ^ 2 - 2 * 1 := by apply h
    _ = -1 := by numbers


example {n : ℕ} (hn : ∀ m, n ∣ m) : n = 1 := by
  have h1 : n ∣ 1 := by apply hn
  have h2 : 0 < 1 := by numbers
  apply le_antisymm
  · apply Nat.le_of_dvd h2 h1
  · apply Nat.pos_of_dvd_of_pos h1 h2


example {a b : ℝ} (h : ∀ x, x ≥ a ∨ x ≤ b) : a ≤ b := by
  have h1: (a+b)/2 >= a ∨ (a+b)/2 <= b := by apply h
  match h1 with
  | Or.inr hleb =>
    calc
      a = 2*((a+b)/2) - b := by ring
      _ <= 2*b - b := by rel[hleb]
      _ = b := by ring
  | Or.inl hgea =>
    calc
      b = 2*((a+b)/2) - a := by ring
      _ >= 2*a - a := by rel[hgea]
      _ = a := by ring

example {a b : ℝ} (ha1 : a ^ 2 ≤ 2) (hb1 : b ^ 2 ≤ 2) (ha2 : ∀ y, y ^ 2 ≤ 2 → y ≤ a)
    (hb2 : ∀ y, y ^ 2 ≤ 2 → y ≤ b) :
    a = b := by
  apply le_antisymm
  · apply hb2
    apply ha1
  · apply ha2
    apply hb1

example : ∃ b : ℝ, ∀ x : ℝ, b ≤ x ^ 2 - 2 * x := by
  use -1
  intro x
  calc
    -1 ≤ -1 + (x - 1) ^ 2 := by extra
    _ = x ^ 2 - 2 * x := by ring


example :∃ c : ℝ, ∀ x y, x ^ 2 + y ^ 2 ≤ 4 → x + y ≥ c := by {
  use -3
  intro x y hxy

  have hp' : -3 ≤ x + y ∧ x + y ≤ 3
  apply abs_le_of_sq_le_sq'
  . calc
    (x+y)^2 <= (x+y)^2 + (x-y)^2 := by extra
    _ = 2*(x^2+y^2) := by ring
    _ <= 2*4 := by rel[hxy]
    _ <= 3^2 := by numbers
  . numbers
  . addarith[hp'.1]
}

example : forall_sufficiently_large n : ℤ, n ^ 3 ≥ 4 * n ^ 2 + 7 := by
  dsimp
  use 5
  intro n hn
  calc
    n ^ 3 = n * n ^ 2 := by ring
    _ ≥ 5 * n ^ 2 := by rel [hn]
    _ = 4 * n ^ 2 + n ^ 2 := by ring
    _ ≥ 4 * n ^ 2 + 5 ^ 2 := by rel [hn]
    _ = 4 * n ^ 2 + 7 + 18 := by ring
    _ ≥ 4 * n ^ 2 + 7 := by extra


example : Prime 2 := by
  constructor
  · numbers -- show `2 ≤ 2`
  intro m hmp
  have hp : 0 < 2 := by numbers
  have hmp_le : m ≤ 2 := Nat.le_of_dvd hp hmp
  have h1m : 1 ≤ m := Nat.pos_of_dvd_of_pos hmp hp
  interval_cases m
  · left
    numbers -- show `1 = 1`
  · right
    numbers -- show `2 = 2`


example : ¬ Prime 6 := by
  apply not_prime 2 3
  · numbers -- show `2 ≠ 1`
  · numbers -- show `2 ≠ 6`
  · numbers -- show `6 = 2 * 3`

/-! # Exercises -/


example {a : ℚ} (h : ∀ b : ℚ, a ≥ -3 + 4 * b - b ^ 2) : a ≥ 1 :=
  calc
    a >= -3 + 4*2 - 2^2 := by apply h
    _ = 1 := by ring

example {n : ℤ} (hn : ∀ m, 1 ≤ m → m ≤ 5 → m ∣ n) : 15 ∣ n := by
  have h5d: 5 ∣ n := by {
    apply hn
    . numbers
    . numbers
  }
  obtain ⟨k5, h5⟩ := h5d
  have h3d: 3 ∣ n := by {
    apply hn
    . numbers
    . numbers
  }
  obtain ⟨k3, h3⟩ := h3d
  use 2*k3 - 3*k5
  calc
    n = 10*n - 9*n := by ring
    _ = 10*(3*k3) - 9*n := by rw[h3]
    _ = 10*(3*k3) - 9*(5*k5) := by rw[h5]
    _ = 15 * (2*k3 - 3*k5) := by ring

example : ∃ n : ℕ, ∀ m : ℕ, n ≤ m := by
  use 0
  exact fun m ↦ Nat.zero_le m

example : ∃ a : ℝ, ∀ b : ℝ, ∃ c : ℝ, a + b < c := by
  use 0
  intro b
  use b + 1
  norm_num

example : forall_sufficiently_large x : ℝ, x ^ 3 + 3 * x ≥ 7 * x ^ 2 + 12 := by
  use 7
  intro x hx
  calc
    x^3 + 3*x = x * x^2 + 3*x := by ring
    _ >= 7 * x^2 + 3*7 := by rel[hx]
    _ = 7*x^2 + 12 + 9 := by ring
    _ >= 7*x^2 + 12 := by extra

example : ¬(Prime 45) := by
  apply not_prime 5 9
  . numbers
  . numbers
  . numbers
