/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init


example {a b : ℝ} (h1 : a - 5 * b = 4) (h2 : b + 2 = 3) : a = 9 := by
  have hb : b = 1 := by addarith [h2]
  calc
    a = a - 5 * b + 5 * b := by ring
    _ = 4 + 5 * 1 := by rw [h1, hb]
    _ = 9 := by ring


example {m n : ℤ} (h1 : m + 3 ≤ 2 * n - 1) (h2 : n ≤ 5) : m ≤ 6 := by
  have h3 :=
  calc
    m + 3 ≤ 2 * n - 1 := by rel [h1]
    _ ≤ 2 * 5 - 1 := by rel [h2]
    _ = 9 := by numbers
  addarith [h3]


example {r s : ℚ} (h1 : s + 3 ≥ r) (h2 : s + r ≤ 3) : r ≤ 3 := by
  have h3 : r ≤ 3 + s := by addarith[h1]
  have h4 : r ≤ 3 - s := by addarith[h2]
  calc
    r = (r + r) / 2 := by ring
    _ ≤ (3 - s + (3 + s)) / 2 := by rel[h3,h4]
    _ = 3 := by ring

example {t : ℝ} (h1 : t ^ 2 = 3 * t) (h2 : t ≥ 1) : t ≥ 2 := by
  have h3 :=
  calc t * t = t ^ 2 := by ring
    _ = 3 * t := by rw [h1]
  cancel t at h3
  addarith [h3]


example {a b : ℝ} (h1 : a ^ 2 = b ^ 2 + 1) (h2 : a ≥ 0) : a ≥ 1 := by
  have h3 :=
  calc
    a ^ 2 = b ^ 2 + 1 := by rw [h1]
    _ ≥ 1 := by extra
    _ = 1 ^ 2 := by ring
  --cancel 2 at h3
  sorry -- not my fault, and also this is likely fine in v4.10 


example {x y : ℤ} (hx : x + 3 ≤ 2) (hy : y + 2 * x ≥ 3) : y > 3 := by
  have hxl: x <= -1 := by addarith[hx]
  calc
    y >= 3 - 2*x := by addarith[hy]
    _ >= 3 - 2*-1 := by rel[hxl]
    _ > 3 := by numbers

example (a b : ℝ) (h1 : -b ≤ a) (h2 : a ≤ b) : a ^ 2 ≤ b ^ 2 := by
  have hp: (b+a) >= 0 := by addarith[h1]
  have hm: (b-a) >= 0 := by addarith[h2]
  calc
    a^2 <= a^2 + (b+a)*(b-a) := by extra
    _ = b ^ 2 := by ring

example (a b : ℝ) (h : a ≤ b) : a ^ 3 ≤ b ^ 3 := by
  have hm: (b-a) >= 0 := by addarith[h]
  calc
    a^3 <= a^3 + (b-a)*((b-a)^2 + 3*(b+a)^2)/4 := by extra
    _ = b^3 := by ring

/-! # Exercises -/


example {x : ℚ} (h1 : x ^ 2 = 4) (h2 : 1 < x) : x = 2 := by
  have hm :=
  calc
    x * x = x^2 := by ring
    _ = 2 * 2 := by addarith[h1]
  --cancel x at hm
  --have hx: x = 2 ∨ x = -2 := by nlinarith[h1]
  sorry

example {n : ℤ} (hn : n ^ 2 + 4 = 4 * n) : n = 2 := by
  have hs :=
  calc
    (n-2)^2 = n^2 +4 -4*n := by ring
    _ = 4*n -4*n := by rw[hn]
    _ = 0 := by ring
  have hz :=
  calc
    (n-2)
    _ = 0 := by exact pow_eq_zero hs
  addarith[hz]

example (x y : ℚ) (h : x * y = 1) (h2 : x ≥ 1) : y ≤ 1 := by
  have hx : x > 0 := by addarith[h2]
  have hy := 
  calc
    y = 1/1 * y := by ring
    _ = x/x * y := by field_simp
    _ = (x*y) / x := by ring
    _  = 1 / x := by rw[h]
  calc
    y = y := by ring
    _ = 1/x := by rw[hy]
    _ <= 1/1 := by rel[h2]
    _ = 1 := by ring
