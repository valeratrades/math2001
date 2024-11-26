/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init


example {x y : ℝ} (h : x = 1 ∨ y = -1) : x * y + x = y + 1 := by
  match h with
  | Or.inl hx =>
    calc
    x * y + x = 1 * y + 1 := by rw [hx]
    _ = y + 1 := by ring
  | Or.inr hy =>
    calc
    x * y + x = x * -1 + x := by rw [hy]
    _ = -1 + 1 := by ring
    _ = y + 1 := by rw [hy]

example {n : ℕ} : n ^ 2 ≠ 2 := by
  match (le_or_succ_le n 1) with
  | Or.inl hp =>
    apply ne_of_lt
    calc
      n^2 ≤ 1^2 := by rel[hp]
      _ < 2 := by numbers
  | Or.inr hn =>
    apply ne_of_gt
    calc
      n^2 >= 2^2 := by rel[hn]
      _ > 2 := by numbers

example {x : ℝ} (hx : 2 * x + 1 = 5) : x = 1 ∨ x = 2 := by
  right
  calc
    x = (2 * x + 1 - 1) / 2 := by ring
    _ = (5 - 1) / 2 := by rw [hx]
    _ = 2 := by numbers


example {x : ℝ} (hx : x ^ 2 - 3 * x + 2 = 0) : x = 1 ∨ x = 2 := by
  have h1 :=
    calc
    (x - 1) * (x - 2) = x ^ 2 - 3 * x + 2 := by ring
    _ = 0 := by rw [hx]
  match (eq_zero_or_eq_zero_of_mul_eq_zero h1) with
  | Or.inl hm1 =>
    left
    calc
      x = x - 1 + 1 := by ring
      _ = 0 + 1 := by rw[hm1]
      _ = 1 := by ring
  | Or.inr hm2 =>
    right
    calc
      x = x - 2 + 2 := by ring
      _ = 0 + 2 := by rw[hm2]
      _ = 2 := by ring

example {n : ℤ} : n ^ 2 ≠ 2 := by
  have hn0 := le_or_succ_le n 0
  obtain hn0 | hn0 := hn0
  · have : 0 ≤ -n := by addarith [hn0]
    have hn := le_or_succ_le (-n) 1
    obtain hn | hn := hn
    · apply ne_of_lt
      calc
        n ^ 2 = (-n) ^ 2 := by ring
        _ ≤ 1 ^ 2 := by rel [hn]
        _ < 2 := by numbers
    · apply ne_of_gt
      calc
        (2:ℤ) < 2 ^ 2 := by numbers
        _ ≤ (-n) ^ 2 := by rel [hn]
        _ = n ^ 2 := by ring
  · have hn := le_or_succ_le n 1
    obtain hn | hn := hn
    · apply ne_of_lt
      calc
        n ^ 2 ≤ 1 ^ 2 := by rel [hn]
        _ < 2 := by numbers
    · apply ne_of_gt
      calc
        (2:ℤ) < 2 ^ 2 := by numbers
        _ ≤ n ^ 2 := by rel [hn]


/-! # Exercises -/

example {x : ℚ} (h : x = 4 ∨ x = -4) : x ^ 2 + 1 = 17 := by
  match h with
  | Or.inl hp =>
    calc
      x^2 + 1 = 4^2 + 1 := by rw [hp]
      _ = 17 := by ring
  | Or.inr hn =>
    calc
      x^2 + 1 = (-4)^2 + 1 := by rw [hn]
      _ = 17 := by ring

example {x : ℝ} (h : x = 1 ∨ x = 2) : x ^ 2 - 3 * x + 2 = 0 := by
  match h with
  | Or.inl h1 =>
    calc
      x^2 - 3 * x + 2 = (x - 1) * (x - 2) := by ring
      _ = (1 - 1) * (x - 2) := by rw [h1]
      _ = 0 := by ring
  | Or.inr h2 =>
    calc
      x^2 - 3 * x + 2 = (x - 1) * (x - 2) := by ring
      _ = (x - 1) * (2 - 2) := by rw [h2]
      _ = 0 := by ring

example {t : ℚ} (h : t = -2 ∨ t = 3) : t ^ 2 - t - 6 = 0 := by
   match h with
  | Or.inl hm2 =>
    calc
      t^2 - t - 6 = (-2)^2 - (-2) - 6 := by rw[hm2]
      _ = 0 := by ring
  | Or.inr h3 =>
    calc
      t^2 - t - 6 = (3)^2 - (3) - 6 := by rw[h3]
      _ = 0 := by ring

example {x y : ℝ} (h : x = 2 ∨ y = -2) : x * y + 2 * x = 2 * y + 4 := by
  match h with
  | Or.inl hx2 =>
    calc
      x*y + 2*x = 2*y + 2*2 := by rw[hx2]
      _ = 2*y + 4 := by ring
  | Or.inr hym2 =>
    calc
      x*y + 2*x = x*(-2) + 2*x := by rw[hym2]
      _ = 2*(-2) + 4 := by ring
      _ = 2*y + 4 := by rw[hym2]

example {s t : ℚ} (h : s = 3 - t) : s + t = 3 ∨ s + t = 5 := by
  left
  calc
    s + t = 3 - t + t := by rw[h]
    _ = 3 := by ring

example {a b : ℚ} (h : a + 2 * b < 0) : b < a / 2 ∨ b < - a / 2 := by
  right
  calc
    b = (a + 2*b)/2 - a/2 := by ring
    _ < 0/2 - a/2 := by rel[h]
    _ = -a/2 := by ring

example {x y : ℝ} (h : y = 2 * x + 1) : x < y / 2 ∨ x > y / 2 := by
  left
  calc
    x = (2*x - y)/2 + y/2 := by ring
    _ = (2*x - (2*x + 1))/2 + y/2 := by rw[h]
    _ = y/2 - 1/2 := by ring
    _ < y/2 := by apply sub_lt_self; norm_num

example {x : ℝ} (hx : x ^ 2 + 2 * x - 3 = 0) : x = -3 ∨ x = 1 := by
  have hmul :=
  calc
    (x+3)*(x-1) = x^2 + 2*x -3 := by ring
    _ = 0 := by rw[hx]
  have hz := eq_zero_or_eq_zero_of_mul_eq_zero hmul
  match hz with
  | Or.inl hm3 =>
    left
    addarith[hm3]
  | Or.inr h1 =>
    right
    addarith[h1]

example {a b : ℝ} (hab : a ^ 2 + 2 * b ^ 2 = 3 * a * b) : a = b ∨ a = 2 * b := by
  have h0: a^2 + 2*b^2 - 3*a*b = 0 := by addarith[hab]
  have hmul :=
  calc
    (a-b)*(a-2*b) = a^2 + 2*b^2 - 3*a*b := by ring
    _ = 0 := by rw[h0]
  match eq_zero_or_eq_zero_of_mul_eq_zero hmul with
  | Or.inl hab =>
    left
    addarith[hab]
  | Or.inr ha2b =>
    right
    addarith[ha2b]

example {t : ℝ} (ht : t ^ 3 = t ^ 2) : t = 1 ∨ t = 0 := by
  have hmul :=
  calc
    (t-1) * (t*t) = t^3 - t^2 := by ring
    _ = t^2 - t^2 := by rw[ht]
    _ = 0 := by ring
  match eq_zero_or_eq_zero_of_mul_eq_zero hmul with
  | Or.inl h1 =>
    left
    addarith[h1]
  | Or.inr h0 =>
    right
    exact eq_zero_of_mul_self_eq_zero h0

example {n : ℕ} : n ^ 2 ≠ 7 := by
  match le_or_succ_le n 2 with
  | Or.inl hle2 =>
    apply ne_of_lt
    calc
      n^2 = n * n := by ring
      _ ≤ 2 * 2 := by rel[hle2]
      _ < 7 := by numbers
  | Or.inr hge3 =>
    apply ne_of_gt
    calc
      n^2 = n * n := by ring
      _ ≥ 3 * 3 := by rel[hge3]
      _ > 7 := by numbers

example {x : ℤ} : 2 * x ≠ 3 := by
  match le_or_succ_le x 1 with
  | Or.inl hle1 =>
    apply ne_of_lt
    calc
      2 * x ≤ 2 * 1 := by rel[hle1]
      _ < 3 := by numbers
  | Or.inr hge2 =>
    apply ne_of_gt
    calc
      2 * x ≥ 2 * 2 := by rel[hge2]
      _ > 3 := by numbers

example {t : ℤ} : 5 * t ≠ 18 := by
  match le_or_succ_le t 3 with
  | Or.inl hle3 =>
    apply ne_of_lt
    calc
      5 * t ≤ 5 * 3 := by rel[hle3]
      _ < 18 := by numbers
  | Or.inr hge4 =>
    apply ne_of_gt
    calc
      5 * t ≥ 5 * 4 := by rel[hge4]
      _ > 18 := by numbers

example {m : ℕ} : m ^ 2 + 4 * m ≠ 46 := by
  match le_or_succ_le m 5 with
  | Or.inl hle5 =>
    apply ne_of_lt
    calc
      m^2 + 4 * m = (m^2 + 4 * m + 4) - 4 := by norm_num
      _ = (m + 2)^2 - 4 := by ring
      _ ≤ (5 + 2)^2 - 4 := by rel[hle5]
      _ < 46 := by numbers
  | Or.inr hge6 =>
    apply ne_of_gt
    calc
      m^2 + 4 * m = (m^2 + 4 * m + 4) - 4 := by norm_num
      _ = (m + 2)^2 - 4 := by ring
      _ ≥ (6 + 2)^2 - 4 := by rel[hge6]
      _ > 46 := by numbers
