/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Library.Basic

math2001_init


example {n : ℤ} (hn : 8 ∣ 5 * n) : 8 ∣ n := by
  obtain ⟨a, ha⟩ := hn
  use -3 * a + 2 * n
  calc
    n = -3 * (5 * n) + 16 * n := by ring
    _ = -3 * (8 * a) + 16 * n := by rw [ha]
    _ = 8 * (-3 * a + 2 * n) := by ring


example {n : ℤ} (hn : 8 ∣ 5 * n) : 8 ∣ n := by
  obtain ⟨k, hk⟩ := hn
  use 5*k - 3*n
  calc
    n = 5*(5*n) - 24*n := by ring
    _ = 5*(8*k) - 24*n := by rw[hk]
    _ = 8 * (5*k - 3*n) := by ring

example {n : ℤ} (h1 : 5 ∣ 3 * n) : 5 ∣ n := by
  obtain ⟨k, hk⟩ := h1
  use 2*k - n
  calc
    n = 2*(3*n) - 5*n := by ring
    _ = 2*(5*k) - 5*n := by rw[hk]
    _ = 5 * (2*k - n) := by ring

example {m : ℤ} (h1 : 8 ∣ m) (h2 : 5 ∣ m) : 40 ∣ m := by
  obtain ⟨a, ha⟩ := h1
  obtain ⟨b, hb⟩ := h2
  use -3 * a + 2 * b
  calc
    m = -15 * m + 16 * m := by ring
    _ = -15 * (8 * a) + 16 * m := by rw [ha]
    _ = -15 * (8 * a) + 16 * (5 * b) := by rw [hb]
    _ = 40 * (-3 * a + 2 * b) := by ring

/-! # Exercises -/


example {n : ℤ} (hn : 6 ∣ 11 * n) : 6 ∣ n := by
  obtain ⟨k, hk⟩ := hn
  use 5*k - 9*n
  calc
    n = 5*(11*n) - 54*n := by ring
    _ = 5*(6*k) - 54*n := by rw[hk]
    _= 6*(5*k - 9*n) := by ring

example {a : ℤ} (ha : 7 ∣ 5 * a) : 7 ∣ a := by
  obtain ⟨k, hk⟩ := ha
  use 3*k - 2*a
  calc
    a = 3*(5*a) - 14*a := by ring
    _ = 3*(7*k) - 14*a := by rw[hk]
    _ = 7*(3*k - 2*a) := by ring

example {n : ℤ} (h1 : 7 ∣ n) (h2 : 9 ∣ n) : 63 ∣ n := by
  obtain ⟨k7, hk7⟩ := h1
  obtain ⟨k9, hk9⟩ := h2
  use 4*k9 - 3*k7
  calc
    n = 28*n - 27*n := by ring
    _ = 28 * (9*k9) - 27*n := by rw[hk9]
    _ = 28 * (9*k9) - 27 * (7*k7) := by rw[hk7]
    _ = 63 * (4*k9 - 3*k7) := by ring

example {n : ℤ} (h1 : 5 ∣ n) (h2 : 13 ∣ n) : 65 ∣ n := by
  obtain ⟨k5, hk5⟩ := h1
  obtain ⟨k13, hk13⟩ := h2
  use 2*k5 - 5*k13
  calc
    n = 26*n - 25*n := by ring
    _ = 26*(5*k5) - 25*n := by rw[hk5]
    _ = 26*(5*k5) - 25*(13*k13) := by rw[hk13]
    _ = 65 * (2*k5 - 5*k13) := by ring
