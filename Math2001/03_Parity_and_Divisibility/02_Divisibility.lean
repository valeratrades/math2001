/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Mathlib.Tactic.GCongr
import Library.Basic

math2001_init


example : (11 : ℕ) ∣ 88 := by
  dsimp [(· ∣ ·)]
  use 8
  numbers


example : (-2 : ℤ) ∣ 6 := by
  dsimp [(. ∣ .)]
  use -3
  numbers

example {a b : ℤ} (hab : a ∣ b) : a ∣ b ^ 2 + 2 * b := by
  obtain ⟨k, hk⟩ := hab
  use k * (a * k + 2)
  calc
    b ^ 2 + 2 * b = (a * k) ^ 2 + 2 * (a * k) := by rw [hk]
    _ = a * (k * (a * k + 2)) := by ring


example {a b c : ℕ} (hab : a ∣ b) (hbc : b ^ 2 ∣ c) : a ^ 2 ∣ c := by
  dsimp[(· ∣ ·)]
  obtain ⟨kab, hab⟩ := hab
  obtain ⟨kbc, hbc⟩ := hbc
  use kab^2 * kbc
  calc
    c = b^2 * kbc := by rw[hbc]
    _ = (a*kab)^2 * kbc := by rw[hab]
    _ = a^2 * (kab^2 * kbc) := by ring

example {x y z : ℕ} (h : x * y ∣ z) : x ∣ z := by
  obtain ⟨kxy, hxy⟩ := h
  use y * kxy
  calc
    z = x * y * kxy := by rw[hxy]
    _ = x * (y * kxy) := by ring

example : ¬((5 : ℤ) ∣ 12) := by
  apply Int.not_dvd_of_exists_lt_and_lt
  use 2
  constructor
  · numbers -- show `5 * 2 < 12`
  · numbers -- show `12 < 5 * (2 + 1)`


example {a b : ℕ} (hb : 0 < b) (hab : a ∣ b) : a ≤ b := by
  obtain ⟨k, hk⟩ := hab
  have H1 :=
    calc
      0 < b := hb
      _ = a * k := hk
  cancel a at H1
  have H : 1 ≤ k := H1
  calc
    a = a * 1 := by ring
    _ ≤ a * k := by rel [H]
    _ = b := by rw [hk]


example {a b : ℕ} (hab : a ∣ b) (hb : 0 < b) : 0 < a := by
  obtain ⟨kab, hab⟩ := hab
  have h0ltak :=
  calc
    0 < b := hb
    _ = a * kab := by rw[hab]
  cancel kab at h0ltak

/-! # Exercises -/


example (t : ℤ) : t ∣ 0 := by
  use 0
  ring

example : ¬(3 : ℤ) ∣ -10 := by
  apply Int.not_dvd_of_exists_lt_and_lt
  use -4
  constructor
  . numbers
  . numbers

example {x y : ℤ} (h : x ∣ y) : x ∣ 3 * y - 4 * y ^ 2 := by
  obtain ⟨kxy, hxy⟩ := h
  use 3*kxy - 4*x*kxy^2
  calc
    3*y - 4*y^2 = 3*(x * kxy) - 4*(x * kxy)^2 := by rw[hxy]
    _ = x * (3*kxy - 4*x*kxy^2) := by ring

example {m n : ℤ} (h : m ∣ n) : m ∣ 2 * n ^ 3 + n := by
  obtain ⟨kmn, hmn⟩ := h
  use 2*m^2*kmn^3 + kmn
  calc
    2*n^3 + n = 2*(m * kmn)^3 + (m * kmn) := by rw[hmn]
    _ = m* (2*m^2*kmn^3 + kmn) := by ring

example {a b : ℤ} (hab : a ∣ b) : a ∣ 2 * b ^ 3 - b ^ 2 + 3 * b := by
  obtain ⟨kab, hab⟩ := hab
  use 2*a^2*kab^3 - a*kab^2 + 3*kab
  calc
    2*b^3 - b^2 + 3*b = 2*(a*kab)^3 - (a*kab)^2 + 3*(a*kab) := by rw[hab]
    _ = a * (2*a^2*kab^3 - a*kab^2 + 3*kab) := by ring

example {k l m : ℤ} (h1 : k ∣ l) (h2 : l ^ 3 ∣ m) : k ^ 3 ∣ m := by
  obtain ⟨kkl, hkl⟩ := h1
  obtain ⟨kl3m, hl3m⟩ := h2
  use kkl^3 * kl3m
  calc
    m = l^3 * kl3m := by rw[hl3m]
    _ = (k * kkl)^3 * kl3m := by rw[hkl]
    _ = k^3 * (kkl^3 * kl3m) := by ring

example {p q r : ℤ} (hpq : p ^ 3 ∣ q) (hqr : q ^ 2 ∣ r) : p ^ 6 ∣ r := by
  obtain ⟨kp3q, hp3q⟩ := hpq
  obtain ⟨kq2r, hq2r⟩ := hqr
  use kp3q^2 * kq2r
  calc
    r = q^2 * kq2r := by rw[hq2r]
    _ = (p^3 * kp3q)^2 * kq2r := by rw[hp3q]
    _ = p^6 * (kp3q^2 * kq2r) := by ring

example : ∃ n : ℕ, 0 < n ∧ 9 ∣ 2 ^ n - 1 := by
  use 6
  constructor
  . numbers
  . use 7
    ring

example : ∃ a b : ℤ, 0 < b ∧ b < a ∧ a - b ∣ a + b := by
  use 2, 1
  constructor
  . numbers
  . constructor
    . numbers
    . use 3
      ring
