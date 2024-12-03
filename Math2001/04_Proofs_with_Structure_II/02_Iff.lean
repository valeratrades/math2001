/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Tactic.ModEq

math2001_init

namespace Int


example {a : ℚ} : 3 * a + 1 ≤ 7 ↔ a ≤ 2 := by
  constructor
  · intro h
    calc a = ((3 * a + 1) - 1) / 3 := by ring
      _ ≤ (7 - 1) / 3 := by rel [h]
      _ = 2 := by numbers
  · intro h
    calc 3 * a + 1 ≤ 3 * 2 + 1 := by rel [h]
      _ = 7 := by numbers


example {n : ℤ} : 8 ∣ 5 * n ↔ 8 ∣ n := by
  constructor
  · intro hn
    obtain ⟨a, ha⟩ := hn
    use -3 * a + 2 * n
    calc
      n = -3 * (5 * n) + 16 * n := by ring
      _ = -3 * (8 * a) + 16 * n := by rw [ha]
      _ = 8 * (-3 * a + 2 * n) := by ring
  · intro hn
    obtain ⟨a, ha⟩ := hn
    use 5 * a
    calc 5 * n = 5 * (8 * a) := by rw [ha]
      _ = 8 * (5 * a) := by ring


theorem odd_iff_modEq (n : ℤ) : Odd n ↔ n ≡ 1 [ZMOD 2] := by
  constructor
  · intro h
    obtain ⟨k, hk⟩ := h
    dsimp [Int.ModEq]
    dsimp [(· ∣ ·)]
    use k
    addarith [hk]
  · intro h
    obtain ⟨k, hk⟩ := h
    dsimp [Int.Odd]
    use k
    addarith[hk]

theorem even_iff_modEq (n : ℤ) : Even n ↔ n ≡ 0 [ZMOD 2] := by
  constructor
  · intro ⟨k, hk⟩
    dsimp [Int.ModEq]
    dsimp [(· ∣ ·)]
    use k
    addarith [hk]
  · intro ⟨k, hk⟩
    use k
    addarith[hk]

example {x : ℝ} : x ^ 2 + x - 6 = 0 ↔ x = -3 ∨ x = 2 := by
  constructor
  . intro h
    have hmul :=
    calc
      (x+3)*(x-2) = x^2 + x - 6 := by ring
      _ = 0 := by rw[h]
    rw[mul_eq_zero] at hmul
    match hmul with
    | Or.inl hm3 =>
      left
      addarith[hm3]
    | Or.inr h2 =>
      right
      addarith[h2]
  . intro h
    match h with
    | Or.inl hm3 =>
      calc
        x^2 + x - 6 = (-3)^2 + -3 - 6 := by rw[hm3]
        _ = 0 := by ring
    | Or.inr h2 => 
      calc
        x^2 + x - 6 = (2)^2 + 2 - 6 := by rw[h2]
        _ = 0 := by ring

example {a : ℤ} : a ^ 2 - 5 * a + 5 ≤ -1 ↔ a = 2 ∨ a = 3 := by {
  constructor
  . intro hf
    have hmul :=
    calc
      (2*a - 5)^2 = 4*(a^2 - 5*a + 5) + 5 := by ring
      _ <= 4*(-1) + 5 := by rel[hf]
      _ = 1^2 := by ring
    apply abs_le_of_sq_le_sq' at hmul
    have hbound := hmul (by numbers)
    match (le_or_gt a 2) with
    | Or.inl ha_le =>
      left
      apply le_antisymm
      . exact ha_le
      . have hm2:=
        calc
          2*a = 2*a - 5 + 5 := by ring
          _ >= (-1) + 5 := by rel[hbound.1]
          _ = 2*2 := by ring
        cancel 2 at hm2
    | Or.inr ha_gt =>
      right
      apply le_antisymm
      . have hm2:=
        calc
          2*a = 2*a - 5 + 5 := by ring
          _ <= 1 + 5 := by rel[hbound.2]
          _ = 2*3 := by ring
        cancel 2 at hm2
      . addarith[ha_gt]
  . intro hb
    match hb with
    | Or.inl he2 =>
      calc
        a^2 - 5*a + 5 = 2^2 - 5*2 + 5 := by rw[he2]
        _ <= -1 := by numbers
    | Or.inr he3 =>
      calc
        a^2 - 5*a + 5 = 3^2 - 5*3 + 5 := by rw[he3]
        _ <= -1 := by numbers
}

example {n : ℤ} (hn : n ^ 2 - 10 * n + 24 = 0) : Even n := by
  have hn1 :=
    calc (n - 4) * (n - 6) = n ^ 2 - 10 * n + 24 := by ring
      _ = 0 := hn
  match (eq_zero_or_eq_zero_of_mul_eq_zero hn1) with
  | Or.inl h4 =>
    use 2
    calc
      n = 4 := by addarith[h4]
      _ = 2*2 := by ring
  | Or.inr h6 =>
    use 3
    calc
      n = 6 := by addarith[h6]
      _ = 2*3 := by ring

example {n : ℤ} (hn : n ^ 2 - 10 * n + 24 = 0) : Even n := by
  have hn1 :=
    calc (n - 4) * (n - 6) = n ^ 2 - 10 * n + 24 := by ring
      _ = 0 := hn
  rw [mul_eq_zero] at hn1 -- `hn1 : n - 4 = 0 ∨ n - 6 = 0`
  match hn1 with
  | Or.inl h4 =>
    use 2
    calc
      n = 4 := by addarith[h4]
      _ = 2*2 := by ring
  | Or.inr h6 =>
    use 3
    calc
      n = 6 := by addarith[h6]
      _ = 2*3 := by ring

example {x y : ℤ} (hx : Odd x) (hy : Odd y) : Odd (x + y + 1) := by
  rw [Int.odd_iff_modEq] at *
  calc x + y + 1 ≡ 1 + 1 + 1 [ZMOD 2] := by rel [hx, hy]
    _ = 2 * 1 + 1 := by ring
    _ ≡ 1 [ZMOD 2] := by extra


example (n : ℤ) : Even n ∨ Odd n := by
  mod_cases hn : n % 2
  · left
    rw [Int.even_iff_modEq]
    apply hn
  · right
    rw [Int.odd_iff_modEq]
    apply hn

/-! # Exercises -/


example {x : ℝ} : 2 * x - 1 = 11 ↔ x = 6 := by
  constructor
  . intro hx
    calc
    x = (2*x - 1)/2 + 1/2 := by ring
    _ = 11/2 + 1/2 := by rw[hx]
    _ = 6 := by ring
  . intro h6
    calc
      2*x - 1 = 2*6 - 1 := by rw[h6]
      _ = 11 := by ring

lemma d7d9 {n : ℤ} (h1 : 7 ∣ n) (h2 : 9 ∣ n) : 63 ∣ n := by
  obtain ⟨k7, hk7⟩ := h1
  obtain ⟨k9, hk9⟩ := h2
  use 4*k9 - 3*k7
  calc
    n = 28*n - 27*n := by ring
    _ = 28 * (9*k9) - 27*n := by rw[hk9]
    _ = 28 * (9*k9) - 27 * (7*k7) := by rw[hk7]
    _ = 63 * (4*k9 - 3*k7) := by ring


example {n : ℤ} : 63 ∣ n ↔ 7 ∣ n ∧ 9 ∣ n := by
  dsimp[(· ∣ ·)]
  constructor
  . intro h
    constructor
    . obtain ⟨k, hk⟩ := h
      use 9*k
      calc
        n = 63 * k := by rw[hk]
        _ = 7 * (9 * k) := by ring
    . obtain ⟨k, hk⟩ := h
      use 7*k
      calc
        n = 63 * k := by rw[hk]
        _ = 9 * (7*k) := by ring
  . intro ⟨h7, h9⟩
    exact d7d9 h7 h9

theorem dvd_iff_modEq {a n : ℤ} : n ∣ a ↔ a ≡ 0 [ZMOD n] := by
  constructor
  . intro ⟨k, hk⟩
    calc
      a = n * k := by rw[hk]
      _ ≡ 0 [ZMOD n] := by extra
  . intro ⟨k, hk⟩
    use k
    calc
      a = a - 0 := by ring
      _ = n * k := by rw[hk]


example {a b : ℤ} (hab : a ∣ b) : a ∣ 2 * b ^ 3 - b ^ 2 + 3 * b := by
  rw[dvd_iff_modEq] at hab
  rw[dvd_iff_modEq]
  calc
    2 * b ^ 3 - b ^ 2 + 3 * b ≡ 2*b^3 - b^2 + 3*0 [ZMOD a] := by rel[hab]
    _ = b*(b*(b*2 - 1)) := by ring
    _ ≡ 0*(b*(b*2 - 1)) [ZMOD a] := by rel[hab]
    _ = 0 := by ring
    _ ≡ 0 [ZMOD a] := by extra

theorem natAbs_lt_iff_sq_lt (x y: ℕ) (h: x^2 < y^2): x < y := by {
  have h': y^2 > x^2 := by addarith[h]
  have h_diff: y^2 - x^2 > 0 := Nat.sub_pos_of_lt h
  have hmul:=
  calc
    (y + x) * (y - x) = y^2 - x^2 := by sorry
    _ > 0 := by addarith[h_diff]
  have ha: (x + y) > 0 ∧ (x - y) > 0 := by sorry
  have hlt: (x - y) > 0 := ha.2
  --calc
  --  y = (y - x) + x := by norm_num
  --  _ > 0 + x := by rel[hlt]
  -- _ = x := by ring
  
  -- nat numbers are pain
  sorry
}

example {k : ℕ} : k ^ 2 ≤ 6 ↔ k = 0 ∨ k = 1 ∨ k = 2 := by
  constructor
  . intro h
    have hlt: k^2 < 3^2 := by addarith[h]
    have hpos: 0 <= 3 := by numbers --dbg
    have hlt3: k < 3 := by {
      apply natAbs_lt_iff_sq_lt
      exact hlt
    }

    interval_cases k
    . left
      ring
    . right; left
      ring
    . right; right
      ring
  . intro h
    match h with
    | Or.inl h0 =>
      calc
        k^2 = 0^2 := by rw[h0]
        _ <= 6 := by numbers
    | Or.inr (Or.inl h1) =>
      calc
        k^2 = 1^2 := by rw[h1]
        _ <= 6 := by numbers
    | Or.inr (Or.inr h2) =>
      calc
        k^2 = 2^2 := by rw[h2]
        _ <= 6 := by numbers
