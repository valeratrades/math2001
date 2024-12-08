/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Tactic.ModEq
import Library.Theory.ParityModular

math2001_init


example {y : ℝ} (x : ℝ) (h : 0 < x * y) (hx : 0 ≤ x) : 0 < y := by
  obtain hneg | hpos : y ≤ 0 ∨ 0 < y := le_or_lt y 0
  · -- the case `y ≤ 0`
    have: ¬(0 < x * y) := by {
      apply not_lt_of_ge
      calc
        0 = x * 0 := by ring
        _ ≥ x * y := by rel[hneg]
    }
    contradiction
  · -- the case `0 < y`
    apply hpos


example {t : ℤ} (h2 : t < 3) (h : t - 1 = 6) : t = 13 := by
  have H :=
  calc
    7 = t := by addarith [h]
    _ < 3 := h2
  have : ¬(7 : ℤ) < 3 := by numbers
  contradiction


example {t : ℤ} (h2 : t < 3) (h : t - 1 = 6) : t = 13 := by
  have H :=
  calc
    7 = t := by addarith [h]
    _ < 3 := h2
  numbers at H -- this is a contradiction!


example (n : ℤ) (hn : n ^ 2 + n + 1 ≡ 1 [ZMOD 3]) :
    n ≡ 0 [ZMOD 3] ∨ n ≡ 2 [ZMOD 3] := by
  mod_cases h : n % 3
  · -- case 1: `n ≡ 0 [ZMOD 3]`
    left
    apply h
  · -- case 2: `n ≡ 1 [ZMOD 3]`
    have H :=
      calc 0 ≡ 0 + 3 * 1 [ZMOD 3] := by extra
      _ = 1 ^ 2 + 1 + 1 := by numbers
      _ ≡ n ^ 2 + n + 1 [ZMOD 3] := by rel [h]
      _ ≡ 1 [ZMOD 3] := hn
    numbers at H -- contradiction!
  · -- case 3: `n ≡ 2 [ZMOD 3]`
    right
    apply h


example {p : ℕ} (hp : 2 ≤ p) (H : ∀ m : ℕ, 1 < m → m < p → ¬m ∣ p) : Prime p := by
  dsimp[Prime]
  constructor
  · apply hp -- show that `2 ≤ p`
  intro m hmp
  have hp' : 0 < p := by extra
  have h1m : 1 ≤ m := Nat.pos_of_dvd_of_pos hmp hp'
  obtain hm | hm_left : 1 = m ∨ 1 < m := eq_or_lt_of_le h1m
  · -- the case `m = 1`
    left
    addarith [hm]
  . -- the case `1 < m`
    --? have 2 
    have hmltp_suff := H m (hm_left)
    have: m <= p := by apply Nat.le_of_dvd hp' hmp
    obtain meqp | mltp: m = p ∨ m < p := eq_or_lt_of_le this
    . right
      exact meqp
    . have hc: ¬(m ∣ p) := by apply hmltp_suff mltp
      contradiction

example : Prime 5 := by
  apply prime_test
  · numbers
  intro m hm_left hm_right
  apply Nat.not_dvd_of_exists_lt_and_lt
  interval_cases m
  · use 2
    constructor <;> numbers
  · use 1
    constructor <;> numbers
  · use 1
    constructor <;> numbers

theorem sq_lt {a b: ℕ} (h: a^2 < b^2): a < b := by
  have:=
  calc
    a*a = a^2 := by ring
    _ < b^2 := by rel[h]
    _ = b*b := by ring
  exact lt_of_mul_self_lt_mul_self (by norm_num) this

example {a b c : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h_pyth : a ^ 2 + b ^ 2 = c ^ 2) : 3 ≤ a := by
  match (le_or_succ_le a 2) with
  | Or.inl hale2 =>
    match (le_or_succ_le b 1) with
    | Or.inl hble1 =>
      have hb: b = 1 := by {
        sorry
      }

      have:=
      calc
        c^2 = a^2 + b^2 := by addarith[h_pyth]
        _ <= 2^2 + 1^2 := by rel[hale2, hble1]
        _ < 3^2 := by numbers
      have hclt3:= sq_lt this

      interval_cases c
      . interval_cases a
        . 
          have:=
          calc
            1^2 = 1^2 + b^2 := by addarith[h_pyth]
            _ = 1^2 + 1^2 := by rw[hb]
            _ = 2 := by ring
          numbers at this
        . 
          have:=
          calc
            1^2 = 2^2 + b^2 := by addarith[h_pyth]
            _ = 2^2 + 1^2 := by rw[hb]
            _ = 5 := by ring
          numbers at this
      . interval_cases a
        .
          have:=
          calc
            2^2 = 1^2 + b^2 := by addarith[h_pyth]
            _ = 1^2 + 1^2 := by rw[hb]
            _ = 2 := by ring
          numbers at this
        .
          have:=
          calc
            2^2 = 2^2 + b^2 := by addarith[h_pyth]
            _ = 2^2 + 1^2 := by rw[hb]
            _ = 5 := by ring
          numbers at this
    | Or.inr h2leb =>
      -- c > 2
      have hbp1le: b+1 <= c := by {
        have hage1: a >= 1 := by addarith[ha]
        have bs:=
        calc
          b^2 < 1^2 + b^2 := by extra
          _ <= a^2 + b^2 := by rel[hage1]
          _ = c^2 := by addarith[h_pyth]
        addarith[sq_lt bs]
      }

      have:=
      calc
        c^2 = a^2 + b^2 := by addarith[h_pyth]
        _ <= 2^2 + b^2 := by rel[hale2]
        _ = b^2 + 2*2 := by ring
        _ <= b^2 + 2*b := by rel[h2leb]
        _ < b^2 + 2*b + 1 := by extra
        _ = (b+1)^2 := by ring
      have hclt:= sq_lt this
      have h_false:= not_lt_of_le hbp1le
      contradiction
  | Or.inr h3lea =>
    exact h3lea

/-! # Exercises -/


example {x y : ℝ} (n : ℕ) (hx : 0 ≤ x) (hn : 0 < n) (h : y ^ n ≤ x ^ n) :
    y ≤ x := by
  match (lt_or_ge x y) with
  | Or.inl hxlty =>
    have hdiff:=
    calc
      y - x > x - x := by rel[hxlty]
      _ = 0 := by ring
    have:=
    calc
      y^n = (x + (y - x))^n := by ring
      _ > (x + 0)^n := by rel[hdiff]
      _ = x^n := by ring
    have h_false:= not_le_of_lt this
    contradiction
  | Or.inr h =>
    addarith[h]



example (n : ℤ) (hn : n ^ 2 ≡ 4 [ZMOD 5]) : n ≡ 2 [ZMOD 5] ∨ n ≡ 3 [ZMOD 5] := by
  mod_cases h: n % 5
  . have:=
    calc
      4 ≡ n^2 [ZMOD 5] := by rel[hn]
      _ = n*n := by ring
      _ ≡ n * n [ZMOD 5] := by extra
      _ ≡ 0 * 0 [ZMOD 5] := by rel[h]
      _ = 0 := by ring
    numbers at this
  .
    have:=
    calc
      4 ≡ n^2 [ZMOD 5] := by rel[hn]
      _ = n*n := by ring
      _ ≡ n * n [ZMOD 5] := by extra
      _ ≡ 1 * 1 [ZMOD 5] := by rel[h]
      _ = 1 := by ring
    numbers at this
  . left; exact h
  . right; exact h
  . have:=
    calc
      4 ≡ n^2 [ZMOD 5] := by rel[hn]
      _ = n*n := by ring
      _ ≡ n * n [ZMOD 5] := by extra
      _ ≡ 4 * 4 [ZMOD 5] := by rel[h]
      _ ≡ 1 + 5*3 [ZMOD 5] := by numbers
      _ ≡ 1 [ZMOD 5] := by extra
      _ = 1 := by ring
    numbers at this

example : Prime 7 := by {
  apply prime_test
  · numbers
  intro m hm_left hm_right
  apply Nat.not_dvd_of_exists_lt_and_lt
  interval_cases m
  · use 3
    constructor <;> numbers
  · use 2
    constructor <;> numbers
  · use 1
    constructor <;> numbers
  · use 1
    constructor <;> numbers
  · use 1
    constructor <;> numbers
}

example {x : ℚ} (h1 : x^2 = 4) (h2 : 1 < x) : x = 2 := by
  have h3 :=
    calc
      (x + 2) * (x - 2) = x ^ 2 + 2 * x - 2 * x - 4 := by ring
      _ = 0 := by addarith [h1]
  rw [mul_eq_zero] at h3
  match h3 with
  | Or.inl hp2 =>
    have:=
    calc
      -2 = x := by addarith[hp2]
      _ > 1 := by rel[h2]
    numbers at this
  | Or.inr hm2 =>
    addarith[hm2]

namespace Nat

example (p : ℕ) (h : Prime p) : p = 2 ∨ Odd p := by
  obtain ⟨h2, hp⟩ := h
  match (le_or_gt p 2) with
  | Or.inl hle2 =>
    left
    exact Nat.le_antisymm hle2 h2
  | Or.inr hgt2 =>
    cases Nat.mod_two_eq_zero_or_one p with --HACK: would be nicer to use something generic like mad_cases, but fuck it
    | inl hmod_zero =>
      left
      have hm0: p ≡ 0 [ZMOD 2] := by sorry -- should just have this with mod_cases
      -- ∃ k, p = 2*k
      -- 2 | p
      -- 2 = p
      -- _ > 2
      -- numbers at this
      sorry
    | inr hmod_one =>
      right
      have hm1: p ≡ 1 [ZMOD 2] := by sorry -- should just have this with mod_cases
      -- say it's p = 2*k + 1 := by addarith[hm1]
      -- that's exact def of Odd
      sorry
