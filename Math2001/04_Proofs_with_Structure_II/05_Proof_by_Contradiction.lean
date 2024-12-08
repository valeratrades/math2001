/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Theory.ParityModular
import Library.Basic
import Library.Tactic.ModEq

math2001_init

open Int


example : ¬ (∀ x : ℝ, x ^ 2 ≥ x) := by
  intro h
  have : 0.5 ^ 2 ≥ 0.5 := h 0.5
  numbers at this


example : ¬ 3 ∣ 13 := by
  intro H
  obtain ⟨k, hk⟩ := H
  match (le_or_succ_le k 4) with
  | Or.inl h4 =>
    have:=
    calc 13 = 3 * k := hk
      _ ≤ 3 * 4 := by rel [h4]
    numbers at this
  | Or.inr h5 =>
    have:=
    calc
      13 = 3*k := hk
      _ >= 3 * 5 := by rel[h5]
    numbers at this

example {x y : ℝ} (h : x + y = 0) : ¬(x > 0 ∧ y > 0) := by
  intro hpred
  obtain ⟨hx, hy⟩ := hpred
  have H :=
  calc 0 = x + y := by rw [h]
    _ > 0 := by extra
  numbers at H


example : ¬ (∃ n : ℕ, n ^ 2 = 2) := by
  intro h
  obtain ⟨n, hn⟩ := h
  match (le_or_succ_le n 1) with
  | Or.inl h1 =>
    have:=
    calc
      2 = n^2 := by addarith[hn]
      _ <= 1^2 := by rel[h1]
      _ = 1 := by ring
    numbers at this
  | Or.inr h2 =>
    have:=
    calc
      2 = n^2 := by addarith[hn]
      _ >= 2^2 := by rel[h2]
      _ = 4 := by ring
    numbers at this

example (n : ℤ) : Int.Even n ↔ ¬ Int.Odd n := by
  constructor
  · intro h1 h2
    rw [Int.even_iff_modEq] at h1
    rw [Int.odd_iff_modEq] at h2
    have :=
    calc 0 ≡ n [ZMOD 2] := by rel [h1]
      _ ≡ 1 [ZMOD 2] := by rel [h2]
    numbers at this -- contradiction!
  · intro h
    obtain h1 | h2 := Int.even_or_odd n
    · apply h1
    · contradiction


example (n : ℤ) : Int.Odd n ↔ ¬ Int.Even n := by
  constructor
  . intro ho he
    rw[Int.even_iff_modEq] at he
    rw[Int.odd_iff_modEq] at ho
    have:=
    calc 0 ≡ n [ZMOD 2] := by rel[he]
      _ ≡ 1 [ZMOD 2] := by rel[ho]
    numbers at this
  . intro h
    match (Int.even_or_odd n) with
    | Or.inl he =>
      contradiction
    | Or.inr ho =>
      apply ho

example (n : ℤ) : ¬(n ^ 2 ≡ 2 [ZMOD 3]) := by
  intro h
  mod_cases hn : n % 3
  · have:=
    calc (0:ℤ) = 0 ^ 2 := by numbers
      _ ≡ n ^ 2 [ZMOD 3] := by rel [hn]
      _ ≡ 2 [ZMOD 3] := by rel [h]
    numbers at this -- contradiction!
  · have:=
    calc (1:ℤ) = 1^2 := by ring
      _ ≡ n^2 [ZMOD 3] := by rel[hn]
      _ ≡ 2 [ZMOD 3] := by rel[h]
    numbers at this
  · have:=
    calc (1:ℤ) ≡ 1 + 1*3 [ZMOD 3] := by extra
      _ = 2^2 := by ring
      _ ≡ n^2 [ZMOD 3] := by rel[hn]
      _ ≡ 2 [ZMOD 3] := by rel[h]
    numbers at this

example {p : ℕ} (k l : ℕ) (hk1 : k ≠ 1) (hkp : k ≠ p) (hkl : p = k * l) :
    ¬(Prime p) := by
  have hk : k ∣ p := by {
    · use l
      apply hkl
  }
  intro h
  obtain ⟨h2, hfact⟩ := h
  have : k = 1 ∨ k = p := hfact k hk
  obtain hk1' | hkp' := this
  · contradiction
  · contradiction


example (a b : ℤ) (h : ∃ q, b * q < a ∧ a < b * (q + 1)) : ¬b ∣ a := by
  intro H
  obtain ⟨k, hk⟩ := H
  obtain ⟨q, hq₁, hq₂⟩ := h
  have hb :=
  calc 0 = a - a := by ring
    _ < b * (q + 1) - b * q := by rel [hq₁, hq₂]
    _ = b := by ring
  have hlt_succ :=
  calc b * k = a := by rw [hk]
    _ < b * (q + 1) := hq₂
  cancel b at hlt_succ
  -- q < k < q+1
  -- all are on ℤ, so impossible
  have hgt_prev: q < k := by {
    have:=
    calc
      b * q < a := hq₁
      _ = b * k := by rw[hk]
    cancel b at this
  }
  have: q + 1 <= k := by addarith[hgt_prev]
  have:=
  calc
    q + 1 <= k := this
    _ < q + 1 := by rel[hlt_succ]
  have: 1 < 1 := by addarith[this]
  numbers at this

example {p : ℕ} (hp : 2 ≤ p)  (T : ℕ) (hTp : p < T ^ 2)
    (H : ∀ (m : ℕ), 1 < m → m < T → ¬ (m ∣ p)) :
    Prime p := by
  apply prime_test hp
  intro m hm1 hmp
  obtain hmT | hmT := lt_or_le m T
  · apply H m hm1 hmT
  intro h_div
  obtain ⟨l, hl⟩ := h_div
  have: l ∣ p := by {
    use m
    calc p = m * l := hl
      _ = l * m := by ring
  }
  have hl1 :=
    calc m * 1 = m := by ring
      _ < p := hmp
      _ = m * l := hl
  cancel m at hl1
  have hl2: l < T := by {
    have:=
    calc
      m*l = p := by addarith[hl]
      _ < T^2 := by rel[hTp]
      _ = T*T := by ring
      _ <= m*T := by rel[hmT]
    cancel m at this
  }
  have : ¬ l ∣ p := H l hl1 hl2
  contradiction


example : Prime 79 := by
  apply better_prime_test (T := 9)
  · numbers
  · numbers
  intro m hm1 hm2
  apply Nat.not_dvd_of_exists_lt_and_lt
  interval_cases m
  · use 39
    constructor <;> numbers
  · use 26
    constructor <;> numbers
  · use 19
    constructor <;> numbers
  · use 15
    constructor <;> numbers
  · use 13
    constructor <;> numbers
  · use 11
    constructor <;> numbers
  · use 9
    constructor <;> numbers

/-! # Exercises -/


example : ¬ (∃ t : ℝ, t ≤ 4 ∧ t ≥ 5) := by
  intro h
  obtain ⟨t, h4, h5⟩ := h
  have hlt5: t < 5 := by addarith[h4]
  have:=
  calc
    5 <= t := by rel[h5]
    _ < 5 := by rel[hlt5]
  numbers at this

example : ¬ (∃ a : ℝ, a ^ 2 ≤ 8 ∧ a ^ 3 ≥ 30) := by
  intro H
  obtain ⟨a, hp2, hp3⟩ := H
  have hlt3: a < 3 := by {
    have:=
    calc a^2 <= 8 := hp2
      _ < 3^2 := by numbers
    apply abs_lt_of_sq_lt_sq' at this
    exact (this (by norm_num)).2
  }
  have:=
  calc
    30 <= a^3 := by addarith[hp3]
    _ = a^2 *a := by ring
    _ <= a^2 *3 := by rel[hlt3]
    _ <= 8 * 3 := by rel[hp2]
    _ = 24 := by ring
  numbers at this

example : ¬ Int.Even 7 := by
  intro h
  obtain ⟨k, hk⟩ := h
  -- think I need to just prove the whole thing with q and q+1 again

  have h4: k < 4 := by {
    have:=
    calc
      2 * k = 7 := by addarith[hk]
      _ < 2 * 4 := by numbers
    cancel 2 at this
  }
  have h3: k > 3 := by {
    have:=
    calc
      2 * k = 7 := by addarith[hk]
      _ > 2 * 3 := by numbers
    cancel 2 at this
  }
  have hge: k >= 4 := by addarith[h3]
  have:=
  calc
    4 > k := by rel[h4]
    _ >= 4 := by rel[hge]
  numbers at this


example {n : ℤ} (hn : n + 3 = 7) : ¬ (Int.Even n ∧ n ^ 2 = 10) := by
  intro H
  have hfalse := H.2
  have h0: 0 <= n := by addarith[hn]

  have h3: n > 3 := by {
    have:=
    calc
      n^2 = 10 := hfalse
      _ > 3^2 := by numbers
    apply abs_lt_of_sq_lt_sq' at this
    exact (this h0).2
  }
  have h4: n < 4 := by {
    have:=
    calc
      n^2 = 10 := hfalse
      _ < 4^2 := by numbers
    apply abs_lt_of_sq_lt_sq' at this
    exact (this (by norm_num)).2
  }

  have hge: n >= 4 := by addarith[h3]
  have:=
  calc
    4 > n := by rel[h4]
    _ >= 4 := by rel[hge]
  numbers at this

example {x : ℝ} (hx : x ^ 2 < 9) : ¬ (x ≤ -3 ∨ x ≥ 3) := by
  intro H
  match H with
  | Or.inl hlem3 =>
    have: 3 <= -x := by addarith[hlem3]
    have:=
    calc
      3*3 <= -x*-x := by rel[this]
      _ = x^2 := by ring
      _ < 9 := by rel[hx]
    numbers at this
  | Or.inr h3le =>
    have:=
    calc
      3*3 <= x*x := by rel[h3le]
      _ = x^2 := by ring
      _ < 9 := by rel[hx]
    numbers at this

-- changed to ℤ from ℕ because the mod_cases is not supplied for Nat by our local lib. But I will do the exercise in ℕ spirit, using `-` as I would on ℕ
example : ¬ (∃ N : ℤ, ∀ k > N, Int.Even k) := by
  intro H
  dsimp[Int.Even] at *
  obtain ⟨n, hka⟩ := H
  mod_cases h: n % 2
  . -- 0 [ZMOD] 2
    have ha:= hka (n+1) (by norm_num)
    have hm1:=
    calc
      n + 1 ≡ 0 + 1 [ZMOD 2] := by rel[h]
      _ = 1 := by ring
    have hm0: n + 1 ≡ 0 [ZMOD 2] := by {
      obtain ⟨k, hk⟩ := ha
      calc
        n+1 = 2*k := by rw[hk]
        _ ≡ 0 [ZMOD 2] := by extra
    }
    have:=
    calc
      0 ≡ n + 1 [ZMOD 2] := by rel[hm0]
      _ ≡ 1 [ZMOD 2] := by rel[hm1]
    numbers at this
  . -- 1 [ZMOD] 2
    -- same as prev, but (n+2) instead of (n+1)
    have ha:= hka (n+2) (by norm_num)
    have hm1:=
    calc
      n + 2 ≡ 1 + 2 [ZMOD 2] := by rel[h]
      _ = 1 + 1*2 := by ring
      _ ≡ 1 [ZMOD 2] := by extra
    have hm0: n + 2 ≡ 0 [ZMOD 2] := by {
      obtain ⟨k, hk⟩ := ha
      calc
        n+2 = 2*k := by rw[hk]
        _ ≡ 0 [ZMOD 2] := by extra
    }
    have:=
    calc
      0 ≡ n + 2 [ZMOD 2] := by rel[hm0]
      _ ≡ 1 [ZMOD 2] := by rel[hm1]
    numbers at this

example (n : ℤ) : ¬(n ^ 2 ≡ 2 [ZMOD 4]) := by
  intro hnp2m2
  mod_cases h: n % 4
  . have:=
    calc
      2 ≡ n^2 [ZMOD 4] := by rel[hnp2m2]
      _ ≡ 0^2 [ZMOD 4] := by rel[h]
      _ = 0 := by ring
    numbers at this
  . have:=
    calc
      2 ≡ n^2 [ZMOD 4] := by rel[hnp2m2]
      _ ≡ 1^2 [ZMOD 4] := by rel[h]
      _ = 1 := by ring
    numbers at this
  . have:=
    calc
      2 ≡ n^2 [ZMOD 4] := by rel[hnp2m2]
      _ ≡ 2^2 [ZMOD 4] := by rel[h]
      _ = 0 + 4*1 := by ring
      _ ≡ 0 [ZMOD 4] := by extra
    numbers at this
  . have:=
    calc
      2 ≡ n^2 [ZMOD 4] := by rel[hnp2m2]
      _ ≡ 3^2 [ZMOD 4] := by rel[h]
      _ = 1 + 4*2 := by ring
      _ ≡ 1 [ZMOD 4] := by extra
    numbers at this

example : ¬ Prime 1 := by
  intro H
  have h2:= H.1
  numbers at h2

example: Prime 97 := by
  apply better_prime_test (T := 10)
  . numbers
  . numbers

  intro m hm1 hm2
  apply Nat.not_dvd_of_exists_lt_and_lt
  interval_cases m
  · use 48
    constructor <;> numbers
  · use 32
    constructor <;> numbers
  · use 24
    constructor <;> numbers
  · use 19
    constructor <;> numbers
  · use 16
    constructor <;> numbers
  · use 13
    constructor <;> numbers
  · use 12
    constructor <;> numbers
  · use 10
    constructor <;> numbers
