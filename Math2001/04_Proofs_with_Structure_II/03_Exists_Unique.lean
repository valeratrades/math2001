/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Theory.ModEq.Defs

math2001_init

namespace Int


example : ∃! a : ℝ, 3 * a + 1 = 7 := by
  use 2
  dsimp
  constructor
  · numbers
  . intro y hy
    calc
      y = (3 * y + 1 - 1) / 3 := by ring
      _ = (7 - 1) / 3 := by rw [hy]
      _ = 2 := by numbers


example : ∃! x : ℚ, ∀ a, a ≥ 1 → a ≤ 3 → (a - x) ^ 2 ≤ 1 := by
  use 2
  dsimp
  constructor
  . intro a
    intro hge1
    intro hle3
    rw[sq_le_one_iff_abs_le_one]
    dsimp[abs]
    apply max_le
    . addarith[hle3]
    . addarith[hge1]
  . intro y
    intro H
    have h1 := H 1 (by norm_num) (by norm_num) --NB: important to understand how this extraction works: ∀ in H covers all values of a, so as long we satisfy both conditions, we can use the implication for whatever number we provide.
    have h3 := H 3 (by norm_num) (by norm_num)

    have hle0:=
    calc
      (y-2)^2 = ((1-y)^2 + (3-y)^2 - 2) / 2 := by ring
      _ <= (1 + 1 - 2) / 2 := by rel[h1, h3]
      _ = 0 := by ring
    have hpos: (y - 2)^2 >= 0 := by apply sq_nonneg
    have hs0: (y - 2)^2 = 0 := by apply le_antisymm hle0 hpos
    addarith[sq_eq_zero_iff.mp hs0]

example {x : ℚ} (hx : ∃! a : ℚ, a ^ 2 = x) : x = 0 := by
  obtain ⟨a, ha1, ha2⟩ := hx
  have h1 : -a = a := by {
    apply ha2
    calc
      (-a) ^ 2 = a ^ 2 := by ring
      _ = x := ha1
  }
  have h2 :=
    calc
      a = (a - -a) / 2 := by ring
      _ = (a - a) / 2 := by rw [h1]
      _ = 0 := by ring
  calc
    x = a ^ 2 := by rw [ha1]
    _ = 0 ^ 2 := by rw [h2]
    _ = 0 := by ring


example : ∃! r : ℤ, 0 ≤ r ∧ r < 5 ∧ 14 ≡ r [ZMOD 5] := by
  use 4
  dsimp
  constructor
  · constructor
    · numbers
    constructor
    · numbers
    use 2
    numbers
  . intro r hr
    obtain ⟨hr1, hr2, q, hr3⟩ := hr
    have :=
      calc
        5 * 1 < 14 - r := by addarith [hr2]
        _ = 5 * q := by rw [hr3]
    cancel 5 at this
    have :=
      calc
        5 * q = 14 - r := by rw [hr3]
        _ < 5 * 3 := by addarith [hr1]
    cancel 5 at this
    interval_cases q
    addarith [hr3]

/-! # Exercises -/


example : ∃! x : ℚ, 4 * x - 3 = 9 := by
  use 3
  dsimp
  constructor
  . numbers
  . intro x
    intro h
    have h4: 4*x = 4*3 := by addarith[h]
    cancel 4 at h4

example : ∃! n : ℕ, ∀ a, n ≤ a := by
  use 0
  dsimp
  constructor
  . intro a; exact Nat.zero_le a
  . intro y
    intro H
    apply le_antisymm
    . apply H 0
    . apply Nat.zero_le y

example : ∃! r : ℤ, 0 ≤ r ∧ r < 3 ∧ 11 ≡ r [ZMOD 3] := by
  use 2
  dsimp
  dsimp[Int.ModEq]
  dsimp[(· ∣ ·)]
  constructor
  . constructor
    . norm_num
    . constructor
      . norm_num
      . use 3
        ring
  . intro r
    intro ⟨h0le, hlt3, ⟨k, hk⟩⟩
    have hge:=
    calc
      3*k = 11 - r := by addarith[hk]
      _ <= 11 - 0 := by addarith[h0le]
      _ < 3*4 := by numbers
    cancel 3 at hge
    have hlt:=
    calc
      3*k = 11 - r := by addarith[hk]
      _ > 11 - 3 := by addarith[hlt3]
      _ > 3*2 := by numbers
    cancel 3 at hlt
    have hlt: 3 <= k := by addarith[hlt]
    have hge: k <= 3 := by addarith[hge]
    have hk3: k = 3 := by apply le_antisymm hge hlt
    calc
      r = 11 - 3*k := by addarith[hk]
      _ = 11 - 3*3 := by rw[hk3]
      _ = 2 := by ring
