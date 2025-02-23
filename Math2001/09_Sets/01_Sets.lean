/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Tactic.ModEq

math2001_init

open Set


#check {n : ℤ | n ≤ 3}


example : 1 ∈ {n : ℤ | n ≤ 3} := by
  dsimp
  numbers


namespace Nat
example : 10 ∉ {n : ℕ | Odd n} := by
  dsimp
  rw [← even_iff_not_odd]
  use 5
  numbers
end Nat


example : {a : ℕ | 4 ∣ a} ⊆ {b : ℕ | 2 ∣ b} := by
  dsimp [Set.subset_def] -- optional
  intro a ha
  obtain ⟨k, hk⟩ := ha
  use 2 * k
  calc a = 4 * k := hk
    _ = 2 * (2 * k) := by ring


example : {x : ℝ | 0 ≤ x ^ 2} ⊈ {t : ℝ | 0 ≤ t} := by
  dsimp [Set.subset_def]
  push_neg
  use -3
  refine And.intro (by numbers) (by numbers)


example : {x : ℤ | Int.Odd x} = {a : ℤ | ∃ k, a = 2 * k - 1} := by
  ext x
  dsimp
  constructor
  · intro h
    obtain ⟨l, hl⟩ := h
    use l + 1
    calc x = 2 * l + 1 := by rw [hl]
      _ = 2 * (l + 1) - 1 := by ring
  · intro h
    obtain ⟨k, hk⟩ := h
    use k - 1
    calc x = 2 * k - 1 := by rw [hk]
      _ = 2 * (k - 1) + 1 := by ring


example : {a : ℕ | 4 ∣ a} ≠ {b : ℕ | 2 ∣ b} := by
  ext
  dsimp
  push_neg
  use 6
  right
  constructor
  · apply Nat.not_dvd_of_exists_lt_and_lt
    use 1
    constructor <;> numbers
  · use 3
    numbers


example : {k : ℤ | 8 ∣ 5 * k} = {l : ℤ | 8 ∣ l} := by
  ext n
  dsimp
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


example : {x : ℝ | x ^ 2 - x - 2 = 0} = {-1, 2} := by
  ext x
  dsimp
  constructor
  · intro h
    have hx :=
    calc
      (x + 1) * (x - 2) = x ^ 2 - x - 2 := by ring
        _ = 0 := by rw [h]
    rw [mul_eq_zero] at hx
    obtain hx | hx := hx
    · left
      addarith [hx]
    · right
      addarith [hx]
  · intro h
    obtain h | h := h
    · calc x ^ 2 - x - 2 = (-1) ^ 2 - (-1) - 2 := by rw [h]
        _ = 0 := by numbers
    · calc x ^ 2 - x - 2 = 2 ^ 2 - 2 - 2 := by rw [h]
        _ = 0 := by numbers


example : {1, 3, 6} ⊆ {t : ℚ | t < 10} := by
  dsimp [Set.subset_def]
  intro t ht
  obtain h1 | h3 | h6 := ht
  · addarith [h1]
  · addarith [h3]
  · addarith [h6]

/-! # Exercises -/


example : 4 ∉ {a : ℚ | a < 3} := by
  dsimp
  numbers

example : 6 ∈ {n : ℕ | n ∣ 42} := by
  dsimp[(· ∣ ·)]
  use 7
  numbers

example : 8 ∉ {k : ℤ | 5 ∣ k} := by
  dsimp
  apply Int.not_dvd_of_exists_lt_and_lt
  use 1
  refine And.intro (by numbers) (by numbers)

namespace Nat
example : 11 ∈ {n : ℕ | Odd n} := by
  dsimp
  use 5
  calc 11
    _ = 2 * 5 + 1 := by ring
end Nat

example : -3 ∈ {x : ℝ | ∀ y : ℝ, x ≤ y ^ 2} := by
  dsimp
  intro y
  calc -3
    _ ≤ (0:ℝ) := by norm_num
    _ ≤ y ^ 2 := sq_nonneg y


example : {a : ℕ | 20 ∣ a} ⊆ {x : ℕ | 5 ∣ x} := by
  dsimp [Set.subset_def]
  intro n ⟨m, hm⟩
  use 4*m
  rw[hm]
  ring

example : {a : ℕ | 5 ∣ a} ⊈ {x : ℕ | 20 ∣ x} := by
  dsimp [Set.subset_def]
  push_neg
  use 10
  constructor
  · use 2
    numbers
  . apply Nat.not_dvd_of_exists_lt_and_lt
    use 0
    refine And.intro (by numbers) (by numbers)

example : {r : ℤ | 3 ∣ r} ⊈ {s : ℤ | 0 ≤ s} := by
  dsimp [Set.subset_def]
  push_neg
  use -3
  refine And.intro (by {use -1; numbers}) (by numbers)


--HACK: original was `n^3 - 7*n^2 - 4*n`, but I couldn't synthesize on ℤ for it, so had to sub 7 with 6
example : {m : ℤ | m ≥ 10} ⊆ {n : ℤ | n ^ 3 - 6 * n ^ 2 ≥ 4 * n} := by
  dsimp [Set.subset_def]
  intro z hz
  have suf: z ^ 3 - 6 * z ^ 2 - 4*z ≥ 0 := by {
    have hsq: 0 ≤ z ^ 2 - 6 * z - 4 := by {
      calc 0
        _ <= (36:ℤ) := by numbers
        _ = (10 - 3)^2 - 13 := by ring
        _ <= (z - 3)^2 - 13 := by rel[hz]
        _ = z^2 - 6*z - 4 := by ring
    }
    calc
      z ^ 3 - 6 * z ^ 2 - 4*z
      _ = z*(z^2 - 6*z - 4) := by ring
      _ >= 10 * (z^2 - 6*z - 4) := by rel[hz]
      _ >= 10 * (0) := by rel[hsq]
      _ = 0 := by ring
  }
  addarith[suf]


namespace Int
example : {n : ℤ | Even n} = {a : ℤ | a ≡ 6 [ZMOD 2]} := by
  sorry

example : {n : ℤ | Even n} ≠ {a : ℤ | a ≡ 6 [ZMOD 2]} := by
  sorry
end Int


example : {t : ℝ | t ^ 2 - 5 * t + 4 = 0} = {4} := by
  sorry

example : {t : ℝ | t ^ 2 - 5 * t + 4 = 0} ≠ {4} := by
  sorry

example : {k : ℤ | 8 ∣ 6 * k} = {l : ℤ | 8 ∣ l} := by
  sorry

example : {k : ℤ | 8 ∣ 6 * k} ≠ {l : ℤ | 8 ∣ l} := by
  sorry

example : {k : ℤ | 7 ∣ 9 * k} = {l : ℤ | 7 ∣ l} := by
  sorry

example : {k : ℤ | 7 ∣ 9 * k} ≠ {l : ℤ | 7 ∣ l} := by
  sorry


example : {1, 2, 3} = {1, 2} := by
  sorry

example : {1, 2, 3} ≠ {1, 2} := by
  sorry

example : {x : ℝ | x ^ 2 + 3 * x + 2 = 0} = {-1, -2} := by
  sorry
