/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Theory.ParityModular
import Library.Basic
import Library.Tactic.Exhaust
import Library.Tactic.ModEq

math2001_init

open Set



example (t : ℝ) : t ∈ {x : ℝ | -1 < x} ∪ {x : ℝ | x < 1} := by
  dsimp
  obtain h | h := le_or_lt t 0
  · right
    addarith [h]
  · left
    addarith [h]


example : {1, 2} ∪ {2, 4} = {1, 2, 4} := by
  ext n
  dsimp
  constructor
  · intro h
    obtain (h | h) | (h | h) := h
    · left
      apply h
    · right
      left
      apply h
  -- and much, much more
    · sorry
    · sorry
  · sorry


example : {2, 1} ∪ {2, 4} = {1, 2, 4} := by
  ext n
  dsimp
  exhaust


example : {-2, 3} ∩ {x : ℚ | x ^ 2 = 9} ⊆ {a : ℚ | 0 < a} := by
  dsimp [Set.subset_def]
  intro t h
  obtain ⟨(h1 | h1), h2⟩ := h
  · have :=
    calc (-2) ^ 2 = t ^ 2 := by rw [h1]
      _ = 9 := by rw [h2]
    numbers at this
  · addarith [h1]


example : {n : ℕ | 4 ≤ n} ∩ {n : ℕ | n < 7} ⊆ {4, 5, 6} := by
  dsimp [Set.subset_def]
  intro n h
  obtain ⟨h1, h2⟩ := h
  interval_cases n <;> exhaust


namespace Int
example : {n : ℤ | Even n}ᶜ = {n : ℤ | Odd n} := by
  ext n
  dsimp
  rw [odd_iff_not_even]
end Int


example (x : ℤ) : x ∉ ∅ := by
  dsimp
  exhaust

example (U : Set ℤ) : ∅ ⊆ U := by
  dsimp [Set.subset_def]
  intro x
  exhaust


example : {n : ℤ | n ≡ 1 [ZMOD 5]} ∩ {n : ℤ | n ≡ 2 [ZMOD 5]} = ∅ := by
  ext x
  dsimp
  constructor
  · intro hx
    obtain ⟨hx1, hx2⟩ := hx
    have :=
    calc 1 ≡ x [ZMOD 5] := by rel [hx1]
      _ ≡ 2 [ZMOD 5] := by rel [hx2]
    numbers at this
  · intro hx
    contradiction


example : {n : ℤ | n ≡ 1 [ZMOD 5]} ∩ {n : ℤ | n ≡ 2 [ZMOD 5]} = ∅ := by
  ext x
  dsimp
  suffices ¬(x ≡ 1 [ZMOD 5] ∧ x ≡ 2 [ZMOD 5]) by exhaust
  intro hx
  obtain ⟨hx1, hx2⟩ := hx
  have :=
  calc 1 ≡ x [ZMOD 5] := by rel [hx1]
    _ ≡ 2 [ZMOD 5] := by rel [hx2]
  numbers at this


example (x : ℤ) : x ∈ univ := by dsimp

example (U : Set ℤ) : U ⊆ univ := by
  dsimp [Set.subset_def]
  intro x
  exhaust


example : {x : ℝ | -1 < x} ∪ {x : ℝ | x < 1} = univ := by
  ext t
  dsimp
  suffices -1 < t ∨ t < 1 by exhaust
  obtain h | h := le_or_lt t 0
  · right
    addarith [h]
  · left
    addarith [h]

/-! # Exercises -/


macro "check_equality_of_explicit_sets" : tactic => `(tactic| (ext; dsimp; exhaust))


example : {-1, 2, 4, 4} ∪ {3, -2, 2} = {-2, -1, 2, 3, 4} := by ext; dsimp; exhaust

example : {0, 1, 2, 3, 4} ∩ {0, 2, 4, 6, 8} = {0, 2, 4} := by
  ext; dsimp; exhaust

example : {1, 2} ∩ {3} = {} := by ext; dsimp; exhaust

example : {3, 4, 5}ᶜ ∩ {1, 3, 5, 7, 9} = {1, 7, 9} := by
  ext; dsimp; exhaust


example : {r : ℤ | r ≡ 7 [ZMOD 10] }
    ⊆ {s : ℤ | s ≡ 1 [ZMOD 2]} ∩ {t : ℤ | t ≡ 2 [ZMOD 5]} := by
  dsimp [Set.subset_def]
  intro z h
  constructor
  . 
    have:=
    calc z
      _ ≡ 7 [ZMOD 10] := by rel [h]
      _ = 7 := by norm_num
      _ = 1 + 2 * 3 := by ring
    obtain ⟨x, hx⟩ := this

    calc z
      _ = 10*x + (1+2*3) := by addarith[hx]
      _ = 1 + 2*(5*x + 3) := by ring
      _ ≡ 1 [ZMOD 2] := by extra

  . 
    have:=
    calc z
      _ ≡ 7 [ZMOD 10] := by rel [h]
      _ = 7 := by norm_num
      _ = 2 + 5*1 := by norm_num
    obtain ⟨x, hx⟩ := this
    
    calc z
      _ = 10*x + (2+5*1) := by addarith[hx]
      _ = 2 + 5*(2*x + 1) := by ring
      _ ≡ 2 [ZMOD 5] := by extra

example : {n : ℤ | 5 ∣ n} ∩ {n : ℤ | 8 ∣ n} ⊆ {n : ℤ | 40 ∣ n} := by
  dsimp [Set.subset_def]
  intro z ⟨⟨a, h5⟩, ⟨b, h8⟩⟩
  use 2*a - 3*b
  calc z
    _ = 16*(z) - 15*(z) := by ring
    _ = 16*(5*a) - 15*(z) := by rw [h5]
    _ = 16*(5*a) - 15*(8*b) := by rw [h8]
    _ = 40*(2*a - 3*b) := by ring

namespace Int
example :
    {n : ℤ | 3 ∣ n} ∪ {n : ℤ | 2 ∣ n} ⊆ {n : ℤ | n ^ 2 ≡ 1 [ZMOD 6]}ᶜ := by
  dsimp [Set.subset_def]
  intro z h
  match h with
  | .inl ⟨c, h3⟩ =>
    intro h
    have h0:=
    calc z^2
      _ = (3*c)^2 := by rw[h3]
      _ = 0 + 3*(3*c^2) := by ring
      _ ≡ 0 [ZMOD 3] := by extra

    have h1: z^2 ≡ 1 [ZMOD 3] := by {
      dsimp[Int.ModEq] at *
      obtain ⟨k, hk⟩ := h
      use 2*k
      calc z^2 - 1
        _ = 6*k := by rw[hk]
        _ = 3*(2*k) := by ring
    }
    
    have:=
    calc 1
      _ ≡ z^2 [ZMOD 3] := by rel[h1]
      _ ≡ 0 [ZMOD 3] := by rel[h0]
    numbers at this

  | .inr ⟨c, h2⟩ =>
    intro h
    have h0:=
    calc z^2
      _ = (2*c)^2 := by rw[h2]
      _ = 0 + 2*(2*c^2) := by ring
      _ ≡ 0 [ZMOD 2] := by extra

    have h1: z^2 ≡ 1 [ZMOD 2] := by {
      dsimp[Int.ModEq] at *
      obtain ⟨k, hk⟩ := h
      use 3*k
      calc z^2 - 1
        _ = 6*k := by rw[hk]
        _ = 2*(3*k) := by ring
    }
    
    have:=
    calc 1
      _ ≡ z^2 [ZMOD 2] := by rel[h1]
      _ ≡ 0 [ZMOD 2] := by rel[h0]
    numbers at this
end Int

def SizeAtLeastTwo (s : Set X) : Prop := ∃ x1 x2 : X, x1 ≠ x2 ∧ x1 ∈ s ∧ x2 ∈ s
def SizeAtLeastThree (s : Set X) : Prop :=
  ∃ x1 x2 x3 : X, x1 ≠ x2 ∧ x1 ≠ x3 ∧ x2 ≠ x3 ∧ x1 ∈ s ∧ x2 ∈ s ∧ x3 ∈ s

example {s t : Set X} (hs : SizeAtLeastTwo s) (ht : SizeAtLeastTwo t)
    (hst : ¬ SizeAtLeastTwo (s ∩ t)) :
    SizeAtLeastThree (s ∪ t) := by
  dsimp [SizeAtLeastTwo, SizeAtLeastThree] at *
  push_neg at *
  obtain ⟨x1, x2, hx12, hx1i, hx2i⟩ := hs
  obtain ⟨y1, y2, hy12, hy1i, hy2i⟩ := ht

  use x1, x2
  simp
  constructor
  . exact hx12

  -- match on matrix {x,y} (4-split)
  -- actually, no clue how to expand exhausts here

  sorry
