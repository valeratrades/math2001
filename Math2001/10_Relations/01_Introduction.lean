/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Tactic.Exhaust
import Library.Tactic.ModEq

math2001_init


example : Reflexive ((·:ℕ) ∣ ·) := by
  dsimp [Reflexive]
  intro x
  use 1
  ring


example : ¬ Symmetric ((·:ℕ) ∣ ·) := by
  dsimp [Symmetric]
  push_neg
  use 1, 2
  constructor
  · use 2
    numbers
  · apply Nat.not_dvd_of_exists_lt_and_lt
    use 0
    constructor
    · numbers
    · numbers


example : AntiSymmetric ((·:ℕ) ∣ ·) := by
  have H : ∀ {m n}, m = 0 → m ∣ n → m = n
  · intro m n h1 h2
    obtain ⟨k, hk⟩ := h2
    calc m = 0 := by rw [h1]
      _ = 0 * k := by ring
      _ = m * k := by rw [h1]
      _ = n := by rw [hk]
  dsimp [AntiSymmetric]
  intro x y h1 h2
  obtain hx | hx := Nat.eq_zero_or_pos x
  · apply H hx h1
  obtain hy | hy := Nat.eq_zero_or_pos y
  · have : y = x := by apply H hy h2
    rw [this]
  apply le_antisymm
  · apply Nat.le_of_dvd hy h1
  · apply Nat.le_of_dvd hx h2


example : Transitive ((·:ℕ) ∣ ·) := by
  dsimp [Transitive]
  intro a b c hab hbc
  obtain ⟨k, hk⟩ := hab
  obtain ⟨l, hl⟩ := hbc
  use k * l
  calc c = b * l := by rw [hl]
    _ = (a * k) * l := by rw [hk]
    _ = a * (k * l) := by ring


example : Reflexive ((·:ℝ) = ·) := by
  dsimp [Reflexive]
  intro x
  ring

example : Symmetric ((·:ℝ) = ·) := by
  dsimp [Symmetric]
  intro x y h
  rw [h]

example : AntiSymmetric ((·:ℝ) = ·) := by
  dsimp [AntiSymmetric]
  intro x y h1 h2
  rw [h1]

example : Transitive ((·:ℝ) = ·) := by
  dsimp [Transitive]
  intro x y z h1 h2
  rw [h1, h2]


section
local infix:50 "∼" => fun (x y : ℝ) ↦ (x - y) ^ 2 ≤ 1

example : Reflexive (· ∼ ·) := by
  dsimp [Reflexive]
  intro x
  calc (x - x) ^ 2 = 0 := by ring
    _ ≤ 1 := by numbers

example : Symmetric (· ∼ ·) := by
  dsimp [Symmetric]
  intro x y h
  calc (y - x) ^ 2 = (x - y) ^ 2 := by ring
    _ ≤ 1 := by rel [h]

example : ¬ AntiSymmetric (· ∼ ·) := by
  dsimp [AntiSymmetric]
  push_neg
  use 1, 1.1
  constructor
  · numbers
  constructor
  · numbers
  · numbers

example : ¬ Transitive (· ∼ ·) := by
  dsimp [Transitive]
  push_neg
  use 1, 1.9, 2.5
  constructor
  · numbers
  constructor
  · numbers
  · numbers

end


section

inductive Hand
  | rock
  | paper
  | scissors

open Hand


@[reducible] def r : Hand → Hand → Prop
  | rock, rock => False
  | rock, paper => True
  | rock, scissors => False
  | paper, rock => False
  | paper, paper => False
  | paper, scissors => True
  | scissors, rock => True
  | scissors, paper => False
  | scissors, scissors => False

local infix:50 " ≺ " => r


example : ¬ Reflexive (· ≺ ·) := by
  dsimp [Reflexive]
  push_neg
  use rock
  exhaust

example : ¬ Symmetric (· ≺ ·) := by
  dsimp [Symmetric]
  push_neg
  use rock, paper
  exhaust

example : AntiSymmetric (· ≺ ·) := by
  dsimp [AntiSymmetric]
  intro x y
  cases x <;> cases y <;> exhaust

example : ¬ Transitive (· ≺ ·) := by
  dsimp [Transitive]
  push_neg
  use rock, paper, scissors
  exhaust

end

/-! # Exercises -/


example : ¬ Symmetric ((·:ℝ) < ·) := by
  dsimp [Symmetric]
  push_neg
  use 1,2
  norm_num

section
local infix:50 "∼" => fun (x y : ℤ) ↦ x ≡ y [ZMOD 2]

example : ¬ AntiSymmetric (· ∼ ·) := by
  dsimp [AntiSymmetric]
  push_neg
  use 1,3
  constructor
  . calc (1:ℤ)
    _ ≡ 1 [ZMOD 2] := by extra
    _ ≡ 1 + 2*1 [ZMOD 2] := by extra
    _ = 3 := by ring
  . constructor
    . calc (3:ℤ)
      _ = 1 + 2*1 := by ring
      _ ≡ 1 [ZMOD 2] := by extra
    . numbers
end


section
inductive Little
  | meg
  | jo
  | beth
  | amy
  deriving DecidableEq

open Little

@[reducible] def s : Little → Little → Prop
  | meg, meg => True
  | meg, jo => True
  | meg, beth => True
  | meg, amy => True
  | jo, meg => True
  | jo, jo => True
  | jo, beth => True
  | jo, amy => False
  | beth, meg => True
  | beth, jo => True
  | beth, beth => False
  | beth, amy => True
  | amy, meg => True
  | amy, jo => False
  | amy, beth => True
  | amy, amy => True

local infix:50 " ∼ " => s


example : ¬ Reflexive (· ∼ ·) := by
  dsimp[Reflexive]
  push_neg
  use beth
  dsimp[s]
  norm_num

example : Symmetric (· ∼ ·) := by
  intro x y h
  cases x <;> cases y <;> exhaust

example : ¬ AntiSymmetric (· ∼ ·) := by
  dsimp[AntiSymmetric]
  push_neg
  use jo, meg
  dsimp[s]
  exhaust

example : ¬ Transitive (· ∼ ·) := by
  dsimp[Transitive]
  push_neg
  use amy, meg, jo
  exhaust
end


section
local infix:50 "∼" => fun (x y : ℤ) ↦ x ≡ y + 1 [ZMOD 5]

example : ¬ Reflexive (· ∼ ·) := by
  dsimp [Reflexive]
  push_neg
  use 1
  norm_num

example : ¬ Symmetric (· ∼ ·) := by
  dsimp [Symmetric]; push_neg
  use 2, 1
  norm_num

example : AntiSymmetric (· ∼ ·) := by
  intro a b hab hba
  have ha2:=
  calc a
    _ ≡ b + 1 [ZMOD 5] := by rel [hab]
    _ ≡ a + 1 + 1 [ZMOD 5] := by rel [hba]
    _ = a + 2 := by ring
  have ha4:=
  calc a + 2
    _ ≡ b + 1 + 2 [ZMOD 5] := by rel [hab]
    _ ≡ a + 1 + 1 + 2 [ZMOD 5] := by rel [hba]
    _ = a + 4 := by ring

  have:=
  calc 2
    _ ≡ 2 [ZMOD 5] := by extra
    _ = (a + 2) - a := by ring
    _ ≡ (a + 4) - a [ZMOD 5] := by rel [ha4]
    _ = 4 := by ring
  numbers at this

example : ¬ Transitive (· ∼ ·) := by
  dsimp[Transitive]; push_neg
  use 3,2,1
  norm_num
end


section
local infix:50 "∼" => fun (x y : ℤ) ↦ x + y ≡ 0 [ZMOD 3]

example : ¬ Reflexive (· ∼ ·) := by
  dsimp[Reflexive]; push_neg
  use 1
  norm_num

example : Symmetric (· ∼ ·) := by
  intro a b h
  calc b + a
    _ = a + b := by ring
    _ ≡ 0 [ZMOD 3] := by rel [h]

example : ¬ AntiSymmetric (· ∼ ·) := by
  dsimp[AntiSymmetric]; push_neg
  use 1,2
  norm_num
  calc (3:ℤ)
    _ = 0 + 3*1 := by ring
    _ ≡ 0 [ZMOD 3] := by extra

example : ¬ Transitive (· ∼ ·) := by
  dsimp[Transitive]; push_neg
  use 1,2,1
  norm_num
  calc (3:ℤ)
    _ = 0 + 3*1 := by ring
    _ ≡ 0 [ZMOD 3] := by extra
end


example : Reflexive ((· : Set ℕ) ⊆ ·) := by
  intro A a h
  exact h

example : ¬ Symmetric ((· : Set ℕ) ⊆ ·) := by
  dsimp[Symmetric]; push_neg
  use {1}, {1,2}
  norm_num

example : AntiSymmetric ((· : Set ℕ) ⊆ ·) := by
  intro A B haib hbia
  dsimp[Set.subset_def] at *
  ext x
  apply Iff.intro
  · intro a
    simp_all only
  · intro a
    simp_all only

example : Transitive ((· : Set ℕ) ⊆ ·) := by
  intro A B C hab hbc x h
  dsimp[Set.subset_def] at *
  have hb:= hab x h
  exact hbc x hb

section
local infix:50 "≺" => fun ((x1, y1) : ℝ × ℝ) (x2, y2) ↦ (x1 ≤ x2 ∧ y1 ≤ y2)

example : Reflexive (· ≺ ·) := by
  intro (x, y)
  norm_num

example : ¬ Symmetric (· ≺ ·) := by
  dsimp[Symmetric]; push_neg
  use (1,1), (2,2)
  norm_num

example : AntiSymmetric (· ≺ ·) := by
  intro (x1, y1) (x2, y2) h1 h2
  simp_all only
  have hx:= le_antisymm h1.1 h2.1
  have hy:= le_antisymm h1.2 h2.2
  rw[hx, hy]

example : Transitive (· ≺ ·) := by
  intro (x1, y1) (x2, y2) (x3, y3) h12 h23
  simp_all only
  have hx:=
  calc x1
    _ ≤ x2 := h12.1
    _ ≤ x3 := h23.1
  have hy:=
  calc y1
    _ ≤ y2 := h12.2
    _ ≤ y3 := h23.2
  exact ⟨hx, hy⟩
end
