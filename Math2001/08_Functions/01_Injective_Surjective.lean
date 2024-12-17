/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Tactic.Exhaust
import Library.Tactic.ModEq
import Library.Theory.ParityModular

math2001_init
set_option pp.funBinderTypes true

open Function
namespace Int


def F : ℕ → ℤ
  | 0 => 1
  | 1 => 1
  | n + 2 => F (n + 1) + F n

#eval F 5 -- infoview displays `8`


#check @F -- infoview displays `F : ℕ → ℤ`


def q (x : ℝ) : ℝ := x + 3


#check @q -- infoview displays `q : ℝ → ℝ`


#check fun (x : ℝ) ↦ x ^ 2 -- infoview displays `fun x ↦ x ^ 2 : ℝ → ℝ`


example : Injective q := by
  dsimp [Injective]
  intro x1 x2 h
  dsimp [q] at h
  addarith [h]


example : ¬ Injective (fun x : ℝ ↦ x ^ 2) := by
  dsimp [Injective]
  push_neg
  use -1, 1
  constructor
  · numbers
  · numbers


def s (a : ℚ) : ℚ := 3 * a + 2

example : Surjective s := by
  dsimp [Surjective]
  intro y
  use (y - 2) / 3
  calc s ((y - 2) / 3) = 3 * ((y - 2) / 3) + 2 := by rw [s]
    _ = y := by ring


example : ¬ Surjective (fun x : ℝ ↦ x ^ 2) := by
  dsimp [Surjective]
  push_neg
  use -1
  intro x
  apply ne_of_gt
  calc -1 < 0 := by numbers
    _ ≤ x ^ 2 := by extra


inductive Musketeer
  | athos
  | porthos
  | aramis
  deriving DecidableEq

open Musketeer


def f : Musketeer → Musketeer
  | athos => aramis
  | porthos => aramis
  | aramis => athos


example : ¬ Injective f := by
  dsimp [Injective]
  push_neg
  use athos, porthos
  dsimp [f] -- optional
  exhaust


example : ¬ Surjective f := by
  dsimp [Surjective]
  push_neg
  use porthos
  intro a
  cases a
  · exhaust
  · exhaust
  · exhaust


-- better (more automated) version of the previous proof
example : ¬ Surjective f := by
  dsimp [Surjective]
  push_neg
  use porthos
  intro a
  cases a <;> exhaust


def g : Musketeer → Musketeer
  | athos => porthos
  | porthos => aramis
  | aramis => athos


example : Injective g := by
  dsimp [Injective]
  intro x1 x2 hx
  cases x1 <;> cases x2 <;> exhaust


example : Surjective g := by
  dsimp [Surjective]
  intro y
  cases y
  · use aramis
    exhaust
  · use athos
    exhaust
  · use porthos
    exhaust



example : Injective (fun (x:ℝ) ↦ x ^ 3) := by
  intro x1 x2 hx
  dsimp at hx
  have H : (x1 - x2) * (x1 ^ 2 + x1 * x2 + x2 ^ 2) = 0
  · calc (x1 - x2) * (x1 ^ 2 + x1 * x2 + x2 ^ 2) = x1 ^ 3 - x2 ^ 3 := by ring
      _ = x1 ^ 3 - x1 ^ 3 := by rw [hx]
      _ = 0 := by ring
  rw [mul_eq_zero] at H
  obtain H1 | H2 := H
  · -- case 1: x1 - x2 = 0
    addarith [H1]
  · -- case 2: x1 ^2 + x1 * x2 + x2 ^ 2  = 0
    by_cases hx1 : x1 = 0
    · -- case 2a: x1 = 0
      have hx2 :=
      calc x2 ^ 3 = x1 ^ 3 := by rw [hx]
        _ = 0 ^ 3 := by rw [hx1]
        _ = 0 := by numbers
      cancel 3 at hx2
      calc x1 = 0 := by rw [hx1]
        _ = x2 := by rw [hx2]
    · -- case 2b: x1 ≠ 0
      have :=
      calc 0 < x1 ^ 2 + ((x1 + x2) ^ 2 + x2 ^ 2) := by extra
          _ = 2 * (x1 ^ 2 + x1 * x2 + x2 ^ 2) := by ring
          _ = 2 * 0 := by rw [H2]
          _ = 0 := by ring
      numbers at this -- contradiction!

/-! # Exercises -/


example : Injective (fun (x : ℚ) ↦ x - 12) := by
  intro x1 x2 hx
  dsimp at hx
  addarith[hx]

example : ¬ Injective (fun (x : ℝ) ↦ 3) := by
  dsimp[Injective]
  push_neg
  exact ⟨0, 1, ⟨rfl, by {push_neg; numbers}⟩⟩

example : Injective (fun (x : ℚ) ↦ 3 * x - 1) := by
  intro x1 x2 hx
  dsimp at hx
  norm_num at hx
  exact hx

example : Injective (fun (x : ℤ) ↦ 3 * x - 1) := by
  intro x1 x2 hx
  dsimp at hx
  norm_num at hx
  exact hx

example : Surjective (fun (x : ℝ) ↦ 2 * x) := by
  dsimp[Surjective]
  intro x
  use x / 2
  ring

example : ¬ Surjective (fun (x : ℤ) ↦ 2 * x) := by
  dsimp[Surjective]
  push_neg
  use 1
  intro a
  by_contra hf
  match (le_or_succ_le a 0) with
  | Or.inl h0 =>
    have:=
    calc 1
      _ = 2 * a := by rw[hf]
      _ ≤ 2 * 0 := by rel[h0]
      _ = 0 := by ring
    numbers at this
  | Or.inr h1 =>
    have:=
    calc 1
      _ = 2 * a := by rw[hf]
      _ ≥ 2 * (1) := by rel[h1]
      _ = 2 := by ring
    numbers at this

example : ¬ Surjective (fun (n : ℕ) ↦ n ^ 2) := by
  dsimp[Surjective]
  push_neg
  use 2
  intro a
  match (le_or_succ_le a 1) with
  | Or.inl h1 =>
    by_contra hf
    have:=
    calc 2
      _ = a^2 := by rw[hf]
      _ = a * a := by ring
      _ ≤ 1 * 1 := by rel[h1]
      _ = 1 := by ring
    numbers at this
  | Or.inr h2 =>
    by_contra hf
    have:=
    calc 2
      _ = a^2 := by rw[hf]
      _ = a * a := by ring
      _ ≥ 2 * 2 := by rel[h2]
      _ = 4 := by ring
    numbers at this

inductive White
  | meg
  | jack
  deriving DecidableEq

open White

def h : Musketeer → White
  | athos => jack
  | porthos => meg
  | aramis => jack

example : ¬ Injective h := by
  dsimp[Injective]
  push_neg
  use athos, aramis
  exhaust

example : Surjective h := by
  dsimp[Surjective]
  intro a
  cases a
  . use porthos; exhaust
  . use athos; exhaust

def l : White → Musketeer
  | meg => aramis
  | jack => porthos

example : Injective l := by
  dsimp[Injective]
  intro x1 x2 hx
  cases x1 <;> cases x2 <;> exhaust

example : ¬ Surjective l := by
  dsimp[Surjective]
  push_neg
  use athos
  intro a
  cases a <;> exhaust

example (f : X → Y) : Injective f ↔ ∀ x1 x2 : X, x1 ≠ x2 → f x1 ≠ f x2 := by
  constructor
  . dsimp[Injective]
    intro H
    intro x1 x2 hne hfeq
    have hcontra:= H hfeq
    contradiction
  . 
    dsimp[Injective] at *
    intro H
    intro x1 x2 hfeq
    by_cases h: x1 = x2
    . exact h
    . push_neg at h
      have hcontra:= H x1 x2 h
      contradiction

example : ∀ (f : ℚ → ℚ), Injective f → Injective (fun x ↦ f x + 1) := by
  dsimp[Injective] at *
  intro f H
  intro x1 x2 heq
  norm_num at heq
  exact H heq

example : ¬∀ (f : ℚ → ℚ), Injective f → Injective (fun x ↦ f x + x) := by
  dsimp[Injective] at *
  push_neg
  use fun (x: ℚ) ↦ -x
  constructor
  . norm_num
  use 1, -1
  norm_num


example : ¬ ∀ (f : ℤ → ℤ), Surjective f → Surjective (fun x ↦ 2 * f x) := by
  dsimp[Surjective] at *
  push_neg
  use fun (x: ℤ) ↦ x
  constructor
  . norm_num
  use 1
  intro a
  match (le_or_succ_le a 0) with
  | Or.inl h0 =>
    by_contra heq
    have:= calc 1
      _ = 2 * a := by rw[heq]
      _ ≤ 2 * 0 := by rel[h0]
      _ = 0 := by ring
    numbers at this
  | Or.inr h1 =>
    by_contra heq
    have:= calc 1
      _ = 2 * a := by rw[heq]
      _ ≥ 2 * 1 := by rel[h1]
      _ = 2 := by ring
    numbers at this

example : ¬∀ c : ℝ, Surjective (fun x ↦ c * x) := by
  dsimp[Surjective]
  push_neg
  use 0, 1
  norm_num

example {f : ℚ → ℚ} (H: ∀ x y, x < y → f x < f y) : Injective f := by
  dsimp[Injective] at *
  --obtain ⟨x, y, h⟩ := hf
  intro x y hfeq
  by_contra hne
  match (lt_or_gt_of_ne hne) with
  | Or.inl h =>
    have hf:= H x y h
    have: f x ≠ f y := by {
      apply ne_of_lt
      exact hf
    }
    contradiction
  | Or.inr h =>
    have hf:= H y x h
    have: f x ≠ f y := by {
      apply ne_of_gt
      exact hf
    }
    contradiction



example {f : X → ℕ} {x0 : X} (h0 : f x0 = 0) {i : X → X}
    (hi : ∀ x, f (i x) = f x + 1) : Surjective f := by
  dsimp[Surjective] at *
  intro y
  simple_induction y with y IH
  . use x0; rw[h0]
  . 
    obtain ⟨ia, hia⟩ := IH
    use (i ia)
    calc f (i ia)
      _ = f ia + 1 := by rw[hi]
      _ = y + 1 := by rw[hia]
