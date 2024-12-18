/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Tactic.Exhaust

math2001_init

open Function


def p (x : ℝ) : ℝ := 2 * x - 5

example : Bijective p := by
  dsimp [Bijective]
  constructor
  · dsimp [Injective]
    intro x1 x2 hx
    dsimp [p] at hx
    calc x1 = ((2 * x1 - 5) + 5) / 2 := by ring
      _ = ((2 * x2 - 5) + 5) / 2 := by rw [hx]
      _ = x2 := by ring
  · dsimp [Surjective]
    intro y
    use (y + 5) / 2
    calc p ((y + 5) / 2) = 2 * ((y + 5) / 2) - 5 := by rfl
      _ = y := by ring



def a (t : ℝ) : ℝ := t ^ 3 - t

example : ¬ Bijective a := by
  dsimp [Bijective]
  push_neg
  left
  dsimp [Injective]
  push_neg
  use 0, 1
  constructor
  · calc a 0 = 0 ^ 3 - 0 := by rfl
      _ = 1 ^ 3 - 1 := by numbers
      _ = a 1 := by rfl
  · numbers


inductive Celestial
  | sun
  | moon
  deriving DecidableEq

inductive Subatomic
  | proton
  | neutron
  | electron
  deriving DecidableEq

open Celestial Subatomic


def f : Celestial → Subatomic
  | sun => proton
  | moon => electron


example : ¬ Bijective f := by
  dsimp [Bijective]
  push_neg
  right
  dsimp [Surjective]
  push_neg
  use neutron
  intro x
  cases x <;> exhaust


example {f : X → Y} : Bijective f ↔ ∀ y, ∃! x, f x = y := by
  constructor
  · -- if `f` is bijective then `∀ y, ∃! x, f x = y`
    intro h y
    obtain ⟨h_inj, h_surj⟩ := h
    obtain ⟨x, hx⟩ := h_surj y
    use x
    dsimp
    constructor
    · apply hx
    · intro x' hx'
      apply h_inj
      calc f x' = y := by rw [hx']
        _ = f x := by rw [hx]
  · -- if `∀ y, ∃! x, f x = y` then `f` is bijective
    intro h
    constructor
    · -- `f` is injective
      intro x1 x2 hx1x2
      obtain ⟨x, hx, hx'⟩ := h (f x1)
      have hxx1 : x1 = x
      · apply hx'
        rfl
      have hxx2 : x2 = x
      · apply hx'
        rw [hx1x2]
      calc x1 = x := by rw [hxx1]
        _ = x2 := by rw [hxx2]
    · -- `f` is surjective
      intro y
      obtain ⟨x, hx, hx'⟩ := h y
      use x
      apply hx


example : ∀ f : Celestial → Celestial, Injective f → Bijective f := by
  intro f hf
  constructor
  · -- `f` is injective by assumption
    apply hf
  -- show that `f` is surjective
  match h_sun : f sun, h_moon : f moon with
  | sun, sun =>
    have : sun = moon
    · apply hf
      rw [h_sun, h_moon]
    contradiction
  | sun, moon =>
    intro y
    cases y
    · use sun
      apply h_sun
    · use moon
      apply h_moon
  | moon, sun =>
    dsimp[Surjective] at *
    intro c
    cases c
    . use moon; exact h_moon
    . use sun; exact h_sun
  | moon, moon =>
    have: sun = moon := by {
      apply hf
      rw[h_sun, h_moon]
    }
    contradiction


example : ¬ ∀ f : ℕ → ℕ, Injective f → Bijective f := by
  push_neg
  use fun n ↦ n + 1
  constructor
  · -- the function is injective
    intro n1 n2 hn
    addarith [hn]
  · -- the function is not bijective
    dsimp [Bijective]
    push_neg
    right
    -- specifically, it's not surjective
    dsimp [Surjective]
    push_neg
    use 0
    intro n
    apply ne_of_gt
    extra

/-! # Exercises -/


example : Bijective (fun (x : ℝ) ↦ 4 - 3 * x) := by
  constructor
  . intro x y h
    dsimp at h
    norm_num at h
    exact h
  . intro y
    use (4 - y) / 3
    dsimp
    ring

example : ¬ Bijective (fun (x : ℝ) ↦ x ^ 2 + 2 * x) := by
  dsimp[Bijective]
  dsimp[Injective]
  push_neg at *
  left
  use 2, -4
  norm_num
  
inductive Element
  | fire
  | water
  | earth
  | air
  deriving DecidableEq

open Element

def e : Element → Element
  | fire => earth
  | water => air
  | earth => fire
  | air => water

example : Bijective e := by
  dsimp[Bijective]
  constructor
  . 
    intro x y h
    dsimp[e] at h
    cases x <;> cases y <;> exhaust
  . 
    intro y
    cases y
    . use earth; exhaust
    . use air; exhaust
    . use fire; exhaust
    . use water; exhaust


example : ∀ f : Subatomic → Subatomic, Injective f → Bijective f := by
  dsimp[Injective, Bijective]
  intro f
  intro h
  constructor
  . exact h
  dsimp[Surjective]
  intro b
  cases b
  . 
    cases hp : f Subatomic.proton with
    | proton => use proton; exhaust
    | neutron =>
      cases hn : f Subatomic.neutron with
      | proton => use neutron; exhaust
      | neutron =>
        have: f proton = f neutron := by { rw[hp, hn] }
        have:= h this
        exhaust
      | electron =>
        cases he : f Subatomic.electron with
        | proton => use electron; exhaust
        | neutron =>
          have: f proton = f electron := by { rw[hp, he] }
          have:= h this
          exhaust
        | electron =>
          have: f electron = f neutron := by { rw[he, hn] }
          have:= h this
          exhaust
    | electron =>
      cases he : f Subatomic.electron with
      | proton => use electron; exhaust
      | neutron =>
        cases hn : f Subatomic.neutron with
        | proton => use neutron; exhaust
        | neutron =>
          have: f electron = f neutron := by { rw[he, hn] }
          have:= h this
          exhaust
        | electron =>
          have: f proton = f neutron := by { rw[hp, hn] }
          have:= h this
          exhaust
      | electron =>
        have: f electron = f proton := by { rw[he, hp] }
        have:= h this
        exhaust
  -- Last two are exactly the same, just switch the order
  . sorry
  . sorry


example : ∀ f : Element → Element, Injective f → Bijective f := by
  -- uh, fuck no
  sorry
