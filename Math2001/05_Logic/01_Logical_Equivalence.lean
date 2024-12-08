/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Library.Basic

math2001_init
set_option pp.funBinderTypes true


example {P Q : Prop} (h1 : P ∨ Q) (h2 : ¬ Q) : P := by
  obtain hP | hQ := h1
  · apply hP
  · contradiction


example (P Q : Prop) : P → (P ∨ ¬ Q) := by
  intro hP
  left
  apply hP


#truth_table ¬(P ∧ ¬ Q)


example (P : Prop) : (P ∨ P) ↔ P := by
  constructor
  · intro h
    obtain h1 | h2 := h
    · apply h1
    · apply h2
  · intro h
    left
    apply h


example (P Q R : Prop) : (P ∧ (Q ∨ R)) ↔ ((P ∧ Q) ∨ (P ∧ R)) := by
  constructor
  · intro h
    obtain ⟨h1, h2 | h2⟩ := h
    · left
      constructor
      · apply h1
      · apply h2
    · right
      constructor
      · apply h1
      · apply h2
  · intro H
    match H with
    | Or.inl hpaq =>
      constructor
      . exact hpaq.1
      . left
        exact hpaq.2
    | Or.inr hpar =>
      constructor
      . exact hpar.1
      . right
        exact hpar.2

#truth_table P ∧ (Q ∨ R)
#truth_table (P ∧ Q) ∨ (P ∧ R)


example {P Q : α → Prop} (h1 : ∀ x : α, P x) (h2 : ∀ x : α, Q x) :
    ∀ x : α, P x ∧ Q x := by
  intro x
  constructor
  · apply h1
  · apply h2


example {P : α → β → Prop} (h : ∃ x : α, ∀ y : β, P x y) :
    ∀ y : β, ∃ x : α, P x y := by
  obtain ⟨x, hx⟩ := h
  intro y
  use x
  apply hx


example (P : α → Prop) : ¬ (∃ x, P x) ↔ ∀ x, ¬ P x := by
  constructor
  · intro h a ha
    have : ∃ x, P x := by {
      use a
      apply ha
    }
    contradiction
  · intro h h'
    obtain ⟨x, hx⟩ := h'
    have : ¬ P x := h x
    contradiction

/-! # Exercises -/


example {P Q : Prop} (h : P ∧ Q) : P ∨ Q := by
  right
  exact h.2

example {P Q R : Prop} (h1 : P → Q) (h2 : P → R) (h3 : P) : Q ∧ R := by
  constructor
  . exact (h1 h3)
  . exact (h2 h3)

example (P : Prop) : ¬(P ∧ ¬ P) := by
  intro ⟨hp, hnp⟩
  contradiction

example {P Q : Prop} (h1 : P ↔ ¬ Q) (h2 : Q) : ¬ P := by
  intro h
  have:= h1.1 h
  contradiction

example {P Q : Prop} (h1 : P ∨ Q) (h2 : Q → P) : P := by
  cases h1 with
  | inl hp =>
    exact hp
  | inr hq =>
    exact h2 hq

example {P Q R : Prop} (h : P ↔ Q) : (P ∧ R) ↔ (Q ∧ R) := by
  constructor
  . intro hpar
    constructor
    . exact h.1 hpar.1
    . exact hpar.2
  . intro hqar
    constructor
    . exact h.2 hqar.1
    . exact hqar.2

example (P : Prop) : (P ∧ P) ↔ P := by
  constructor
  . intro hpap
    exact hpap.1
  . intro hp
    constructor <;> exact hp

example (P Q : Prop) : (P ∨ Q) ↔ (Q ∨ P) := by
  constructor
  . intro hpoq
    cases hpoq with
    | inl hp =>
      right; exact hp
    | inr hq =>
      left; exact hq
  . intro hqop
    cases hqop with
    | inl hq =>
      right; exact hq
    | inr hp =>
      left; exact hp

example (P Q : Prop) : ¬(P ∨ Q) ↔ (¬P ∧ ¬Q) := by
  constructor
  . intro h
    -- both work:
    -- # method 1
    --have : ¬P ∧ ¬Q := ⟨fun p => h (Or.inl p), fun q => h (Or.inr q)⟩
    --exact this
    -- # method 2
    constructor
    . intro h
      have: P ∨ Q := by {left; exact h}
      contradiction
    . intro h
      have: P ∨ Q := by {right; exact h}
      contradiction
  . intro h
    intro hpaq
    cases hpaq with
    | inl hp =>
      have:=h.1
      contradiction
    | inr hq =>
      have:=h.2
      contradiction

example {P Q : α → Prop} (h1 : ∀ x, P x → Q x) (h2 : ∀ x, P x) : ∀ x, Q x := by
  intro x
  have hp := h2 x
  have hptq := h1 x
  exact hptq hp

example {P Q : α → Prop} (h : ∀ x, P x ↔ Q x) : (∃ x, P x) ↔ (∃ x, Q x) := by
  constructor
  . 
    intro ⟨x, hx⟩
    use x
    exact (h x).1 hx
  . 
    intro ⟨x, hx⟩
    use x
    exact (h x).2 hx

example (P : α → β → Prop) : (∃ x y, P x y) ↔ ∃ y x, P x y := by
  constructor
  . intro H
    obtain ⟨x, y, hxy⟩ := H
    use y, x
    exact hxy
  . intro H
    obtain ⟨y, x, hxy⟩ := H
    use x, y
    exact hxy

example (P : α → β → Prop) : (∀ x y, P x y) ↔ ∀ y x, P x y := by
  constructor
  . intro H
    intro x y
    exact H y x
  . intro H
    intro y x
    exact H x y

example (P : α → Prop) (Q : Prop) : ((∃ x, P x) ∧ Q) ↔ ∃ x, (P x ∧ Q) := by
  constructor
  . intro H
    obtain ⟨⟨x, hx⟩, hq⟩ := H
    use x
    exact ⟨hx, hq⟩
  . 
    intro H
    obtain ⟨x, hx, hq⟩ := H
    constructor
    . use x; exact hx
    . exact hq

-- same but more functional
example (P : α → Prop) (Q : Prop) : ((∃ x, P x) ∧ Q) ↔ ∃ x, (P x ∧ Q) := by
  constructor
  . intro H
    obtain ⟨⟨x, hx⟩, hq⟩ := H
    exact ⟨x, ⟨hx, hq⟩⟩
  . 
    intro H
    obtain ⟨x, hx, hq⟩ := H
    exact ⟨⟨x, hx⟩, hq⟩

-- same purely functional
example (P : α → Prop) (Q : Prop) : ((∃ x, P x) ∧ Q) ↔ ∃ x, (P x ∧ Q) :=
  ⟨fun ⟨⟨x, hx⟩, hq⟩ => ⟨x, ⟨hx, hq⟩⟩,
   fun ⟨x, ⟨hx, hq⟩⟩ => ⟨⟨x, hx⟩, hq⟩⟩
