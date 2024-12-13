/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Tactic.GCongr
import Library.Basic
import Library.Tactic.ModEq

math2001_init

open Int


def a : ℕ → ℤ
  | 0 => 2
  | 1 => 1
  | n + 2 => a (n + 1) + 2 * a n


#eval a 5 -- infoview displays `31`


example (n : ℕ) : a n = 2 ^ n + (-1) ^ n := by
  two_step_induction n with k IH1 IH2
  . calc a 0 = 2 := by rw [a]
      _ = 2 ^ 0 + (-1) ^ 0 := by numbers
  . calc a 1 = 1 := by rw [a]
      _ = 2 ^ 1 + (-1) ^ 1 := by numbers
  calc
    a (k + 2)
      = a (k + 1) + 2 * a k := by rw [a]
    _ = (2 ^ (k + 1) + (-1) ^ (k + 1)) + 2 * (2 ^ k + (-1) ^ k) := by rw [IH1, IH2]
    _ = (2 : ℤ) ^ (k + 2) + (-1) ^ (k + 2) := by ring

-- proving it this way is necessary as split on combinations of values of IH1 and IH2 would produce cases that are in practice never reached and produce contradiction with goal
example {m : ℕ} (hm : 1 ≤ m) : a m ≡ 1 [ZMOD 6] ∨ a m ≡ 5 [ZMOD 6] := by
  have H : ∀ n : ℕ, 1 ≤ n →
      (a n ≡ 1 [ZMOD 6] ∧ a (n + 1) ≡ 5 [ZMOD 6])
    ∨ (a n ≡ 5 [ZMOD 6] ∧ a (n + 1) ≡ 1 [ZMOD 6])
  · intro n hn
    induction_from_starting_point n, hn with k hk IH
    · left
      constructor
      calc a 1 = 1 := by rw [a]
        _ ≡ 1 [ZMOD 6] := by extra
      calc a (1 + 1) = 1 + 2 * 2 := by rw [a, a, a]
        _ = 5 := by numbers
        _ ≡ 5 [ZMOD 6] := by extra
    · obtain ⟨IH1, IH2⟩ | ⟨IH1, IH2⟩ := IH
      · right
        constructor
        · apply IH2
        calc a (k + 1 + 1) = a (k + 1) + 2 * a k := by rw [a]
          _ ≡ 5 + 2 * 1 [ZMOD 6] := by rel [IH1, IH2]
          _ = 6 * 1 + 1 := by numbers
          _ ≡ 1 [ZMOD 6] := by extra
      · left
        constructor
        · apply IH2
        calc a (k + 1 + 1) = a (k + 1) + 2 * a k := by rw [a]
          _ ≡ 1 + 2 * 5 [ZMOD 6] := by rel [IH1, IH2]
          _ = 6 * 1 + 5 := by numbers
          _ ≡ 5 [ZMOD 6] := by extra
  obtain ⟨H1, H2⟩ | ⟨H1, H2⟩ := H m hm
  · left
    apply H1
  · right
    apply H1


def F : ℕ → ℤ
  | 0 => 1
  | 1 => 1
  | n + 2 => F (n + 1) + F n

def test_F (n: ℕ): Bool :=
  (0.4:ℚ) * 1.6 ^ n < F n ∧ F n < (0.5:ℚ) * 1.7 ^ n
#eval test_F 8 -- first true


example (n : ℕ) : F n ≤ 2 ^ n := by
  two_step_induction n with k IH1 IH2
  · calc F 0 = 1 := by rw [F]
      _ ≤ 2 ^ 0 := by numbers
  · calc F 1 = 1 := by rw [F]
      _ ≤ 2 ^ 1 := by numbers
  · calc F (k + 2) = F (k + 1) + F k := by rw [F]
      _ ≤ 2 ^ (k + 1) + 2 ^ k := by rel [IH1, IH2]
      _ ≤ 2 ^ (k + 1) + 2 ^ k + 2 ^ k := by extra
      _ = 2 ^ (k + 2) := by ring


example (n : ℕ) : F (n + 1) ^ 2 - F (n + 1) * F n - F n ^ 2 = - (-1) ^ n := by
  simple_induction n with k IH
  · calc F 1 ^ 2 - F 1 * F 0 - F 0 ^ 2 = 1 ^ 2 - 1 * 1 - 1 ^ 2 := by rw [F, F]
      _ = - (-1) ^ 0 := by numbers
  · calc F (k + 2) ^ 2 - F (k + 2) * F (k + 1) - F (k + 1) ^ 2
        = (F (k + 1) + F k) ^ 2 - (F (k + 1) + F k) * F (k + 1)
            - F (k + 1) ^ 2 := by rw [F]
      _ = - (F (k + 1) ^ 2 - F (k + 1) * F k - F k ^ 2) := by ring
      _ = - -(-1) ^ k := by rw [IH]
      _ = -(-1) ^ (k + 1) := by ring


def d : ℕ → ℤ
  | 0 => 3
  | 1 => 1
  | k + 2 => 3 * d (k + 1) + 5 * d k


#eval d 2 -- infoview displays `18`
#eval d 3 -- infoview displays `59`
#eval d 4 -- infoview displays `267`
#eval d 5 -- infoview displays `1096`
#eval d 6 -- infoview displays `4623`
#eval d 7 -- infoview displays `19349`


#eval 4 ^ 2 -- infoview displays `16`
#eval 4 ^ 3 -- infoview displays `64`
#eval 4 ^ 4 -- infoview displays `256`
#eval 4 ^ 5 -- infoview displays `1024`
#eval 4 ^ 6 -- infoview displays `4096`
#eval 4 ^ 7 -- infoview displays `16384`


example : forall_sufficiently_large n : ℕ, d n ≥ 4 ^ n := by
  dsimp
  use 4
  intro n hn
  two_step_induction_from_starting_point n, hn with k hk IH1 IH2
  · calc d 4 = 267 := by rfl
      _ ≥ 4 ^ 4 := by numbers
  · calc d 5 = 1096 := by rfl
      _ ≥ 4 ^ 5 := by numbers
  calc d (k + 2) = 3 * d (k + 1) + 5 * d k := by rw [d]
    _ ≥ 3 * 4 ^ (k + 1) + 5 * 4 ^ k := by rel [IH1, IH2]
    _ = 16 * 4 ^ k + 4 ^ k := by ring
    _ ≥ 16 * 4 ^ k := by extra
    _ = 4 ^ (k + 2) := by ring

/-! # Exercises -/


def b : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | n + 2 => 5 * b (n + 1) - 6 * b n

example (n : ℕ) : b n = 3 ^ n - 2 ^ n := by
  two_step_induction n with k IH1 IH2
  . rw[b]; norm_num
  . rw[b]; norm_num
  . calc b (k + 1 + 1)
    _ = b (k + 2) := by ring
    _ = 5*b (k + 1) - 6 * b k := by rw[b]
    _ = 5*(3^(k+1) - 2^(k+1)) - 6 * (3^k - 2^k) := by rw[IH2, IH1]
    _ = 3 ^ (k + 1 + 1) - 2 ^ (k + 1 + 1) := by ring

def c : ℕ → ℤ
  | 0 => 3
  | 1 => 2
  | n + 2 => 4 * c n

example (n : ℕ) : c n = 2 * 2 ^ n + (-2) ^ n := by
  two_step_induction n with k IH1 IH2
  . rw[c]; norm_num
  . rw[c]; norm_num
  . calc c (k + 1 + 1)
    _ = c (k + 2) := by ring
    _ = 4 * c k := by rw[c]
    _ = 4 * (2 * 2^k + (-2)^k) := by rw[IH1]
    _ = 2 * 2 ^ (k + 1 + 1) + (-2) ^ (k + 1 + 1) := by ring

def t : ℕ → ℤ
  | 0 => 5
  | 1 => 7
  | n + 2 => 2 * t (n + 1) - t n

example (n : ℕ) : t n = 2 * n + 5 := by
  two_step_induction n with k IH1 IH2
  . rw[t]; norm_num
  . rw[t]; norm_num
  . calc t (k + 1 + 1)
    _ = t (k + 2) := by ring
    _ = 2 * t (k + 1) - t k := by rw[t]
    _ = 2 * (2 * (k+1) + 5) - (2*k + 5) := by rw[IH2, IH1]
    _ = 2 * (k + 1 + 1) + 5 := by ring

def q : ℕ → ℤ
  | 0 => 1
  | 1 => 2
  | n + 2 => 2 * q (n + 1) - q n + 6 * n + 6

example (n : ℕ) : q n = (n:ℤ) ^ 3 + 1 := by
  two_step_induction n with k IH1 IH2
  . rw[q]; norm_num
  . rw[q]; norm_num
  . calc q (k + 1 + 1)
    _ = q (k + 2) := by ring
    _ = 2 * q (k + 1) - q k + 6 * k + 6 := by rw[q]
    _ = 2 * ((k+1)^3 + 1) - (k^3 + 1) + 6 * k + 6 := by rw[IH2, IH1]
    _ = (k + 1 + 1) ^ 3 + 1 := by ring

def s : ℕ → ℤ
  | 0 => 2
  | 1 => 3
  | n + 2 => 2 * s (n + 1) + 3 * s n

example (m : ℕ) : s m ≡ 2 [ZMOD 5] ∨ s m ≡ 3 [ZMOD 5] := by
  have H: (n: ℕ) →
  (s n ≡ 2 [ZMOD 5] ∧ s (n+1) ≡ 3 [ZMOD 5])
  ∨ (s n ≡ 3 [ZMOD 5] ∧ s (n+1) ≡ 2 [ZMOD 5]) := by {
    intro n
    simple_induction n with k IH
    . left; constructor
      . rw[s]; extra
      . rw[s]; extra
    . match IH with
    | Or.inl ⟨h12, h23⟩ =>
      right;
      constructor
      . exact h23
      . rw[s]; calc 2 * s (k + 1) + 3 * s k
        _ ≡ 2 * (3) + 3*(2) [ZMOD 5] := by rel[h12, h23]
        _ = 2 + 5*2 := by ring
        _ ≡ 2 [ZMOD 5] := by extra
    | Or.inr ⟨h13, h22⟩ =>
      left;
      constructor
      . exact h22
      . rw[s]; calc 2 * s (k + 1) + 3 * s k
      _ ≡ 2 * (2) + 3 * (3) [ZMOD 5] := by rel[h22, h13]
      _ = 3 + 5*2 := by ring
      _ ≡ 3 [ZMOD 5] := by extra
  }
  match (H m) with
  | Or.inl ⟨H1, H2⟩ =>
    left; exact H1
  | Or.inr ⟨H1, H2⟩ =>
    right; exact H1

def p : ℕ → ℤ
  | 0 => 2
  | 1 => 3
  | n + 2 => 6 * p (n + 1) - p n

def test_p (n1 n2 : ℕ) : ℤ :=
  (6 * n2 - n1) % 7
#eval test_p 2 3 -- 2
#eval test_p 3 2 -- 2
#eval test_p 2 2 -- 3

example (m : ℕ) : p m ≡ 2 [ZMOD 7] ∨ p m ≡ 3 [ZMOD 7] := by
  have H: (n: ℕ) →
  (p n ≡ 2 [ZMOD 7] ∧ p (n+1) ≡ 3 [ZMOD 7])
  ∨ (p n ≡ 3 [ZMOD 7] ∧ p (n+1) ≡ 2 [ZMOD 7])
  ∨ (p n ≡ 2 [ZMOD 7] ∧ p (n+1) ≡ 2 [ZMOD 7])
  := by {
    intro n
    simple_induction n with k IH
    . left; constructor
      . rw[p]; extra
      . rw[p]; extra
    . match IH with
    | Or.inl ⟨h12, h23⟩ =>
      right; left;
      constructor
      . exact h23
      . rw[p]; calc 6 * p (k + 1) - p k
        _ ≡ 6 * (3) - (2) [ZMOD 7] := by rel[h23, h12]
        _ = 2 + 7*2 := by ring
        _ ≡ 2 [ZMOD 7] := by extra
    | Or.inr (Or.inl ⟨h13, h22⟩) =>
      right; right;
      constructor
      . exact h22
      . rw[p]; calc 6 * p (k + 1) - p k
      _ ≡ 6 * (2) - (3) [ZMOD 7] := by rel[h22, h13]
      _ = 2 + 7*1 := by ring
      _ ≡ 2 [ZMOD 7] := by extra
    | Or.inr (Or.inr ⟨h12, h22⟩) =>
      left;
      constructor
      . exact h22
      . rw[p]; calc 6 * p (k + 1) - p k
      _ ≡ 6 * (2) - (2) [ZMOD 7] := by rel[h22, h12]
      _ = 3 + 7*1 := by ring
      _ ≡ 3 [ZMOD 7] := by extra

  }
  match (H m) with
  | Or.inl ⟨H1, H2⟩ =>
    left; exact H1
  | Or.inr (Or.inl ⟨H1, H2⟩) =>
    right; exact H1
  | Or.inr (Or.inr ⟨H1, H2⟩) =>
    left; exact H1


def r : ℕ → ℤ
  | 0 => 2
  | 1 => 0
  | n + 2 => 2 * r (n + 1) + r n

def test_r (n: ℕ): Bool :=
  r n ≥ 2^n
#eval test_r 7 -- first true

example : forall_sufficiently_large n : ℕ, r n ≥ 2 ^ n := by
  use 7
  intro n hn
  two_step_induction_from_starting_point n, hn with k hk HI1 HI2
  . rw[r, r, r, r, r, r, r, r, r]; norm_num
  . rw[r, r, r, r, r, r, r, r, r, r]; norm_num -- there is a better solution (to just properly split this on terms), but this is funnier
  . rw[r]; calc 2 * r (k + 1) + r k
    _ ≥ 2 * (2^(k+1)) + 2^k := by rel[HI2, HI1]
    _ = 2 ^ (k + 1 + 1) + 2^k := by ring
    _ ≥ 2 ^ (k + 1 + 1) := by norm_num

example : forall_sufficiently_large n : ℕ,
    (0.4:ℚ) * 1.6 ^ n < F n ∧ F n < (0.5:ℚ) * 1.7 ^ n := by
  use 8
  intro n hn
  two_step_induction_from_starting_point n, hn with k hk HI1 HI2
  . rw[F, F, F, F, F, F, F, F, F, F]
    constructor <;> norm_num
  . rw[F, F, F, F, F, F, F, F, F, F, F] --lol
    constructor <;> norm_num
  .
    constructor
    . 
      have: (1.6:ℚ) * 1.6 < 1.6 + 1 := by norm_num
      rw[F]; have:=
      calc ↑(F (k + 1) + F k)
        _ = ↑(F (k + 1)) + ↑(F k) := by norm_num
        _ > ↑(0.4 * 1.6 ^ (k + 1)) + ↑(0.4 * 1.6^k) := by rel[HI2.1, HI1.1]
        _ = (0.4:ℚ) * 1.6^k * (1.6 + 1) := by ring
        _ > (0.4:ℚ) * 1.6^k * (1.6 * 1.6) := by rel[this]
        _ = (0.4:ℚ) * 1.6 ^ (k + 1 + 1) := by ring
      addarith[this]
    . have: (1.7:ℚ) + 1 < 1.7 * 1.7 := by norm_num
      rw[F]; calc
      ↑(F (k + 1) + F k)
      _ = ↑(F (k + 1)) + ↑(F k) := by norm_num
      _ < ((0.5:ℚ) * 1.7 ^ (k + 1)) + (0.5 * 1.7 ^ k) := by rel[HI2.2, HI1.2]
      _ = (0.5:ℚ) * 1.7^(k) * (1.7 + 1) := by ring
      _ < (0.5:ℚ) * 1.7^(k) * (1.7 * 1.7) := by rel[this]
      _ = 0.5 * (1.7:ℚ) ^ (k + 1 + 1) := by ring
