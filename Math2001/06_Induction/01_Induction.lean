/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.ModEq
import Library.Basic
import Library.Tactic.ModEq

math2001_init

namespace Nat


example (n : ℕ) : 2 ^ n ≥ n + 1 := by
  simple_induction n with k IH
  · -- base case
    numbers
  · -- inductive step
    calc 2 ^ (k + 1) = 2 * 2 ^ k := by ring
      _ ≥ 2 * (k + 1) := by rel [IH]
      _ = (k + 1 + 1) + k := by ring
      _ ≥ k + 1 + 1 := by extra


example (n : ℕ) : Even n ∨ Odd n := by
  simple_induction n with k IH
  · -- base case
    left; use 0; norm_num
  · -- inductive step
    obtain ⟨x, hx⟩ | ⟨x, hx⟩ := IH
    · right
      use x
      norm_num
      exact hx
    · left
      use x+1
      calc
        k + 1 = (2*x + 1) + 1 := by rw[hx]
        _ = 2 * (x + 1) := by ring

lemma zmod_pow {a b d : ℤ} (h : a ≡ b [ZMOD d]) (n : ℕ) : a ^ n ≡ b ^ n [ZMOD d] := by
  simple_induction n with k IH
  . calc
    a ^ 0 = 1 := by ring
    _ ≡ 1 [ZMOD d] := by extra
    _ = b ^ 0 := by ring
  . calc
    a ^ (k + 1) = a * a^k := by ring
    _ ≡ b * b^k [ZMOD d] := by rel[h, IH]
    _ = b ^ (k + 1) := by ring

lemma mod_pow {a b d : ℕ} (h : a ≡ b [MOD d]) (n : ℕ) : a ^ n ≡ b ^ n [MOD d] := by
  simple_induction n with k IH
  . calc
    a ^ 0 = 1 := by ring
    _ ≡ 1 [MOD d] := by exact Nat.ModEq.refl 1
    _ = b ^ 0 := by ring
  . calc
    a ^ (k + 1) = a * a^k := by ring
    _ ≡ b * b^k [MOD d] := by rel[h, IH]
    _ = b ^ (k + 1) := by ring

example (n : ℕ) : 4 ^ n ≡ 1 [ZMOD 15] ∨ 4 ^ n ≡ 4 [ZMOD 15] := by
  simple_induction n with k IH
  · -- base case
    left
    numbers
  · -- inductive step
    obtain hk | hk := IH
    · right
      calc (4:ℤ) ^ (k + 1) = 4 * 4 ^ k := by ring
        _ ≡ 4 * 1 [ZMOD 15] := by rel [hk]
        _ = 4 := by numbers
    · left
      calc (4:ℤ) ^ (k + 1) = 4 * 4 ^ k := by ring
        _ ≡ 4 * 4 [ZMOD 15] := by rel [hk]
        _ = 15 * 1 + 1 := by numbers
        _ ≡ 1 [ZMOD 15] := by extra


example {n : ℕ} (hn : 2 ≤ n) : (3:ℤ) ^ n ≥ 2 ^ n + 5 := by
  induction_from_starting_point n, hn with k hk IH
  · -- base case
    numbers
  · -- inductive step
    calc (3:ℤ) ^ (k + 1) = 2 * 3 ^ k + 3 ^ k := by ring
      _ ≥ 2 * (2 ^ k + 5) + 3 ^ k := by rel [IH]
      _ = 2 ^ (k + 1) + 5 + (5 + 3 ^ k) := by ring
      _ ≥ 2 ^ (k + 1) + 5 := by extra


example : forall_sufficiently_large n : ℕ, 2 ^ n ≥ n ^ 2 := by
  dsimp
  use 4
  intro n hn
  induction_from_starting_point n, hn with k hk IH
  · -- base case
    numbers
  · -- inductive step
    calc
      2 ^ (k + 1) = 2^k * 2 := by ring
      _ >= k^2 * 2 := by rel[IH]
      _ = k^2 + k*k := by ring
      _ >= k^2 + 4*k := by rel[hk]
      _ = k^2 + 2*k + 2*k := by ring
      _ >= k^2 + 2*k + 2*4 := by rel[hk]
      _ >= k^2 + 2*k + 1 := by norm_num
      _ = (k + 1)^2 := by ring


/-! # Exercises -/


example (n : ℕ) : 3 ^ n ≥ n ^ 2 + n + 1 := by
  simple_induction n with k IH
  . numbers
  -- have 3^k ≥ k^2 + k + 1
  . calc
      3 ^ (k + 1) = 3^k * 3 := by ring
      _ ≥ (k^2 + k + 1) * 3 := by rel[IH]
      _ = (k^2 + 2*k + 1) + (k+1) + 1 + 2*k^2 := by ring
      _ ≥ (k^2 + 2*k + 1) + (k+1) + 1 := by norm_num
      _ = (k + 1) ^ 2 + (k + 1) + 1 := by ring

example {a : ℝ} (ha : -1 ≤ a) (n : ℕ) : (1 + a) ^ n ≥ 1 + n * a := by
  simple_induction n with k IH
  . norm_num
  . have h0: 1+a >= 0 := by {
      calc
        1+a >= 1 + -1 := by rel[ha]
        _ = 0 := by ring
    }

    calc
    (1 + a) ^ (k + 1)
    _ = (1+a)^(k+1) := rfl
    _ = (1+a)^k * (1+a) := by ring
    _ >= (1 + k*a) * (1+a) := by rel[IH, ha]
    _ = k*a + k*a^2 + (1+a) := by ring
    _ >= k*a + (1 + a) := by extra
    _ = 1 + (k + 1) * a := by ring

example (n : ℕ) : 5 ^ n ≡ 1 [ZMOD 8] ∨ 5 ^ n ≡ 5 [ZMOD 8] := by
  simple_induction n with k IH
  . left; norm_num
  . cases IH with
    | inl h1 =>
      right; calc
        5^(k + 1) = 5^k * 5 := by ring
        _ ≡ 1 * 5 [ZMOD 8] := by rel[h1]
    | inr h5 =>
      left; calc
        5 ^ (k + 1) = 5^k * 5 := by ring
        _ ≡ 5 * 5 [ZMOD 8] := by rel[h5]
        _ = 1 + 8*3 := by ring
        _ ≡ 1 [ZMOD 8] := by extra

example (n : ℕ) : 6 ^ n ≡ 1 [ZMOD 7] ∨ 6 ^ n ≡ 6 [ZMOD 7] := by
  simple_induction n with k IH
  . left; norm_num
  . cases IH with
    | inl h1 =>
      right; calc
        6^(k + 1) = 6^k * 6 := by ring
        _ ≡ 1 * 6 [ZMOD 7] := by rel[h1]
    | inr h6 =>
      left; calc
        6 ^ (k + 1) = 6^k * 6 := by ring
        _ ≡ 6 * 6 [ZMOD 7] := by rel[h6]
        _ = 1 + 7*5 := by ring
        _ ≡ 1 [ZMOD 7] := by extra

example (n : ℕ) :
    4 ^ n ≡ 1 [ZMOD 7] ∨ 4 ^ n ≡ 2 [ZMOD 7] ∨ 4 ^ n ≡ 4 [ZMOD 7] := by
  simple_induction n with k IH
  . left; norm_num
  . match IH with
    | Or.inl h1 =>
      right; right
      calc
        4^(k + 1) = 4^k * 4 := by ring
        _ ≡ 1 * 4 [ZMOD 7] := by rel[h1]
        _ ≡ 4 [ZMOD 7] := by norm_num
    | Or.inr (Or.inl h2) =>
      left
      calc
        4^(k + 1) = 4^k * 4 := by ring
        _ ≡ 2 * 4 [ZMOD 7] := by rel[h2]
        _ = 1 + 7 * 1 := by ring
        _ ≡ 1 [ZMOD 7] := by extra
    | Or.inr (Or.inr h4) =>
      right; left
      calc
        4^(k + 1) = 4^k * 4 := by ring
        _ ≡ 4 * 4 [ZMOD 7] := by rel[h4]
        _ = 2 + 7 * 2 := by ring
        _ ≡ 2 [ZMOD 7] := by extra

example : forall_sufficiently_large n : ℕ, (3:ℤ) ^ n ≥ 2 ^ n + 100 := by
  dsimp
  use 5
  intro n hn
  induction_from_starting_point n, hn with k hk IH
  . norm_num
  . calc
    (3:ℤ) ^ (k + 1)
    _ = 3^k * 3 := by ring
    _ >= (2^k + 100) * 3 := by rel[IH]
    _ = 2^k * 2 + 100 + (2^k + 2*100) := by ring
    _ >= 2^k * 2 + 100 := by extra
    _ = 2 ^ (k + 1) + 100 := by ring

example : forall_sufficiently_large n : ℕ, 2 ^ n ≥ n ^ 2 + 4 := by
  dsimp
  use 5
  intro n hn
  induction_from_starting_point n, hn with k hk IH
  . norm_num
  .
    calc
    2 ^ (k + 1) = 2^k * 2 := by ring
    _ >= (k^2 + 4) * 2 := by rel[IH]
    _ = k^2 + k*k + 8 := by ring
    _ >= k^2 + 5*k + 8 := by rel[hk]
    _ = k^2 + 2*k + 3*k + 8 := by ring
    _ >= k^2 + 2*k + 3*5 + 8 := by rel[hk]
    _ >= k^2 + 2*k + 5 := by norm_num
    _ = (k + 1) ^ 2 + 4 := by ring

example : forall_sufficiently_large n : ℕ, 2 ^ n ≥ n ^ 3 := by
  dsimp
  use 10
  intro n hn
  induction_from_starting_point n, hn with k hk IH
  . norm_num
  .
    calc
    2 ^ (k + 1) = 2^k * 2 := by ring
    _ >= (k^3) * 2 := by rel[IH]
    _ = k^3 + k*k^2 := by ring
    _ >= k^3 + 10*k^2 := by rel[hk]
    _ = k^3 + 3*k^2 + 7*k*k := by ring
    _ >= k^3 + 3*k^2 + 7*10*k := by rel[hk]
    _ = k^3 + 3*k^2 + 3*k + 67*k := by ring
    _ >= k^3 + 3*k^2 + 3*k + 67*10 := by rel[hk]
    _ >= k^3 + 3*k^2 + 3*k + 1 := by norm_num
    _ = (k + 1) ^ 3 := by ring

theorem Odd.pow {a : ℕ} (ha : Odd a) (n : ℕ) : Odd (a ^ n) := by
  simple_induction n with k IH
  . norm_num; use 0; numbers
  . 
    obtain ⟨ka, hka⟩ := ha
    obtain ⟨ki, hki⟩ := IH
    use 2*ki*ka + ki + ka
    calc
      a^(k + 1) = a^k * a := by ring
      _ = (2*ki + 1) * (2*ka + 1) := by rw[hki, hka]
      _ = 2*(2*ki*ka + ki + ka) + 1 := by ring

-- could solve with 2 inductions though
-- modified to be on Z, because fuck this book's operations on Nats
theorem Int.even_of_pow_even {a : ℤ} {n: ℕ} (ha : Int.Even (a ^ n)) : Int.Even a := by
  dsimp[Int.Even] at *
  mod_cases hm: a % 2
  . obtain ⟨k, hk⟩ := hm
    have: a = 2*k := by addarith[hk]
    use k
    exact this
  . 
    have:= zmod_pow hm n
    have hn:=
    calc
      a^n ≡ 1^n [ZMOD 2] := by rel[this]
      _ = 1 := by ring
    obtain ⟨k, hk⟩ := hn
    have: Int.Odd (a^n) := by {
      dsimp[Int.Odd]
      use k
      addarith[hk]
    }
    rw[Int.odd_iff_not_even] at this
    contradiction
