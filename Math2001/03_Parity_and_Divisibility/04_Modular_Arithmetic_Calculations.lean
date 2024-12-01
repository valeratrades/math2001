/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Library.Basic
import Library.Tactic.ModEq

math2001_init


example {a b : ℤ} (ha : a ≡ 2 [ZMOD 4]) :
    a * b ^ 2 + a ^ 2 * b + 3 * a ≡ 2 * b ^ 2 + 2 ^ 2 * b + 3 * 2 [ZMOD 4] := by
  rel [ha]


example {a b : ℤ} (ha : a ≡ 4 [ZMOD 5]) (hb : b ≡ 3 [ZMOD 5]) :
    a * b + b ^ 3 + 3 ≡ 2 [ZMOD 5] :=
  calc
    a * b + b ^ 3 + 3 ≡ 4 * b + b ^ 3 + 3 [ZMOD 5] := by rel [ha]
    _ ≡ 4 * 3 + 3 ^ 3 + 3 [ZMOD 5] := by rel [hb]
    _ = 2 + 5 * 8 := by numbers --? is this equivalent to a `use` statement?
    _ ≡ 2 [ZMOD 5] := by extra


example : ∃ a : ℤ, 6 * a ≡ 4 [ZMOD 11] := by
  use 8
  calc
    (6:ℤ) * 8 = 4 + 4 * 11 := by numbers
    _ ≡ 4 [ZMOD 11] := by extra


example {x : ℤ} : x ^ 3 ≡ x [ZMOD 3] := by
  mod_cases hx : x % 3
  calc
    x ^ 3 ≡ 0 ^ 3 [ZMOD 3] := by rel [hx]
    _ = 0 := by numbers
    _ ≡ x [ZMOD 3] := by rel [hx]
  calc
    x ^ 3 ≡ 1 ^ 3 [ZMOD 3] := by rel [hx]
    _ = 1 := by numbers
    _ ≡ x [ZMOD 3] := by rel [hx]
  calc
    x ^ 3 ≡ 2 ^ 3 [ZMOD 3] := by rel [hx]
    _ = 2 + 3 * 2 := by numbers
    _ ≡ 2 [ZMOD 3] := by extra
    _ ≡ x [ZMOD 3] := by rel [hx]

/-! # Exercises -/

example {n : ℤ} (hn : n ≡ 1 [ZMOD 3]) : n ^ 3 + 7 * n ≡ 2 [ZMOD 3] := by
  calc
    n^3 + 7*n ≡ 1^3 + 7*1 [ZMOD 3] := by rel[hn]
    _ = 2 + 2*3 := by numbers -- I think we can do this because transitivity
    _ ≡ 2 [ZMOD 3] := by extra

example {a : ℤ} (ha : a ≡ 3 [ZMOD 4]) :
    a ^ 3 + 4 * a ^ 2 + 2 ≡ 1 [ZMOD 4] := by
  calc
    a^3 + 4*a^2 + 2 ≡ 3^3 + 4*3^2 + 2 [ZMOD 4] := by rel[ha]
    _ = 4*16 + 1 := by numbers
    _ ≡ 1 [ZMOD 4] := by extra

example (a b : ℤ) : (a + b) ^ 3 ≡ a ^ 3 + b ^ 3 [ZMOD 3] := by
  dsimp [Int.ModEq] at *
  calc
    (a + b)^3 = (a^3 + b^3) + 3*(a^2*b + a*b^2) := by ring
    _ ≡ a^3 + b^3 [ZMOD 3] := by extra

example : ∃ a : ℤ, 4 * a ≡ 1 [ZMOD 7] := by
  use 9
  calc
    4*9 = 1 + 7*5 := by ring
    _ ≡ 1 [ZMOD 7] := by extra

example : ∃ k : ℤ, 5 * k ≡ 6 [ZMOD 8] := by
  use 6
  calc
    5*6 = 6 + 8*3 := by ring
    _ ≡ 6 [ZMOD 8] := by extra

example (n : ℤ) : 5 * n ^ 2 + 3 * n + 7 ≡ 1 [ZMOD 2] := by
  mod_cases hn: n%2
  . calc
    5*n^2 + 3*n + 7 ≡ 5*0^2 + 3*0 + 7 [ZMOD 2] := by rel[hn]
    _ = 1 + 2*3 := by numbers
    _ ≡ 1 [ZMOD 2] := by extra
  . calc
    5*n^2 + 3*n + 7 ≡ 5*1^2 + 3*1 + 7 [ZMOD 2] := by rel[hn]
    _ = 1 + 2*7 := by numbers
    _ ≡ 1 [ZMOD 2] := by extra

example {x : ℤ} : x ^ 5 ≡ x [ZMOD 5] := by
  mod_cases hx: x%5
  . calc
    x^5 ≡ 0^5 [ZMOD 5] := by rel[hx]
    _ = 0 := by numbers
    _ ≡ x [ZMOD 5] := by rel[hx]
  . calc
    x^5 ≡ 1^5 [ZMOD 5] := by rel[hx]
    _ = 1 := by numbers
    _ ≡ x [ZMOD 5] := by rel[hx]
  . calc
    x^5 ≡ 2^5 [ZMOD 5] := by rel[hx]
    _ = 2 + 5*6 := by numbers
    _ ≡ 2 [ZMOD 5] := by extra
    _ ≡ x [ZMOD 5] := by rel[hx]
  . calc
    x^5 ≡ 3^5 [ZMOD 5] := by rel[hx]
    _ = 3 + 5*48 := by numbers
    _ ≡ 3 [ZMOD 5] := by extra
    _ ≡ x [ZMOD 5] := by rel[hx]
  . calc
    x^5 ≡ 4^5 [ZMOD 5] := by rel[hx]
    _ = 4 + 5*204 := by numbers
    _ ≡ 4 [ZMOD 5] := by extra
    _ ≡ x [ZMOD 5] := by rel[hx]
