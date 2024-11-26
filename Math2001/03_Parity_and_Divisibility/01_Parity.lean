/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Library.Basic

math2001_init

open Int


example : Int.Odd (7 : ℤ) := by
  dsimp [Int.Odd]
  use 3
  numbers


example : Int.Odd (-3 : ℤ) := by
  dsimp [Int.Odd]
  use -2
  numbers

example {n : ℤ} (hn : Int.Odd n) : Int.Odd (3 * n + 2) := by
  dsimp [Int.Odd] at *
  obtain ⟨k, hk⟩ := hn
  use 3 * k + 2
  calc
    3 * n + 2 = 3 * (2 * k + 1) + 2 := by rw [hk]
    _ = 2 * (3 * k + 2) + 1 := by ring


example {n : ℤ} (hn : Int.Odd n) : Int.Odd (7 * n - 4) := by
  dsimp [Int.Odd] at *
  obtain ⟨k, hk⟩ := hn
  use 7*k + 1
  calc
    7 * n - 4 = 7 * (2*k + 1) - 4 := by rw[hk]
    _ = 2 * (7 * k + 1) + 1 := by ring

example {x y : ℤ} (hx : Int.Odd x) (hy : Int.Odd y) : Int.Odd (x + y + 1) := by
  obtain ⟨a, ha⟩ := hx
  obtain ⟨b, hb⟩ := hy
  use a + b + 1
  calc
    x + y + 1 = 2 * a + 1 + (2 * b + 1) + 1 := by rw [ha, hb]
    _ = 2 * (a + b + 1) + 1 := by ring


example {x y : ℤ} (hx : Int.Odd x) (hy : Int.Odd y) : Int.Odd (x * y + 2 * y) := by
  dsimp [Int.Odd] at *
  obtain ⟨kx, hx⟩ := hx
  obtain ⟨ky, hy⟩ := hy
  use 2*kx*ky + kx + 3*ky + 1
  calc
    x * y + 2*y = (2*kx + 1) * (2*ky + 1) + 2*(2*ky + 1) := by rw[hx, hy]
    _ = 4*kx*ky + 2*kx + 2*ky + 4*ky + 1 + 2 := by ring
    _ = 2 * (2 * kx * ky + kx + 3 * ky + 1) + 1 := by ring

example {m : ℤ} (hm : Int.Odd m) : Int.Even (3 * m - 5) := by
  dsimp[Int.Odd] at *
  dsimp[Int.Even] at *
  obtain ⟨km, hm⟩ := hm
  use 3*km - 1
  calc
    3*m - 5 = 3*(2*km + 1) - 5 := by rw[hm]
    _ = 2 * (3*km - 1) := by ring

example {n : ℤ} (hn : Int.Even n) : Int.Odd (n ^ 2 + 2 * n - 5) := by
  dsimp[Int.Odd] at *
  dsimp[Int.Even] at *
  obtain ⟨kn, hn⟩ := hn
  use 2*kn^2 + 2*kn - 3
  calc
    n^2 + 2*n - 5 = (2*kn)^2 + 2*(2*kn) - 5 := by rw[hn]
    _ = 2*(2*kn^2 + 2*kn - 3) + 1 := by ring

example (n : ℤ) : Int.Even (n^2 + n + 4) := by
  match (Int.even_or_odd n) with
  | Or.inl heven =>
    obtain ⟨x, hx⟩ := heven
    use 2 * x ^ 2 + x + 2
    calc
      n ^ 2 + n + 4 = (2 * x) ^ 2 + 2 * x + 4 := by rw [hx]
      _ = 2 * (2 * x ^ 2 + x + 2) := by ring
  | Or.inr hodd =>
    obtain ⟨x, hx⟩ := hodd
    use 2 * x ^ 2 + 3 * x + 3
    calc
      n ^ 2 + n + 4 = (2 * x + 1) ^ 2 + (2 * x + 1) + 4 := by rw [hx]
      _ = 2 * (2 * x ^ 2 + 3 * x + 3) := by ring

/-! # Exercises -/


example : Int.Odd (-9 : ℤ) := by
  use -5
  numbers

example : Int.Even (26 : ℤ) := by
  use 13
  numbers

example {m n : ℤ} (hm : Int.Odd m) (hn : Int.Even n) : Int.Odd (n + m) := by
  dsimp[Int.Odd] at *
  dsimp[Int.Even] at *
  obtain ⟨km, hm⟩ := hm
  obtain ⟨kn, hn⟩ := hn
  use kn + km
  calc
    n + m = 2*kn + (2*km + 1) := by rw[hn, hm]
    _ = 2*(kn + km) + 1 := by ring

example {p q : ℤ} (hp : Int.Odd p) (hq : Int.Even q) : Int.Odd (p - q - 4) := by
  obtain ⟨kp, hp⟩ := hp
  obtain ⟨kq, hq⟩ := hq
  use kp - kq - 2
  calc
    p - q - 4 = (2*kp + 1) - 2*kq - 4 := by rw[hp, hq]
    _ = 2*(kp - kq - 2) + 1 := by ring

example {a b : ℤ} (ha : Int.Even a) (hb : Int.Odd b) : Int.Even (3 * a + b - 3) := by
  obtain ⟨ka, ha⟩ := ha
  obtain ⟨kb, hb⟩ := hb
  use 3*ka + kb - 1
  calc
    3*a + b - 3 = 3*(2*ka) + (2*kb + 1) - 3 := by rw[ha, hb]
    _ = 2*(3*ka + kb - 1) := by ring

example {r s : ℤ} (hr : Int.Odd r) (hs : Int.Odd s) : Int.Even (3 * r - 5 * s) := by
  obtain ⟨kr, hr⟩ := hr
  obtain ⟨ks, hs⟩ := hs
  use 3*kr - 5*ks - 1
  calc
    3*r - 5*s = 3*(2*kr + 1) - 5*(2*ks + 1) := by rw[hr, hs]  
    _ = 2*(3*kr - 5*ks - 1) := by ring

example {x : ℤ} (hx : Int.Odd x) : Int.Odd (x ^ 3) := by
  dsimp[Int.Odd] at *
  obtain ⟨kx, hx⟩ := hx
  use 4*kx^3 + 6*kx^2 + 3*kx
  calc
    x^3 = (2*kx + 1)^3 := by rw[hx]
    _ = 8*kx^3 + 12*kx^2 + 6*kx + 1 := by ring
    _ = 2*(4*kx^3 + 6*kx^2 + 3*kx) + 1 := by ring

example {n : ℤ} (hn : Int.Odd n) : Int.Even (n ^ 2 - 3 * n + 2) := by
  obtain ⟨kn, hn⟩ := hn
  use 2*kn^2 - kn
  calc
    n^2 - 3*n + 2 = (2*kn + 1)^2 - 3*(2*kn + 1) + 2 := by rw[hn]
    _ = 4*kn^2 + 4*kn + 1 - 6*kn - 3 + 2 := by ring
    _ = 2*(2*kn^2 - kn) := by ring

example {a : ℤ} (ha : Int.Odd a) : Int.Odd (a ^ 2 + 2 * a - 4) := by
  obtain ⟨ka, ha⟩ := ha
  use 2*ka^2 + 4*ka - 1
  calc
    a^2 + 2*a - 4 = (2*ka + 1)^2 + 2*(2*ka + 1) - 4 := by rw[ha]
    _ = 4*ka^2 + 4*ka + 1 + 4*ka + 2 - 4 := by ring
    _ = 2*(2*ka^2 + 4*ka - 1) + 1 := by ring

example {p : ℤ} (hp : Int.Odd p) : Int.Odd (p ^ 2 + 3 * p - 5) := by
  obtain ⟨kp, hp⟩ := hp
  use 2*kp^2 + 5*kp - 1
  calc
    p^2 + 3*p - 5 = (2*kp + 1)^2 + 3*(2*kp + 1) - 5 := by rw[hp]
    _ = 4*kp^2 + 4*kp + 1 + 6*kp + 3 - 5 := by ring
    _ = 2*(2*kp^2 + 5*kp - 1) + 1 := by ring

example {x y : ℤ} (hx : Int.Odd x) (hy : Int.Odd y) : Int.Odd (x * y) := by
  obtain ⟨kx, hx⟩ := hx
  obtain ⟨ky, hy⟩ := hy
  use 2*kx*ky + kx + ky
  calc
    x * y = (2*kx + 1) * (2*ky + 1) := by rw[hx, hy]
    _ = 4*kx*ky + 2*kx + 2*ky + 1 := by ring
    _ = 2*(2*kx*ky + kx + ky) + 1 := by ring 

example (n : ℤ) : Int.Odd (3 * n ^ 2 + 3 * n - 1) := by
  match (Int.even_or_odd n) with
  | Or.inl heven =>
    obtain ⟨k, hk⟩ := heven
    use 6*k^2 + 3*k - 1
    calc
      3*n^2 + 3*n - 1 = 3*(2*k)^2 + 3*(2*k) - 1 := by rw[hk]
      _ = 2 * (6*k^2 + 3*k - 1) + 1 := by ring
  | Or.inr hodd =>
    obtain ⟨k, hk⟩ := hodd
    use 6*k^2 + 9*k + 2
    calc
      3*n^2 + 3*n - 1 = 3*(2*k + 1)^2 + 3*(2*k + 1) - 1 := by rw[hk]
      _ = 2*(6*k^2 + 9*k + 2) + 1 := by ring

example (n : ℤ) : ∃ m ≥ n, Int.Odd m := by
  match (Int.even_or_odd n) with
  | Or.inl heven =>
    obtain ⟨ke, hk⟩ := heven
    use n + 1
    constructor
    . extra
    . rw[hk]
      use ke
      ring
  | Or.inr hodd =>
    obtain ⟨ko, hk⟩ := hodd
    use n
    constructor
    . extra
    . rw[hk]
      use ko
      ring

lemma even_plus_from_minus (a b: ℤ) (he: Int.Even (a - b)): Int.Even (a + b) := by
  obtain ⟨k, hk⟩ := he
  use k+b
  calc
    a + b = (a - b) + 2*b := by ring
    _ = 2*k + 2*b := by rw[hk]
    _ = 2*(k + b) := by ring

lemma ee (a b : ℤ) (hae : Int.Even a) (hbe : Int.Even b) : Int.Even (a - b) := by
  obtain ⟨ka, hae⟩ := hae
  obtain ⟨kb, hbe⟩ := hbe
  use ka - kb
  calc
    a - b = (2 * ka) - (2 * kb) := by rw [hae, hbe]
    _ = 2 * (ka - kb) := by ring

lemma oo (a b : ℤ) (hao : Int.Odd a) (hbo : Int.Odd b) : Int.Even (a - b) := by
  obtain ⟨ka, hao⟩ := hao
  obtain ⟨kb, hbo⟩ := hbo
  use ka - kb
  calc
    a - b = (2 * ka + 1) - (2 * kb + 1) := by rw [hao, hbo]
    _ = 2 * (ka - kb) := by ring


example (a b c : ℤ) : Int.Even (a - b) ∨ Int.Even (a + c) ∨ Int.Even (b - c) := by
  match (Int.even_or_odd a), (Int.even_or_odd b), (Int.even_or_odd c) with
  | Or.inl hae, Or.inl hbe, Or.inl hce =>
    right; left
    apply even_plus_from_minus
    exact ee a c hae hce
  | Or.inl hae, Or.inl hbe, Or.inr hco =>
    left
    exact ee a b hae hbe
  | Or.inl hae, Or.inr hbo, Or.inl hce =>
    right; left
    apply even_plus_from_minus
    exact ee a c hae hce
  | Or.inl hae, Or.inr hbo, Or.inr hco =>
    right; right
    exact oo b c hbo hco
  | Or.inr hao, Or.inl hbe, Or.inl hce =>
    right; right
    exact ee b c hbe hce
  | Or.inr hao, Or.inl hbe, Or.inr hco =>
    right; left
    apply even_plus_from_minus
    exact oo a c hao hco
  | Or.inr hao, Or.inr hbo, Or.inl hce =>
    left
    exact oo a b hao hbo
  | Or.inr hao, Or.inr hbo, Or.inr hco =>
    right; right
    exact oo b c hbo hco
