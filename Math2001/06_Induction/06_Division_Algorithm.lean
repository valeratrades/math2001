/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Library.Basic
import Library.Theory.ModEq.Defs

math2001_init


def fmod (n d : ℤ) : ℤ :=
  if n * d < 0 then
    fmod (n + d) d
  else if h2 : 0 < d * (n - d) then
    fmod (n - d) d
  else if h3 : n = d then
    0
  else
    n
termination_by _ n d => 2 * n - d

def fdiv (n d : ℤ) : ℤ :=
  if n * d < 0 then
    fdiv (n + d) d - 1
  else if 0 < d * (n - d) then
    fdiv (n - d) d + 1
  else if h3 : n = d then
    1
  else
    0
termination_by _ n d => 2 * n - d


#eval fmod 11 4 -- infoview displays `3`
#eval fdiv 11 4 -- infoview displays `2`


theorem fmod_add_fdiv (n d : ℤ) : fmod n d + d * fdiv n d = n := by
  rw [fdiv, fmod]
  split_ifs with h1 h2 h3 <;> push_neg at *
  · -- case `n * d < 0`
    have IH := fmod_add_fdiv (n + d) d -- inductive hypothesis
    calc fmod (n + d) d + d * (fdiv (n + d) d - 1)
        = (fmod (n + d) d + d * fdiv (n + d) d) - d := by ring
      _ = (n + d) - d := by rw [IH]
      _ = n := by ring
  · -- case `0 < d * (n - d)`
    have IH := fmod_add_fdiv (n - d) d -- inductive hypothesis
    calc fmod (n - d) d + d * (fdiv (n - d) d + 1)
        = (fmod (n - d) d + d * fdiv (n - d) d) + d := by ring
        _ = n := by addarith [IH]
  · -- case `n = d`
    calc 0 + d * 1 = d := by ring
      _ = n := by rw [h3]
  · -- last case
    ring
termination_by _ n d => 2 * n - d



theorem fmod_nonneg_of_pos (n : ℤ) {d : ℤ} (hd : 0 < d) : 0 ≤ fmod n d := by
  rw [fmod]
  split_ifs with h1 h2 h3 <;> push_neg at *
  · -- case `n * d < 0`
    have IH := fmod_nonneg_of_pos (n + d) hd -- inductive hypothesis
    apply IH
  · -- case `0 < d * (n - d)`
    have IH := fmod_nonneg_of_pos (n - d) hd -- inductive hypothesis
    apply IH
  · -- case `n = d`
    extra
  · -- last case
    cancel d at h1
termination_by _ n d hd => 2 * n - d


theorem fmod_lt_of_pos (n : ℤ) {d : ℤ} (hd : 0 < d) : fmod n d < d := by
  rw [fmod]
  split_ifs with h1 h2 h3 <;> push_neg at *
  · -- case `n * d < 0`
    have IH := fmod_lt_of_pos (n + d) hd -- inductive hypothesis
    apply IH
  · -- case `0 < d * (n - d)`
    have IH := fmod_lt_of_pos (n - d) hd -- inductive hypothesis
    apply IH
  · -- case `n = d`
    apply hd
  · -- last case
    have h4 :=
    calc 0 ≤ - d * (n - d) := by addarith [h2]
      _ = d * (d - n) := by ring
    cancel d at h4
    apply lt_of_le_of_ne
    · addarith [h4]
    · apply h3
termination_by _ n d hd => 2 * n - d


example (a b : ℤ) (h : 0 < b) : ∃ r : ℤ, 0 ≤ r ∧ r < b ∧ a ≡ r [ZMOD b] := by
  use fmod a b
  constructor
  · apply fmod_nonneg_of_pos a h
  constructor
  · apply fmod_lt_of_pos a h
  · use fdiv a b
    have Hab : fmod a b + b * fdiv a b = a := fmod_add_fdiv a b
    addarith [Hab]

/-! # Exercises -/


theorem lt_fmod_of_neg (n : ℤ) {d : ℤ} (hd : d < 0) : d < fmod n d := by
  rw[fmod]
  split_ifs with h1 h2 h3 <;> push_neg at *
  . -- case  n * d < 0
    have IH:= lt_fmod_of_neg (n + d) hd
    apply IH
  . -- case 0 ≤ n * d
    have IH:= lt_fmod_of_neg (n - d) hd
    apply IH
  . -- case 0 ≤ n * d
    apply hd
  . -- case _
    have h4: n - d >= 0 := by {
      have:=
        calc -d * 0
        _ = 0 := by ring
        _ ≥ d * (n - d) := by addarith[h2]
        _ = -d * (d - n) := by ring
      have hdpos: -d > 0 := by addarith[hd]
      cancel -d at this
      addarith[this]
    }
    have hge: n >= d := by addarith[h4]
    match (lt_or_eq_of_le hge) with
    | Or.inl hlt => exact hlt
    | Or.inr heq =>
      have: n = d := by addarith[heq]
      contradiction
termination_by _ n d hd => 2 * n - d

--TODO: move some args to be implicit (theoretically should be able to have both d and m be inferred)
lemma fdiv_is_q (z d m q: ℤ) (hm: 0 <= m ∧ m < d ∧ z - m = d * q /-z ≡ m [ZMOD d]-/): fdiv z d = q := by {
  rw[fdiv]
  split_ifs with h1 h2 h3 <;> push_neg at *
  . -- case z * d < 0
    obtain ⟨h0, hlt, hmq⟩ := hm
    have hcond:=
    calc (z + d) - m
      _ = (z - m) + d := by ring
      _ = d * q + d := by rw[hmq]
      _ = d * (q + 1) := by ring
    have: 0 ≤ m ∧ m < d ∧ (z + d) - m = d * (q+1) := ⟨h0, ⟨hlt, hcond⟩⟩
    have IH:= fdiv_is_q (z + d) d m (q+1) (this)
    addarith[IH]
  . -- case 0 < d * (z - d)
    obtain ⟨h0, hlt, hmq⟩ := hm
    have hcond:=
    calc (z - d) - m
      _ = (z - m) - d := by ring
      _ = d * q - d := by rw[hmq]
      _ = d * (q - 1) := by ring
    have: 0 ≤ m ∧ m < d ∧ (z - d) - m = d * (q-1) := ⟨h0, ⟨hlt, hcond⟩⟩
    have IH:= fdiv_is_q (z - d) d m (q-1) (this)
    addarith[IH]
  . -- case z = d
    -- get contra if m!=0
    obtain ⟨h0, hlt, hmq⟩ := hm
    match (eq_or_gt_of_le h0) with
    | Or.inl hm0 =>
      have zpos:=
      calc z
        _ = d := by rw[h3]
        _ > m := by rel[hlt]
        _ = 0 := by rw[hm0]
      have:=
      calc z * 1
        _ = (z - 0) * 1 := by ring
        _ = (z - m) * 1 := by rw[hm0]
        _ = (d * q) * 1 := by rw[hmq]
        _ = (z * q) * 1 := by rw[h3]
        _ = z * q := by ring
      cancel z at this
    | Or.inr hmpos =>
      have: ∃f:ℤ, d*f < z - m ∧ z - m < d*(f+1) := by {
        use 0
        constructor
        . norm_num; calc m
          _ < d := by rel[hlt]
          _ = z := by rw[h3]
        . have: d - m < d := by addarith[hmpos]
          norm_num; calc z - m
          _ = d - m := by rw[h3]
          _ = d - m := by ring
          _ < d := by addarith[hmpos]
      }
      have hnd:= Int.not_dvd_of_exists_lt_and_lt (z - m) d this
      have: d ∣ z - m := by { use q; exact hmq }
      contradiction
  . -- case _
    -- GOAL ⊢ 0 = q
    obtain ⟨h0, hlt, hmq⟩ := hm
    have dpos:=
    calc d
      _ > m := by rel[hlt]
      _ >= 0 := by rel[h0]
    have:=
    calc d * (z - d)
      _ ≤ 0 := by rel[h2]
      _ = d * 0 := by ring
    cancel d at this
    have hzled: z <= d := by addarith[this]
    have hzltd: z < d := by {
      cases (lt_or_eq_of_le hzled) with
      | inl h => exact h
      | inr => contradiction
    }
    clear hzled
    have hzpos: 0 < z := by {
      cases (lt_or_eq_of_le h1) with
      | inl hpos =>
        cancel d at hpos
      | inr hzd0 => 
        have:=
        calc 0 * d
          _ = 0 := by ring
          _ = z * d := by rw[hzd0]
        cancel d at this
        have hmm: -m = d * q :=
        calc -m
          _ = 0 - m := by ring
          _ = z - m := by rw[this]
          _ = d * q := by rw[hmq]

        have: ∃f:ℤ, d*f < -m ∧ -m < d*(f+1) := by {
          use -1
          constructor
          . norm_num; addarith[hlt]
          . norm_num
            cases (lt_or_eq_of_le h0) with
            | inl h => exact h
            | inr h =>
              have:=
              calc d*0
                _ = -0 := by ring
                _ = -(m) := by rw[h]
                _ = d*q := by rw[hmm]
              cancel d at this -- produces 0 = q, which is the goal in matching GOAL comment
              clear hzd0 h1 h2
              sorry -- it's sorry here, but logically I solved it, i either don't know the keyword to return to outside the 2 nested `have` scopes, either lean doesn't have it and I will just imagine it does, because it really really should.
        }
        have hnd:= Int.not_dvd_of_exists_lt_and_lt (-m) d this
        have: d ∣ -m := by { use q; exact hmm }
        contradiction
    }
    
    have hm1lt: -1 < q := by {
      have hlb/-for lower bound-/: z - m > -d :=
      calc (z) - m
        _ > (0) - m := by addarith[hzpos]
        _ = -1 * m := by ring
        _ > -1 * d := by addarith[hlt]
        _ = -d := by ring
      have:=
      calc d * q
        _ = z - m := by addarith[hmq]
        _ > -d := by rel[hlb]
        _ = d * -1 := by ring
      cancel d at this
    }
    have hlt1: q < 1 := by {
      have hub: z - m < d :=
      calc z - m
        _ < d - m := by addarith[hzltd]
        _ <= d - 0 := by addarith[h0]
        _ = d := by ring
      have:=
      calc d * q
        _ = z - m := by addarith[hmq]
        _ < d := by rel[hub]
        _ = d * 1 := by ring
      cancel d at this
    }

    by_contra hqn0
    push_neg at hqn0
    cases (lt_or_gt_of_ne hqn0) with
    | inl hpos =>
      have:=
        calc 1
        _ ≤ q := by addarith[hpos]
        _ < 1 := by rel[hlt1]
      numbers at this
    | inr hneg =>
      have:=
        calc -1
        _ ≥ q := by addarith[hneg]
        _ > -1 := by rel[hm1lt]
      numbers at this
}
termination_by _ z d _ _ hm => 2 * z - d

def T (n : ℤ) : ℤ :=
  if 0 < n then
    T (1 - n) + 2 * n - 1
  else if n < 0 then
    T (-n)
  else
    0
termination_by T n => 3 * n - 1

theorem T_eq (n : ℤ) : T n = n ^ 2 := by
  rw[T]
  split_ifs with h1 h2 <;> push_neg at *
  . have IH:= T_eq (1 - n)
    rw[IH]
    ring
  . have IH:= T_eq (-n)
    rw[IH]
    ring
  . have: n = 0 := LE.le.eq_of_not_lt h1 (by addarith[h2])
    rw[this]
    ring
termination_by _ n => 3 * n - 1

theorem uniqueness (a b : ℤ) (h : 0 < b) {r s : ℤ}
    (hr : 0 ≤ r ∧ r < b ∧ a ≡ r [ZMOD b])
    (hs : 0 ≤ s ∧ s < b ∧ a ≡ s [ZMOD b])
    : r = s := by
  obtain ⟨hr0, hrltb, ⟨qr, hqr⟩⟩ := hr
  obtain ⟨hs0, hsltb, ⟨qs, hqs⟩⟩ := hs
  have hrd:= fdiv_is_q a b r qr ⟨hr0, hrltb, hqr⟩
  have hsd:= fdiv_is_q a b s qs ⟨hs0, hsltb, hqs⟩
  calc r
    _ = -1 * (a - r) + a := by ring
    _ = -1 * (b * qr) + a := by rw[hqr]
    _ = -1 * (b * (fdiv a b)) + a := by rw[hrd]
    _ = -1 * (b * qs) + a := by rw[hsd]
    _ = -1 * (a - s) + a := by rw[hqs]
    _ = s := by ring

example (a b : ℤ) (h : 0 < b) : ∃! r : ℤ, 0 ≤ r ∧ r < b ∧ a ≡ r [ZMOD b] := by
  use fmod a b
  constructor
  .
    apply And.intro
    . exact fmod_nonneg_of_pos a h
    . constructor
      . exact fmod_lt_of_pos a h
      . dsimp[Int.ModEq] at *
        dsimp[(· ∣ · )]
        use fdiv a b
        addarith[fmod_add_fdiv a b]
  . 
    intro m ⟨hm0, hmltb, ⟨qm, hqm⟩⟩
    have hmd:=fdiv_is_q a b m qm ⟨hm0, hmltb, hqm⟩
    have ha:= fmod_add_fdiv a b
    have:= calc fmod a b
      _ = fmod a b + (b * fdiv a b) - (b * fdiv a b) := by ring
      _ = fmod a b + (b * fdiv a b) - (b * qm) := by rw[hmd]
      _ = a - (a - m) := by rw[ha, hqm]
      _ = m := by ring
    addarith[this]
