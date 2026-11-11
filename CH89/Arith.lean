/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Data.Real.Sqrt

/-!
# The parameter inequalities of Theorem 2

With `r = 2n − 1 − d` and `(d + n)² ≥ 7 n²` (that is, `d ≥ (√7 − 1) n`):
* `five_le`: if `r (r − 1) ≤ (2n − 1) p` (Lemma 3) then `5 n ≤ 3 d + p`, by the identity
  `r (r − 1) − (2n − 1)(5n − 3d − 1) = (d + n)² − 7 n² + n + 1`;
* `three_le`: `3 n + 2 ≤ 2 d` as soon as `n ≥ 4`;
* `four_le`: `n ≥ 4` unless `d = 2n − 1`.
* `seven_le_of_real`: `(√7 − 1)/2 · 2n ≤ d` gives `7 n² ≤ (d + n)²`.
-/

@[expose] public section

namespace CH89

theorem five_le {n d p : ℕ} (hn : 1 ≤ n) (hd : d + 1 ≤ 2 * n) (h7 : 7 * n ^ 2 ≤ (d + n) ^ 2)
    (hp : (2 * n - 1 - d) * (2 * n - 1 - d - 1) ≤ (2 * n - 1) * p) : 5 * n ≤ 3 * d + p := by
  by_contra hlt
  push_neg at hlt
  rcases Nat.lt_or_ge d (2 * n - 1) with hr | hr
  · -- `r ≥ 1`
    obtain ⟨r, hr'⟩ : ∃ r, r + 1 = 2 * n - 1 - d := ⟨2 * n - 1 - d - 1, by omega⟩
    rw [← hr', show r + 1 - 1 = r by omega] at hp
    have hzr : ((r : ℤ) + 1) = 2 * n - 1 - d := by omega
    have hp' : ((r : ℤ) + 1) * r ≤ (2 * n - 1) * p := by
      have h0 : (((r + 1) * r : ℕ) : ℤ) ≤ ((((2 * n - 1 : ℕ)) * p : ℕ) : ℤ) := by exact_mod_cast hp
      push_cast [Nat.cast_sub (show 1 ≤ 2 * n by omega)] at h0
      exact h0
    have h7' : (7 : ℤ) * n ^ 2 ≤ ((d : ℤ) + n) ^ 2 := by exact_mod_cast h7
    have hlt' : (p : ℤ) ≤ 5 * n - 3 * d - 1 := by omega
    have hpos : (0 : ℤ) ≤ 2 * n - 1 := by omega
    have h1 : ((2 : ℤ) * n - 1) * p ≤ (2 * n - 1) * (5 * n - 3 * d - 1) :=
      mul_le_mul_of_nonneg_left hlt' hpos
    have hid : ((r : ℤ) + 1) * r - (2 * n - 1) * (5 * n - 3 * d - 1) =
        ((d : ℤ) + n) ^ 2 - 7 * n ^ 2 + n + 1 := by
      have : (r : ℤ) = 2 * n - 2 - d := by omega
      rw [this]
      ring
    nlinarith
  · -- `r = 0`
    have hd' : d = 2 * n - 1 := by omega
    subst hd'
    rcases Nat.lt_or_ge n 3 with h3 | h3
    · interval_cases n <;> simp_all
    · omega

theorem three_le {n d : ℕ} (hn : 4 ≤ n) (h7 : 7 * n ^ 2 ≤ (d + n) ^ 2) : 3 * n + 2 ≤ 2 * d := by
  by_contra hlt
  push_neg at hlt
  have h1 : 2 * (d + n) ≤ 5 * n + 1 := by omega
  have h2 : (2 * (d + n)) ^ 2 ≤ (5 * n + 1) ^ 2 := Nat.pow_le_pow_left h1 2
  nlinarith

theorem four_le {n d : ℕ} (hd : d + 2 ≤ 2 * n) (h7 : 7 * n ^ 2 ≤ (d + n) ^ 2) : 4 ≤ n := by
  by_contra h
  push_neg at h
  have hd4 : d ≤ 4 := by omega
  interval_cases n <;> interval_cases d <;> simp_all

theorem seven_le_of_real {n d : ℕ} (h : (Real.sqrt 7 - 1) / 2 * ((2 * n : ℕ) : ℝ) ≤ d) :
    7 * n ^ 2 ≤ (d + n) ^ 2 := by
  have h1 : Real.sqrt 7 * n ≤ (d : ℝ) + n := by push_cast at h; nlinarith
  have h0 : (0 : ℝ) ≤ Real.sqrt 7 * n := by positivity
  have h2 : (Real.sqrt 7 * n) ^ 2 ≤ ((d : ℝ) + n) ^ 2 := pow_le_pow_left₀ h0 h1 2
  rw [mul_pow, Real.sq_sqrt (by norm_num)] at h2
  exact_mod_cast h2

end CH89
