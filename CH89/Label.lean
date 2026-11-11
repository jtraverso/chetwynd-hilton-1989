/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import OneFactor.Stair
public import CH89.Order
public import CH89.Swap

/-!
# The staircase labelling read off a list

`listStair ℓ m u`: for a list `ℓ` of length `2m + u` (positions `0, …, 2m + u − 1`), the positions
`< m + u` are the right side with index `m − pos`, the others the left side with index
`pos − m − u + 1`; a vertex outside `ℓ` (`v*`) gets the left index `m + 1`. Then `x` is before `y`
in `ℓ` exactly when `x` is uncovered by the staircase class of `v* y` by the article's rules
(`not_cls_of_lt`): `R` before `L`, `r_k` before `r_{k'}` for `k > k'`, `l_j` before `l_a` for
`j < a` (`not_cls_of_LL` is the last rule).
-/

@[expose] public section

namespace CH89

open SimpleGraph Finset OneFactor

variable {V : Type*} [DecidableEq V]

/-- The staircase labelling given by positions in a list. -/
def listStair (ℓ : List V) (m u : ℕ) (hlen : ℓ.length = 2 * m + u) (HS : Finset V)
    (hinj : ∀ a ∈ HS, ∀ b ∈ HS, ℓ.idxOf a = ℓ.idxOf b → a = b) : StairData HS where
  side v := decide (m + u ≤ ℓ.idxOf v)
  idx v := if m + u ≤ ℓ.idxOf v then (ℓ.idxOf v : ℤ) - (m + u) + 1 else (m : ℤ) - ℓ.idxOf v
  t := 1 - u
  m := m
  ht := by omega
  hm := by omega
  hL := fun v _ h => by
    have := List.idxOf_le_length (a := v) (l := ℓ)
    simp only [decide_eq_true_eq] at h
    simp only [if_pos h]; omega
  hR := fun v _ h => by
    simp only [decide_eq_false_iff_not, not_le] at h
    simp only [if_neg (not_le.2 h)]; omega
  injL := fun a ha b hb h1 h2 e => by
    simp only [decide_eq_true_eq] at h1 h2
    simp only [if_pos h1, if_pos h2] at e
    exact hinj a ha b hb (by omega)
  injR := fun a ha b hb h1 h2 e => by
    simp only [decide_eq_false_iff_not, not_le] at h1 h2
    simp only [if_neg (not_le.2 h1), if_neg (not_le.2 h2)] at e
    exact hinj a ha b hb (by omega)

section ListStair

variable {ℓ : List V} {m u : ℕ} {hlen : ℓ.length = 2 * m + u} {HS : Finset V}
  {hinj : ∀ a ∈ HS, ∀ b ∈ HS, ℓ.idxOf a = ℓ.idxOf b → a = b}

theorem listStair_side {v : V} :
    (listStair ℓ m u hlen HS hinj).side v = true ↔ m + u ≤ ℓ.idxOf v := by
  simp [listStair]

theorem listStair_side_false {v : V} :
    (listStair ℓ m u hlen HS hinj).side v = false ↔ ℓ.idxOf v < m + u := by
  simp [listStair]

theorem listStair_idx (v : V) : (listStair ℓ m u hlen HS hinj).idx v =
    if m + u ≤ ℓ.idxOf v then (ℓ.idxOf v : ℤ) - (m + u) + 1 else (m : ℤ) - ℓ.idxOf v := rfl

theorem listStair_m : (listStair ℓ m u hlen HS hinj).m = m := rfl

theorem listStair_q : (listStair ℓ m u hlen HS hinj).q = 2 * m + u := by
  simp only [StairData.q, listStair]; omega

end ListStair

/-- **Left before left.** In the class of `v* y` with `v*` the left vertex of index `m + 1`, a
left vertex `x` of smaller index than `y` is uncovered. -/
theorem not_cls_of_LL {HS : Finset V} (D : StairData HS) (G : SimpleGraph V) {vs y x : V}
    (hvsL : D.side vs = true) (hvsi : D.idx vs = D.m + 1) (hy : D.Eplus G vs y)
    (hxL : D.side x = true) (hyL : D.side y = true) (hlt : D.idx x < D.idx y) :
    x ∉ D.cls G (D.stair vs y) := by
  intro hcls
  obtain ⟨hxH, u, hu, hst⟩ := (StairData.mem_cls _ _).1 hcls
  obtain ⟨-, huH, -, h⟩ := hu
  have hyH := hy.2.1
  have hx' := D.hL x hxH hxL
  have hy' := D.hL y hyH hyL
  have e1 : D.stair vs y = D.idx vs + D.idx y - D.t := by
    simp [StairData.stair, hvsL, hyL]
  rw [e1, hvsi] at hst
  rcases h with ⟨-, h2⟩ | ⟨-, h2, h3⟩ | ⟨h1, -⟩
  · have := D.hL u huH h2
    simp [StairData.stair, hxL, h2] at hst
    omega
  · have := D.hR u huH h2
    simp [StairData.stair, hxL, h2] at hst
    have := D.ht
    omega
  · rw [hxL] at h1; exact absurd h1 (by simp)

/-- **Before in the list means uncovered.** -/
theorem not_cls_of_lt {ℓ : List V} {m u : ℕ} {hlen : ℓ.length = 2 * m + u} {HS : Finset V}
    {hinj : ∀ a ∈ HS, ∀ b ∈ HS, ℓ.idxOf a = ℓ.idxOf b → a = b} (G : SimpleGraph V) {vs x y : V}
    (hvs : vs ∈ HS) (hvsℓ : vs ∉ ℓ) (hx : x ∈ HS)
    (hy : (listStair ℓ m u hlen HS hinj).Eplus G vs y) (hlt : ℓ.idxOf x < ℓ.idxOf y) :
    x ∉ (listStair ℓ m u hlen HS hinj).cls G ((listStair ℓ m u hlen HS hinj).stair vs y) := by
  set D := listStair ℓ m u hlen HS hinj
  have hvsp : ℓ.idxOf vs = 2 * m + u := by rw [List.idxOf_eq_length_iff.2 hvsℓ, hlen]
  have hvsL : D.side vs = true := listStair_side.2 (by omega)
  have hvsi : D.idx vs = D.m + 1 := by
    rw [listStair_idx, if_pos (by omega), hvsp, listStair_m]; push_cast; ring
  by_cases hxL : m + u ≤ ℓ.idxOf x
  · have hxs : D.side x = true := listStair_side.2 hxL
    have hys : D.side y = true := listStair_side.2 (by omega)
    refine not_cls_of_LL D G hvsL hvsi hy hxs hys ?_
    rw [listStair_idx, listStair_idx, if_pos hxL, if_pos (by omega)]
    omega
  · push_neg at hxL
    have hxs : D.side x = false := listStair_side_false.2 hxL
    refine D.not_cls_of_good hvs hvsL hvsi hy hx hxs ?_
    by_cases hyL : m + u ≤ ℓ.idxOf y
    · exact Or.inl (listStair_side.2 hyL)
    · right
      rw [listStair_idx, listStair_idx, if_neg hyL, if_neg (by omega)]
      omega

end CH89
