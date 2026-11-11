/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CH89.Label
public import CH89.Ballot

/-!
# The ballot condition for the list `lst`

With `h = +1` on `X`, `−1` on `Y`: the sum of `h` over `lst` is `|X| − |Y| = 0`; each edge
`(r, l)` contributes `τ(r) + τ(l) = h(l) − h(r)`, so `T = 2 Σ_{lefts} h` and
`T′ = −2 Σ_{partner(lefts)} h` (`tsum_eq`, `tsum_swap_eq`). With `T, T′ ≤ 1` every prefix of `lst`
has `h`-sum at least `−1` (`wsum_take_lst`), and `exists_stair` assembles the staircase labelling
together with a pairing `σ : Y → X` that is good for all but at most one `y`.
-/

@[expose] public section

namespace CH89

open SimpleGraph Finset OneFactor

open scoped Classical

attribute [-instance] SimpleGraph.Sdiff.adjDecidable SimpleGraph.Sup.adjDecidable

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem wsum_congr {φ ψ : V → ℤ} {L : List V} (h : ∀ v ∈ L, φ v = ψ v) : wsum φ L = wsum ψ L := by
  unfold wsum; rw [List.map_congr_left h]

theorem wsum_add (φ ψ : V → ℤ) (L : List V) :
    wsum (fun v => φ v + ψ v) L = wsum φ L + wsum ψ L := by
  induction L with
  | nil => simp
  | cons a L ih => simp only [wsum_cons, ih]; ring

theorem wsum_sub (φ ψ : V → ℤ) (L : List V) :
    wsum (fun v => φ v - ψ v) L = wsum φ L - wsum ψ L := by
  induction L with
  | nil => simp
  | cons a L ih => simp only [wsum_cons, ih]; ring

theorem wsum_neg (φ : V → ℤ) (L : List V) : wsum (fun v => -φ v) L = -wsum φ L := by
  induction L with
  | nil => simp
  | cons a L ih => simp only [wsum_cons, ih]; ring

theorem wsum_map (φ : V → ℤ) (f : V → V) (L : List V) : wsum φ (L.map f) = wsum (φ ∘ f) L := by
  simp [wsum, List.map_map]

theorem wsum_const {φ : V → ℤ} {c : ℤ} {L : List V} (h : ∀ v ∈ L, φ v = c) :
    wsum φ L = c * L.length := by
  induction L with
  | nil => simp
  | cons a L ih =>
    simp only [wsum_cons, List.length_cons, Nat.cast_succ]
    rw [h a (List.mem_cons_self ..), ih fun v hv => h v (List.mem_cons_of_mem _ hv)]
    ring

theorem wsum_perm (φ : V → ℤ) {L L' : List V} (h : L.Perm L') : wsum φ L = wsum φ L' := by
  unfold wsum; exact (h.map φ).sum_eq

theorem hval_eq {X Y : Finset V} (hXY : Disjoint X Y) (v : V) :
    hval X Y v = (if v ∈ X then 1 else 0) - (if v ∈ Y then 1 else 0) := by
  have hv : v ∈ X → v ∉ Y := fun h => Finset.disjoint_left.1 hXY h
  unfold hval
  by_cases hx : v ∈ X
  · simp [hx, hv hx]
  · by_cases hy : v ∈ Y <;> simp [hx, hy]

theorem wsum_hval {X Y : Finset V} (hXY : Disjoint X Y) (L : List V) :
    wsum (hval X Y) L = ((L.filter (· ∈ X)).length : ℤ) - (L.filter (· ∈ Y)).length := by
  induction L with
  | nil => simp
  | cons a L ih =>
    rw [wsum_cons, ih, hval_eq hXY]
    simp only [List.filter_cons, decide_eq_true_eq]
    split_ifs <;> simp <;> ring

/-- Prefix sums of `A ++ B` with `h ≥ 0` on `A` and `h ≤ 0` on `B`. -/
theorem wsum_take_up_down (φ : V → ℤ) {A B : List V} (hA : ∀ v ∈ A, 0 ≤ φ v)
    (hB : ∀ v ∈ B, φ v ≤ 0) (k : ℕ) : min 0 (wsum φ (A ++ B)) ≤ wsum φ ((A ++ B).take k) := by
  rw [List.take_append, wsum_append, wsum_append]
  have h1 := wsum_nonneg_take φ hA k
  have h2 := wsum_nonpos_take φ hB (k - A.length)
  by_cases hk : k ≤ A.length
  · rw [show k - A.length = 0 by omega]; simp only [List.take_zero, wsum_nil]
    exact le_trans (min_le_left _ _) (by linarith)
  · rw [List.take_of_length_le (by omega)]
    exact le_trans (min_le_right _ _) (by linarith)

/-- Prefix sums of `F ++ U ++ reverse L` from the prefix sums of the three parts. -/
theorem prefix_bound {φ : V → ℤ} {F U L : List V} (hF : ∀ j, 0 ≤ wsum φ (F.take j))
    (hU : ∀ j, min 0 (wsum φ U) ≤ wsum φ (U.take j)) (hL : ∀ j, wsum φ (L.take j) ≤ 1)
    (htot : wsum φ F + wsum φ U + wsum φ L = 0) (hF0 : 0 ≤ wsum φ F) (hL0 : wsum φ L ≤ 0)
    (k : ℕ) : -1 ≤ wsum φ ((F ++ U ++ L.reverse).take k) := by
  rw [List.take_append, List.take_append, wsum_append, wsum_append]
  by_cases hk1 : k ≤ F.length
  · rw [Nat.sub_eq_zero_of_le hk1, Nat.sub_eq_zero_of_le (by rw [List.length_append]; omega)]
    simp only [List.take_zero, wsum_nil, add_zero]
    have := hF k; omega
  · rw [List.take_of_length_le (by omega : F.length ≤ k)]
    by_cases hk2 : k ≤ F.length + U.length
    · have e : k - (F ++ U).length = 0 := by rw [List.length_append]; omega
      rw [e]
      simp only [List.take_zero, wsum_nil, add_zero]
      have := hU (k - F.length)
      rcases le_total 0 (wsum φ U) with h | h
      · rw [min_eq_left h] at this; omega
      · rw [min_eq_right h] at this; omega
    · rw [List.take_of_length_le (by omega : U.length ≤ k - F.length), List.take_reverse,
        wsum_reverse]
      have h3 := wsum_take_add_drop φ L (L.length - (k - (F ++ U).length))
      have h4 := hL (L.length - (k - (F ++ U).length))
      omega

section Main

variable {M : SimpleGraph V} {X Y HV : Finset V}
  (hM : IsMatchingGraph M) (hMS : ∀ a b, M.Adj a b → a ∈ HV ∧ b ∈ HV) (hXY : Disjoint X Y)

include hM hMS hXY in
theorem sum_eq_wsum (f : V → ℤ) : ∑ v ∈ HV, f v = wsum f (lst M X Y HV) := by
  have : HV = (lst M X Y HV).toFinset := by
    ext v; rw [List.mem_toFinset, mem_lst hM hMS]
  have h := List.sum_toFinset f (lst_nodup hM hXY (M := M) (HV := HV))
  rw [← this] at h
  exact h

include hM in
theorem tau_pair {l : V} (hl : l ∈ leftM M X Y HV) (hXY : Disjoint X Y) (A B : Finset V)
    (hAB : (A = X ∧ B = Y) ∨ (A = Y ∧ B = X)) :
    tau M A B (partner M l) + tau M A B l = hval X Y l - hval X Y (partner M l) := by
  have hc := leftM_cover hl
  have hadj := adj_partner hc
  have hpref := (mem_leftM.1 hl).2.2
  set r := partner M l
  have al : ∀ u, M.Adj l u ↔ u = r := fun u => ⟨fun h => hM l u r h hadj, fun h => h ▸ hadj⟩
  have ar : ∀ u, M.Adj r u ↔ u = l := fun u =>
    ⟨fun h => hM r u l h hadj.symm, fun h => h ▸ hadj.symm⟩
  have hX1 : l ∈ X → r ∈ X := pref_X hpref
  have hY1 : r ∈ Y → l ∈ Y := pref_Y hXY hpref
  have d1 : l ∈ X → l ∉ Y := fun h => Finset.disjoint_left.1 hXY h
  have d2 : r ∈ X → r ∉ Y := fun h => Finset.disjoint_left.1 hXY h
  have hr' : ∃ u, M.Adj r u := ⟨l, hadj.symm⟩
  have hl' : ∃ u, M.Adj l u := ⟨r, hadj⟩
  unfold tau
  rw [if_pos hr', if_pos hl']
  unfold Mixed hval
  simp only [al, ar, exists_eq_left]
  rcases hAB with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
  · by_cases a1 : l ∈ A <;> by_cases a2 : l ∈ B <;> by_cases a3 : r ∈ A <;>
      by_cases a4 : r ∈ B <;> simp_all

include hXY in
theorem tau_unm {v : V} (hv : ∀ u, ¬ M.Adj v u) :
    tau M X Y v = -hval X Y v ∧ tau M Y X v = hval X Y v := by
  have : ¬ ∃ u, M.Adj v u := fun ⟨u, hu⟩ => hv u hu
  unfold tau
  rw [if_neg this, if_neg this]
  unfold hval
  have hv : v ∈ X → v ∉ Y := fun h => Finset.disjoint_left.1 hXY h
  constructor
  · rfl
  · by_cases hx : v ∈ X
    · simp [hx, hv hx]
    · by_cases hy : v ∈ Y <;> simp [hx, hy]

variable (hXH : X ⊆ HV) (hYH : Y ⊆ HV) (hcard : #X = #Y)

include hM hMS hXY hXH hYH hcard in
theorem wsum_hval_lst : wsum (hval X Y) (lst M X Y HV) = 0 := by
  rw [← sum_eq_wsum hM hMS hXY]
  simp_rw [hval_eq hXY]
  rw [sum_sub_distrib, sum_boole, sum_boole, filter_mem_eq_inter, filter_mem_eq_inter,
    inter_eq_right.2 hXH, inter_eq_right.2 hYH, hcard]
  simp

/-- The three parts of `lst`. -/
theorem wsum_lst (φ : V → ℤ) : wsum φ (lst M X Y HV) =
    wsum φ ((lefts M X Y HV).map (partner M)) + wsum φ (unms M X Y HV) +
      wsum φ (lefts M X Y HV) := by
  unfold lst; rw [wsum_append, wsum_append, wsum_reverse]

include hM hMS hXY in
theorem tsum_eq_aux (A B : Finset V) (hAB : (A = X ∧ B = Y) ∨ (A = Y ∧ B = X)) :
    tsum M HV A B = wsum (hval X Y) (lefts M X Y HV) -
      wsum (hval X Y) ((lefts M X Y HV).map (partner M)) + wsum (tau M A B) (unms M X Y HV) := by
  unfold tsum
  rw [sum_eq_wsum hM hMS hXY, wsum_lst]
  have h1 : wsum (tau M A B) ((lefts M X Y HV).map (partner M)) + wsum (tau M A B) (lefts M X Y HV) =
      wsum (hval X Y) (lefts M X Y HV) - wsum (hval X Y) ((lefts M X Y HV).map (partner M)) := by
    rw [wsum_map, wsum_map, ← wsum_add, ← wsum_sub]
    exact wsum_congr fun l hl => tau_pair hM ((mem_lefts).1 hl) hXY A B hAB
  linarith

include hM hMS hXY hXH hYH hcard in
theorem tsum_eq : tsum M HV X Y = 2 * wsum (hval X Y) (lefts M X Y HV) := by
  rw [tsum_eq_aux hM hMS hXY X Y (Or.inl ⟨rfl, rfl⟩)]
  have h0 := wsum_hval_lst hM hMS hXY hXH hYH hcard
  rw [wsum_lst] at h0
  have : wsum (tau M X Y) (unms M X Y HV) = -wsum (hval X Y) (unms M X Y HV) := by
    rw [← wsum_neg]
    exact wsum_congr fun v hv => (tau_unm hXY fun u hu =>
      (mem_unm.1 (mem_unms.1 hv)).2 (mem_cover.2 ⟨u, hu⟩)).1
  rw [this]; linarith

include hM hMS hXY hXH hYH hcard in
theorem tsum_swap_eq : tsum M HV Y X = -2 * wsum (hval X Y) ((lefts M X Y HV).map (partner M)) := by
  rw [tsum_eq_aux hM hMS hXY Y X (Or.inr ⟨rfl, rfl⟩)]
  have h0 := wsum_hval_lst hM hMS hXY hXH hYH hcard
  rw [wsum_lst] at h0
  have : wsum (tau M Y X) (unms M X Y HV) = wsum (hval X Y) (unms M X Y HV) :=
    wsum_congr fun v hv => (tau_unm hXY fun u hu =>
      (mem_unm.1 (mem_unms.1 hv)).2 (mem_cover.2 ⟨u, hu⟩)).2
  rw [this]; linarith

/-! ### Prefix bounds -/

include hXY in
theorem lefts_take_le (k : ℕ) : wsum (hval X Y) ((lefts M X Y HV).take k) ≤
    max 1 (wsum (hval X Y) (lefts M X Y HV)) := by
  have hA : ∀ v ∈ endsA M X Y HV, hval X Y v ≤ 0 := fun v hv => by
    have := (mem_endsA.1 hv).2.2; unfold hval; split_ifs <;> simp_all
  have hXX : ∀ v ∈ endsXX M X Y HV, hval X Y v = 1 := fun v hv => by
    have := (mem_endsXX.1 hv).2; unfold hval; simp [this]
  have hYY : ∀ v ∈ endsYY M X Y HV, hval X Y v = -1 := fun v hv => by
    have h1 := (mem_endsYY.1 hv)
    have h2 : v ∈ Y := pref_Y hXY (mem_leftM.1 h1.1).2.2 h1.2
    have h3 : v ∉ X := fun h => Finset.disjoint_left.1 hXY h h2
    unfold hval; simp [h2, h3]
  have hI : wsum (hval X Y) (ilv (endsXX M X Y HV) (endsYY M X Y HV)) =
      ((endsXX M X Y HV).length : ℤ) - (endsYY M X Y HV).length := by
    rw [wsum_perm _ (ilv_perm _ _), wsum_append, wsum_const hXX, wsum_const hYY]; ring
  unfold lefts
  rw [List.take_append, wsum_append, wsum_append, hI]
  have h1 := wsum_nonpos_take (hval X Y) hA k
  have h2 := (wsum_ilv_take (hval X Y) hXX hYY (k - (endsA M X Y HV).length)).2
  by_cases hk : k ≤ (endsA M X Y HV).length
  · rw [show k - (endsA M X Y HV).length = 0 by omega]
    simp only [List.take_zero, wsum_nil, add_zero]
    exact le_trans h1.2 (by simp)
  · rw [List.take_of_length_le (by omega)] at h1 ⊢
    have h3 := (wsum_nonpos_take (hval X Y) hA 0)
    simp only [List.take_zero, wsum_nil] at h3
    rcases le_total 1 (((endsXX M X Y HV).length : ℤ) - (endsYY M X Y HV).length) with h | h
    · rw [max_eq_right h] at h2
      exact le_trans (by linarith) (le_max_right _ _)
    · rw [max_eq_left h] at h2
      exact le_trans (by linarith) (le_max_left _ _)

include hM hXY in
theorem partners_take_ge (k : ℕ) : min 0 (wsum (hval X Y) ((lefts M X Y HV).map (partner M))) ≤
    wsum (hval X Y) (((lefts M X Y HV).map (partner M)).take k) := by
  have hA : ∀ v ∈ (endsA M X Y HV).map (partner M), 0 ≤ hval X Y v := fun v hv => by
    obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hv
    have := (mem_endsA.1 hl).2.1; unfold hval; split_ifs <;> simp_all
  have hXX : ∀ v ∈ (endsXX M X Y HV).map (partner M), hval X Y v = 1 := fun v hv => by
    obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hv
    have := pref_X (mem_leftM.1 (mem_endsXX.1 hl).1).2.2 (mem_endsXX.1 hl).2
    unfold hval; simp [this]
  have hYY : ∀ v ∈ (endsYY M X Y HV).map (partner M), hval X Y v = -1 := fun v hv => by
    obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hv
    have h2 := (mem_endsYY.1 hl).2
    have h3 : partner M l ∉ X := fun h => Finset.disjoint_left.1 hXY h h2
    unfold hval; simp [h2, h3]
  set A := (endsA M X Y HV).map (partner M)
  set I := ilv ((endsXX M X Y HV).map (partner M)) ((endsYY M X Y HV).map (partner M))
  have hF : (lefts M X Y HV).map (partner M) = A ++ I := by
    unfold lefts; rw [List.map_append, map_ilv]
  have hI : wsum (hval X Y) I = (((endsXX M X Y HV).map (partner M)).length : ℤ) -
      ((endsYY M X Y HV).map (partner M)).length := by
    rw [wsum_perm _ (ilv_perm _ _), wsum_append, wsum_const hXX, wsum_const hYY]; ring
  rw [hF, List.take_append, wsum_append, wsum_append, hI]
  have h1 := wsum_nonneg_take (hval X Y) hA k
  have h2 := (wsum_ilv_take (hval X Y) hXX hYY (k - A.length)).1
  by_cases hk : k ≤ A.length
  · rw [show k - A.length = 0 by omega]
    simp only [List.take_zero, wsum_nil, add_zero]
    exact le_trans (min_le_left _ _) h1.1
  · rw [List.take_of_length_le (by omega)] at h1 ⊢
    rcases le_total 0 (((((endsXX M X Y HV).map (partner M)).length : ℤ)) -
      ((endsYY M X Y HV).map (partner M)).length) with h | h
    · rw [min_eq_left h] at h2
      exact le_trans (min_le_left _ _) (by linarith)
    · rw [min_eq_right h] at h2
      exact le_trans (min_le_right _ _) (by linarith)

include hXY in
theorem unms_take_ge (k : ℕ) : min 0 (wsum (hval X Y) (unms M X Y HV)) ≤
    wsum (hval X Y) ((unms M X Y HV).take k) := by
  unfold unms
  apply wsum_take_up_down
  · intro v hv
    simp only [Finset.mem_toList, mem_filter] at hv
    unfold hval; simp [hv.2]
  · intro v hv
    simp only [List.mem_append, Finset.mem_toList, mem_filter] at hv
    unfold hval
    rcases hv with hv | hv
    · simp [hv.2.1, hv.2.2]
    · have : v ∉ X := fun h => Finset.disjoint_left.1 hXY h hv.2
      simp [this, hv.2]

include hM hMS hXY hXH hYH hcard in
/-- **Every prefix of `lst` has `#Y ≤ #X + 1`.** -/
theorem wsum_take_lst (hT : tsum M HV X Y ≤ 1) (hT' : tsum M HV Y X ≤ 1) (k : ℕ) :
    -1 ≤ wsum (hval X Y) ((lst M X Y HV).take k) := by
  have e1 := tsum_eq hM hMS hXY hXH hYH hcard
  have e2 := tsum_swap_eq hM hMS hXY hXH hYH hcard
  have h0 := wsum_hval_lst hM hMS hXY hXH hYH hcard
  rw [wsum_lst] at h0
  have hL : wsum (hval X Y) (lefts M X Y HV) ≤ 0 := by omega
  have hF : 0 ≤ wsum (hval X Y) ((lefts M X Y HV).map (partner M)) := by omega
  unfold lst
  refine prefix_bound (fun j => ?_) (fun j => unms_take_ge hXY j) (fun j => ?_) (by linarith) hF hL k
  · have := partners_take_ge hM hXY (HV := HV) j
    rw [min_eq_left hF] at this; exact this
  · have := lefts_take_le hXY (M := M) (HV := HV) j
    rw [max_eq_left (by omega)] at this; exact this

end Main

end CH89
