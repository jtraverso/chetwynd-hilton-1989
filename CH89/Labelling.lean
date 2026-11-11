/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CH89.Prefix

/-!
# The staircase labelling with a good pairing (the repaired ordering step)

`exists_stair`: for a matching `M` inside `HV` with `T, T′ ≤ 1` (`exists_good_matching`), the
labelling `listStair (lst …)` of `insert v* HV` is a staircase labelling with `v*` the left vertex
of index `m + 1`, `q = |HV|`, the matching edges joining left and right vertices of equal index,
the unmatched vertices on the right with index `≤ 0`, and a bijection `σ : Y → X` such that for
all `y ∈ Y` but at most one, `σ y` is uncovered by the staircase class of `v* y`.
-/

@[expose] public section

namespace CH89

open SimpleGraph Finset OneFactor

open scoped Classical

attribute [-instance] SimpleGraph.Sdiff.adjDecidable SimpleGraph.Sup.adjDecidable

variable {V : Type*} [Fintype V] [DecidableEq V]

section

variable {M : SimpleGraph V} {X Y HV : Finset V}
  (hM : IsMatchingGraph M) (hMS : ∀ a b, M.Adj a b → a ∈ HV ∧ b ∈ HV) (hXY : Disjoint X Y)

include hM hMS in
/-- The two ends of a matching edge are `l_i` and `partner(l_i)`. -/
theorem edge_cases {a b : V} (hab : M.Adj a b) : ∃ i, ∃ hi : i < (lefts M X Y HV).length,
    (a = (lefts M X Y HV)[i] ∧ b = partner M (lefts M X Y HV)[i]) ∨
      (b = (lefts M X Y HV)[i] ∧ a = partner M (lefts M X Y HV)[i]) := by
  have hca : a ∈ cover M := mem_cover.2 ⟨b, hab⟩
  by_cases hL : a ∈ leftM M X Y HV
  · obtain ⟨i, hi, e⟩ := List.mem_iff_getElem.1 ((mem_lefts).2 hL)
    exact ⟨i, hi, Or.inl ⟨e.symm, by rw [e, partner_eq hM hab]⟩⟩
  · have hb : partner M a ∈ leftM M X Y HV := partner_mem_leftM hM hMS (hMS a b hab).1 hca hL
    rw [partner_eq hM hab] at hb
    obtain ⟨i, hi, e⟩ := List.mem_iff_getElem.1 ((mem_lefts).2 hb)
    exact ⟨i, hi, Or.inr ⟨e.symm, by rw [e, partner_eq hM hab.symm]⟩⟩

end

/-- **The labelling and the pairing.** -/
theorem exists_stair (G : SimpleGraph V) {M : SimpleGraph V} {X Y HV : Finset V} {vs : V}
    (hM : IsMatchingGraph M) (hMS : ∀ a b, M.Adj a b → a ∈ HV ∧ b ∈ HV) (hXY : Disjoint X Y)
    (hXH : X ⊆ HV) (hYH : Y ⊆ HV) (hcard : #X = #Y) (hvs : vs ∉ HV)
    (hT : tsum M HV X Y ≤ 1) (hT' : tsum M HV Y X ≤ 1) :
    ∃ D : StairData (insert vs HV), D.side vs = true ∧ D.idx vs = D.m + 1 ∧ D.q = #HV ∧
      (∀ u v, M.Adj u v → u ∈ HV ∧ v ∈ HV ∧ D.idx u = D.idx v ∧ D.side u ≠ D.side v) ∧
      (∀ l r, l ∈ HV → r ∈ HV → D.side l = true → D.side r = false → D.idx l = D.idx r →
        M.Adj l r) ∧
      (∀ v ∈ HV, D.side v = false → 1 ≤ D.idx v → v ∈ cover M) ∧
      (∀ v ∈ HV, v ∉ cover M → D.side v = false ∧ D.idx v ≤ 0) ∧
      ∃ (σ : V → V) (Bad : Finset V), Bad ⊆ Y ∧ #Bad ≤ 1 ∧ (∀ y ∈ Y, σ y ∈ X) ∧
        (∀ y ∈ Y, ∀ y' ∈ Y, σ y = σ y' → y = y') ∧
        ∀ y ∈ Y, y ∉ Bad → D.Eplus G vs y → σ y ∉ D.cls G (D.stair vs y) := by
  set ℓ := lst M X Y HV with hℓ
  set m := (lefts M X Y HV).length
  set u := (unms M X Y HV).length
  have hlen : ℓ.length = 2 * m + u := length_lst
  have hnd : ℓ.Nodup := lst_nodup hM hXY
  have hmem : ∀ v, v ∈ ℓ ↔ v ∈ HV := fun v => mem_lst hM hMS
  have hvsℓ : vs ∉ ℓ := fun h => hvs ((hmem vs).1 h)
  have hposvs : ℓ.idxOf vs = 2 * m + u := by rw [List.idxOf_eq_length_iff.2 hvsℓ, hlen]
  have hposlt : ∀ v ∈ HV, ℓ.idxOf v < 2 * m + u := fun v hv => by
    rw [← hlen]; exact List.idxOf_lt_length_iff.2 ((hmem v).2 hv)
  have hinj : ∀ a ∈ insert vs HV, ∀ b ∈ insert vs HV, ℓ.idxOf a = ℓ.idxOf b → a = b := by
    intro a ha b hb e
    rcases mem_insert.1 ha with h1 | h1 <;> rcases mem_insert.1 hb with h2 | h2
    · exact h1.trans h2.symm
    · have := hposlt b h2; rw [h1, hposvs] at e; omega
    · have := hposlt a h1; rw [h2, hposvs] at e; omega
    · exact (List.idxOf_inj ((hmem a).2 h1)).1 e
  set D := listStair ℓ m u hlen (insert vs HV) hinj with hD
  have hside : ∀ v, D.side v = true ↔ m + u ≤ ℓ.idxOf v := fun v => listStair_side
  have hsideF : ∀ v, D.side v = false ↔ ℓ.idxOf v < m + u := fun v => listStair_side_false
  have hidx : ∀ v, D.idx v = if m + u ≤ ℓ.idxOf v then (ℓ.idxOf v : ℤ) - (m + u) + 1
      else (m : ℤ) - ℓ.idxOf v := fun v => listStair_idx v
  -- positions of the ends of an edge
  have hpl : ∀ i (hi : i < m), ℓ.idxOf (lefts M X Y HV)[i] = 2 * m + u - 1 - i :=
    fun i hi => pos_get hM hXY i hi
  have hpr : ∀ i (hi : i < m), ℓ.idxOf (partner M (lefts M X Y HV)[i]) = i :=
    fun i hi => pos_partner_get hM hXY i hi
  have hcovL : ∀ i (hi : i < m), (lefts M X Y HV)[i] ∈ cover M := fun i hi =>
    leftM_cover ((mem_lefts).1 (List.getElem_mem _))
  -- the entries
  have hget : ∀ v ∈ HV, ∀ h : ℓ.idxOf v < ℓ.length, ℓ[ℓ.idxOf v]'(h) = v := fun v _ h =>
    List.getElem_idxOf h
  have hvR : ∀ v ∈ HV, ∀ h : ℓ.idxOf v < m,
      v = partner M ((lefts M X Y HV)[ℓ.idxOf v]'(h)) := fun v hv h =>
    (hget v hv (by omega)).symm.trans
      (lst_get_lt (M := M) (X := X) (Y := Y) (HV := HV) (ℓ.idxOf v) h)
  have hvL : ∀ v ∈ HV, ∀ h : m + u ≤ ℓ.idxOf v, ∀ h' : 2 * m + u - 1 - ℓ.idxOf v < m,
      v = (lefts M X Y HV)[2 * m + u - 1 - ℓ.idxOf v]'(h') :=
    fun v hv h _ => (hget v hv (by have := hposlt v hv; omega)).symm.trans
      (lst_get_ge (M := M) (X := X) (Y := Y) (HV := HV) (ℓ.idxOf v) h (hposlt v hv))
  refine ⟨D, (hside vs).2 (by omega), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hidx, if_pos (by omega), hposvs, listStair_m]; push_cast; ring
  · have hc : #HV = ℓ.length := by
      rw [← List.toFinset_card_of_nodup hnd]; congr 1; ext v; rw [List.mem_toFinset, hmem]
    rw [listStair_q, hc, hlen]; push_cast; ring
  · intro a b hab
    obtain ⟨ha, hb⟩ := hMS a b hab
    obtain ⟨i, hi, h⟩ := edge_cases hM hMS (X := X) (Y := Y) hab
    have hi' : i < m := hi
    have hlI := hpl i hi'
    have hrI := hpr i hi'
    have idxL : D.idx (lefts M X Y HV)[i] = (m : ℤ) - i := by
      rw [hidx, hlI, if_pos (by omega)]; omega
    have idxR : D.idx (partner M (lefts M X Y HV)[i]) = (m : ℤ) - i := by
      rw [hidx, hrI, if_neg (by omega)]
    have sL : D.side (lefts M X Y HV)[i] = true := (hside _).2 (by rw [hlI]; omega)
    have sR : D.side (partner M (lefts M X Y HV)[i]) = false := (hsideF _).2 (by rw [hrI]; omega)
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨ha, hb, by rw [idxL, idxR], by rw [sL, sR]; simp⟩
    · exact ⟨ha, hb, by rw [idxL, idxR], by rw [sL, sR]; simp⟩
  · intro l r hl hr hsl hsr e
    have h1 := (hside l).1 hsl
    have h2 := (hsideF r).1 hsr
    rw [hidx, hidx, if_pos h1, if_neg (by omega)] at e
    have h3 := hposlt l hl
    have hrl : ℓ.idxOf r = 2 * m + u - 1 - ℓ.idxOf l := by omega
    obtain ⟨k, hk⟩ : ∃ k, k = 2 * m + u - 1 - ℓ.idxOf l := ⟨_, rfl⟩
    have hkm : k < m := by omega
    have hL : (lefts M X Y HV)[k]'(hkm) = l := by
      have := hvL l hl h1 (by omega)
      rw [this]; congr 1 <;> omega
    have hR : partner M ((lefts M X Y HV)[k]'(hkm)) = r := by
      have := hvR r hr (by omega)
      rw [this]; congr 2; omega
    rw [← hL, ← hR]
    exact adj_partner (hcovL k hkm)
  · intro v hv hsv hpos
    have h2 := (hsideF v).1 hsv
    rw [hidx, if_neg (by omega)] at hpos
    rw [hvR v hv (by omega)]
    exact partner_mem_cover (hcovL _ (by omega))
  · intro v hv hc
    have h3 := hposlt v hv
    have hlo : m ≤ ℓ.idxOf v := by
      by_contra h
      have hv' := hvR v hv (by omega)
      exact hc (hv' ▸ partner_mem_cover (hcovL _ (by omega)))
    have hhi : ℓ.idxOf v < m + u := by
      by_contra h
      push_neg at h
      have hv' := hvL v hv h (by omega)
      exact hc (hv' ▸ hcovL _ (by omega))
    refine ⟨(hsideF v).2 hhi, ?_⟩
    rw [hidx, if_neg (by omega)]; omega
  · -- the pairing
    have hpre : ∀ k, ((ℓ.take k).filter (· ∈ Y)).length ≤ ((ℓ.take k).filter (· ∈ X)).length + 1 := by
      intro k
      have this : -1 ≤ wsum (hval X Y) (ℓ.take k) := wsum_take_lst hM hMS hXY hXH hYH hcard hT hT' k
      rw [wsum_hval hXY] at this
      omega
    obtain ⟨σ, Bad, hBY, hB1, hσX, hσinj, hgood⟩ := exists_ballot_pairing ℓ hnd
      (fun x hx => (hmem x).2 (hXH hx)) (fun y hy => (hmem y).2 (hYH hy)) hXY hcard vs
      (fun h => hvs (hXH h)) hpre
    refine ⟨σ, Bad, hBY, hB1, hσX, hσinj, fun y hy hb hE => ?_⟩
    exact not_cls_of_lt G (mem_insert_self _ _) hvsℓ (mem_insert_of_mem (hXH (hσX y hy))) hE
      (hgood y hy hb)

end CH89
