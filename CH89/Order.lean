/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import OneFactor.Label67b
public import CH89.Ilv

/-!
# The list `r_m, …, r_1, r_0, …, r_t, l_1, …, l_m`

For a matching `M` inside `HV`, the left ends (`leftM`, the `Y` end of an `XY` edge, the `P` end of
an `XP` edge, the `Y` end of a `YP` edge) are listed from outside in as `lefts`: first those of the
edges with `h(r) ≥ 0 ≥ h(l)` (`endsA`), then the `XX` and `YY` edges alternately (`ilv`). The list
`lst` is `partner(lefts) ++ unmatched ++ reverse(lefts)`, the unmatched with `X` first and `Y` last.
`lst` has no repetitions and consists exactly of `HV` (`lst_nodup`, `mem_lst`); the positions of
the two ends of an edge are `i` and `2m + u − 1 − i` (`pos_partner_get`, `pos_get`).
-/

@[expose] public section

namespace CH89

open SimpleGraph Finset OneFactor

open scoped Classical

attribute [-instance] SimpleGraph.Sdiff.adjDecidable SimpleGraph.Sup.adjDecidable

variable {V : Type*} [Fintype V] [DecidableEq V]

section Defs

variable (M : SimpleGraph V) (X Y HV : Finset V)

/-- Left ends of the edges with `h(r) ≥ 0 ≥ h(l)`. -/
noncomputable def endsA : List V :=
  ((leftM M X Y HV).filter fun l => partner M l ∉ Y ∧ l ∉ X).toList

/-- Left ends of the `XX` edges. -/
noncomputable def endsXX : List V := ((leftM M X Y HV).filter fun l => l ∈ X).toList

/-- Left ends of the `YY` edges. -/
noncomputable def endsYY : List V := ((leftM M X Y HV).filter fun l => partner M l ∈ Y).toList

/-- The left ends, from outside in. -/
noncomputable def lefts : List V := endsA M X Y HV ++ ilv (endsXX M X Y HV) (endsYY M X Y HV)

/-- The unmatched vertices: `X` first, `Y` last. -/
noncomputable def unms : List V :=
  ((unm M HV).filter (· ∈ X)).toList ++
    (((unm M HV).filter fun v => v ∉ X ∧ v ∉ Y).toList ++ ((unm M HV).filter (· ∈ Y)).toList)

/-- The list `r_m, …, r_1, r_0, …, r_t, l_1, …, l_m`. -/
noncomputable def lst : List V :=
  (lefts M X Y HV).map (partner M) ++ unms M X Y HV ++ (lefts M X Y HV).reverse

end Defs

theorem pref_X {X Y : Finset V} {a b : V} (h : Pref X Y a b) (ha : a ∈ X) : b ∈ X := by
  by_contra hb
  have e1 : prio X Y a = 0 := by simp [prio, ha]
  have e2 : 1 ≤ prio X Y b := by unfold prio; split_ifs <;> simp_all
  unfold Pref at h
  rw [e1] at h
  omega

theorem pref_Y {X Y : Finset V} {a b : V} (hXY : Disjoint X Y) (h : Pref X Y a b) (hb : b ∈ Y) :
    a ∈ Y := by
  have hbX : b ∉ X := fun h' => Finset.disjoint_left.1 hXY h' hb
  by_contra ha
  have e1 : prio X Y b = 2 := by simp [prio, hb, hbX]
  have e2 : prio X Y a ≤ 1 := by unfold prio; split_ifs <;> simp_all
  unfold Pref at h
  rw [e1] at h
  omega

section Facts

variable {M : SimpleGraph V} {X Y HV : Finset V}
  (hM : IsMatchingGraph M) (hMS : ∀ a b, M.Adj a b → a ∈ HV ∧ b ∈ HV) (hXY : Disjoint X Y)

theorem mem_endsA {l : V} : l ∈ endsA M X Y HV ↔ l ∈ leftM M X Y HV ∧ partner M l ∉ Y ∧ l ∉ X := by
  simp [endsA]

theorem mem_endsXX {l : V} : l ∈ endsXX M X Y HV ↔ l ∈ leftM M X Y HV ∧ l ∈ X := by
  simp [endsXX]

theorem mem_endsYY {l : V} : l ∈ endsYY M X Y HV ↔ l ∈ leftM M X Y HV ∧ partner M l ∈ Y := by
  simp [endsYY]

theorem mem_lefts {l : V} : l ∈ lefts M X Y HV ↔ l ∈ leftM M X Y HV := by
  unfold lefts
  rw [List.mem_append, (ilv_perm _ _).mem_iff, List.mem_append, mem_endsA, mem_endsXX, mem_endsYY]
  constructor
  · rintro (h | h | h) <;> exact h.1
  · intro h
    by_cases h1 : l ∈ X
    · exact Or.inr (Or.inl ⟨h, h1⟩)
    by_cases h2 : partner M l ∈ Y
    · exact Or.inr (Or.inr ⟨h, h2⟩)
    · exact Or.inl ⟨h, h2, h1⟩

include hXY in
theorem lefts_nodup : (lefts M X Y HV).Nodup := by
  unfold lefts
  have hXX : ∀ l ∈ endsXX M X Y HV, partner M l ∈ X := fun l hl =>
    pref_X ((mem_leftM.1 (mem_endsXX.1 hl).1).2.2) (mem_endsXX.1 hl).2
  have h1 : (endsXX M X Y HV ++ endsYY M X Y HV).Nodup := by
    rw [List.nodup_append]
    refine ⟨Finset.nodup_toList _, Finset.nodup_toList _, fun a ha b hb e => ?_⟩
    subst e
    exact Finset.disjoint_left.1 hXY (hXX a ha) (mem_endsYY.1 hb).2
  rw [List.nodup_append]
  refine ⟨Finset.nodup_toList _, (ilv_perm _ _).nodup_iff.2 h1, fun a ha b hb e => ?_⟩
  subst e
  rw [(ilv_perm _ _).mem_iff, List.mem_append] at hb
  rcases hb with hb | hb
  · exact (mem_endsA.1 ha).2.2 (mem_endsXX.1 hb).2
  · exact (mem_endsA.1 ha).2.1 (mem_endsYY.1 hb).2

theorem mem_unms {v : V} : v ∈ unms M X Y HV ↔ v ∈ unm M HV := by
  unfold unms
  simp only [List.mem_append, Finset.mem_toList, mem_filter]
  tauto

include hXY in
theorem unms_nodup : (unms M X Y HV).Nodup := by
  unfold unms
  rw [List.nodup_append, List.nodup_append]
  refine ⟨Finset.nodup_toList _, ⟨Finset.nodup_toList _, Finset.nodup_toList _, ?_⟩, ?_⟩
  · intro a ha b hb e; subst e
    simp only [Finset.mem_toList, mem_filter] at ha hb
    exact ha.2.2 hb.2
  · intro a ha b hb e; subst e
    simp only [List.mem_append, Finset.mem_toList, mem_filter] at ha hb
    rcases hb with hb | hb
    · exact hb.2.1 ha.2
    · exact Finset.disjoint_left.1 hXY ha.2 hb.2

theorem leftM_cover {l : V} (h : l ∈ leftM M X Y HV) : l ∈ cover M := (mem_leftM.1 h).2.1

include hM hXY in
theorem lst_nodup : (lst M X Y HV).Nodup := by
  have hL := lefts_nodup hXY (M := M) (HV := HV)
  unfold lst
  rw [List.nodup_append, List.nodup_append]
  refine ⟨⟨hL.map_on fun a ha b hb e => ?_, unms_nodup hXY, ?_⟩, List.nodup_reverse.2 hL, ?_⟩
  · have hca := leftM_cover ((mem_lefts).1 ha)
    have hcb := leftM_cover ((mem_lefts).1 hb)
    rw [← partner_partner hM hca, ← partner_partner hM hcb, e]
  · intro a ha b hb e; subst e
    obtain ⟨l, hl, rfl⟩ := List.mem_map.1 ha
    have := (mem_unm.1 (mem_unms.1 hb)).2
    exact this (partner_mem_cover (leftM_cover (mem_lefts.1 hl)))
  · intro a ha b hb e; subst e
    rw [List.mem_reverse, mem_lefts] at hb
    rcases List.mem_append.1 ha with ha | ha
    · obtain ⟨l, hl, rfl⟩ := List.mem_map.1 ha
      exact partner_not_leftM hM (mem_lefts.1 hl) hb
    · exact (mem_unm.1 (mem_unms.1 ha)).2 (leftM_cover hb)

include hM hMS in
theorem mem_lst {v : V} : v ∈ lst M X Y HV ↔ v ∈ HV := by
  unfold lst
  simp only [List.mem_append, List.mem_map, List.mem_reverse, mem_lefts, mem_unms, mem_unm]
  constructor
  · rintro ((⟨l, hl, rfl⟩ | ⟨hv, -⟩) | hv)
    · exact partner_mem hMS (leftM_cover hl)
    · exact hv
    · exact (mem_leftM.1 hv).1
  · intro hv
    by_cases hc : v ∈ cover M
    · by_cases hL : v ∈ leftM M X Y HV
      · exact Or.inr hL
      · exact Or.inl (Or.inl ⟨partner M v, partner_mem_leftM hM hMS hv hc hL,
          partner_partner hM hc⟩)
    · exact Or.inl (Or.inr ⟨hv, hc⟩)

theorem length_lst : (lst M X Y HV).length =
    2 * (lefts M X Y HV).length + (unms M X Y HV).length := by
  unfold lst; simp; ring

/-- Entries of `lst` by position. -/
theorem lst_get_lt (j : ℕ) (hj : j < (lefts M X Y HV).length) :
    (lst M X Y HV)[j]'(by rw [length_lst]; omega) = partner M (lefts M X Y HV)[j] := by
  have h2 : j < (lefts M X Y HV).length + (unms M X Y HV).length := by omega
  simp only [lst, List.getElem_append, List.length_append, List.length_map, List.getElem_map,
    h2, hj, dite_true]

theorem lst_get_ge (j : ℕ) (hj1 : (lefts M X Y HV).length + (unms M X Y HV).length ≤ j)
    (hj2 : j < 2 * (lefts M X Y HV).length + (unms M X Y HV).length) :
    (lst M X Y HV)[j]'(by rw [length_lst]; omega) =
      (lefts M X Y HV)[2 * (lefts M X Y HV).length + (unms M X Y HV).length - 1 - j]'(by omega) := by
  have h2 : ¬ j < (lefts M X Y HV).length + (unms M X Y HV).length := by omega
  simp only [lst, List.getElem_append, List.length_append, List.length_map, h2, dite_false,
    List.getElem_reverse]
  congr 1
  omega

theorem lst_get_mid (j : ℕ) (hj1 : (lefts M X Y HV).length ≤ j)
    (hj2 : j < (lefts M X Y HV).length + (unms M X Y HV).length) :
    (lst M X Y HV)[j]'(by rw [length_lst]; omega) ∈ unms M X Y HV := by
  have h1 : ¬ j < (lefts M X Y HV).length := by omega
  simp only [lst, List.getElem_append, List.length_append, List.length_map, hj2, h1, dite_true,
    dite_false]
  exact List.getElem_mem _

include hM hXY in
/-- The position of `partner(l_i)` is `i`. -/
theorem pos_partner_get (i : ℕ) (hi : i < (lefts M X Y HV).length) :
    (lst M X Y HV).idxOf (partner M (lefts M X Y HV)[i]) = i := by
  rw [← lst_get_lt i hi]
  exact (lst_nodup hM hXY).idxOf_getElem i _

include hM hXY in
/-- The position of `l_i` is `2m + u − 1 − i`. -/
theorem pos_get (i : ℕ) (hi : i < (lefts M X Y HV).length) :
    (lst M X Y HV).idxOf (lefts M X Y HV)[i] =
      2 * (lefts M X Y HV).length + (unms M X Y HV).length - 1 - i := by
  have h1 := lst_get_ge (M := M) (X := X) (Y := Y) (HV := HV)
    (2 * (lefts M X Y HV).length + (unms M X Y HV).length - 1 - i) (by omega) (by omega)
  have e : (lefts M X Y HV)[2 * (lefts M X Y HV).length + (unms M X Y HV).length - 1 -
      (2 * (lefts M X Y HV).length + (unms M X Y HV).length - 1 - i)]'(by omega) =
      (lefts M X Y HV)[i] := by congr 1; omega
  rw [e] at h1
  rw [← h1]
  exact (lst_nodup hM hXY).idxOf_getElem _ _

end Facts

end CH89
