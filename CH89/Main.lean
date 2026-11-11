/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CH89.Engine
public import CH89.Labelling
public import CH89.Count
public import CH89.Arith

/-!
# Chetwynd–Hilton 1989, Theorem 2

**Theorem** (`colorable_of_sqrt7`). A `d`-regular graph on `2n` vertices with `(d + n)² ≥ 7 n²`,
that is `d ≥ (√7 − 1) n = ½(√7 − 1)|V|`, is `d`-edge-colourable (1-factorizable).

Proof: the complete graph (`d = 2n − 1`) directly (Vizing on `G − w`, then re-insert `w`).
Otherwise take `w, v*` with many common non-neighbours (Lemma 3, `exists_pair_many_common`),
`X = N(w) − N[v*]`, `Y = W ∩ N(v*)`, drop one vertex from each when they are nonempty, choose the
matching `M₀` (`exists_good_matching`), the labelling and the pairing (`exists_stair`), and apply
Theorem 1 (`colorable_of_labelling`); the budget `n + |HV| + 3 ≤ d` is `five_le` / `three_le`.
-/

@[expose] public section

namespace CH89

open SimpleGraph Finset OneFactor

open scoped Classical

attribute [-instance] SimpleGraph.Sdiff.adjDecidable SimpleGraph.Sup.adjDecidable

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

/-- Theorem 1 for given sets `X ⊆ N(w) − N[v*]`, `Y ⊆ W ∩ N(v*)` of equal size. -/
theorem colorable_of_sets {d n : ℕ} (hcard : Fintype.card V = 2 * n)
    (hreg : ∀ v, G.degree v = d) {w vs : V} (hwv : w ≠ vs) {X Y : Finset V}
    (hXs : X ⊆ setX G w vs) (hYs : Y ⊆ setY G w vs) (hXY : #X = #Y)
    (hY0 : #(setY G w vs \ Y) ≤ 1)
    (hbud : n + #((X ∪ setW G w).erase vs) + 3 ≤ d) : G.lineGraph.Colorable d := by
  set HV := (X ∪ setW G w).erase vs with hHVdef
  have hHV : ∀ v, v ∈ HV ↔ v ≠ vs ∧ (v ∈ X ∨ v ∈ setW G w) := fun v => by
    rw [mem_erase, mem_union]
  have hvsH : vs ∉ HV := fun h => ((hHV vs).1 h).1 rfl
  have hXH : X ⊆ HV := fun x hx => (hHV x).2 ⟨(mem_setX.1 (hXs hx)).2.1, Or.inl hx⟩
  have hYH : Y ⊆ HV := fun y hy =>
    (hHV y).2 ⟨fun e => (mem_setY.1 (hYs hy)).2.ne e.symm,
      Or.inr (mem_setW.2 (mem_setY.1 (hYs hy)).1)⟩
  have hXYd : Disjoint X Y := Finset.disjoint_left.2 fun a ha hb =>
    (mem_setY.1 (hYs hb)).1.2 (mem_setX.1 (hXs ha)).1
  have hXW : Disjoint X (setW G w) := Finset.disjoint_left.2 fun a ha hb =>
    (mem_setW.1 hb).2 (mem_setX.1 (hXs ha)).1
  have hr : #(setW G w) + d + 1 = Fintype.card V := card_nonNbr G hreg w
  have hHVc : #X + #(setW G w) ≤ #HV + 1 := by
    have h2 : #(X ∪ setW G w) - 1 ≤ #HV := by rw [hHVdef]; exact pred_card_le_card_erase
    rw [card_union_of_disjoint hXW] at h2
    omega
  have hYb : ∀ y ∈ Y, #(HV.filter fun z => z ≠ y ∧ ¬ G.Adj y z) + #Y ≤ #HV := by
    intro y hy
    have hyW : y ∈ setW G w := mem_setW.2 (mem_setY.1 (hYs hy)).1
    have hsub : HV.filter (fun z => z ≠ y ∧ ¬ G.Adj y z) ⊆ (nonNbr G y).erase w := by
      intro z hz
      obtain ⟨hzH, hzy, hadj⟩ := mem_filter.1 hz
      refine mem_erase.2 ⟨fun e => ?_, mem_filter.2 ⟨mem_univ _, hzy, hadj⟩⟩
      subst e
      rcases ((hHV z).1 hzH).2 with h | h
      · exact (mem_setX.1 (hXs h)).1.ne rfl
      · exact (mem_setW.1 h).1 rfl
    have hw : w ∈ nonNbr G y := mem_filter.2 ⟨mem_univ _, (mem_setW.1 hyW).1.symm,
      fun h => (mem_setW.1 hyW).2 h.symm⟩
    have h1 := card_le_card hsub
    rw [card_erase_of_mem hw] at h1
    have h3 := card_pos.2 ⟨w, hw⟩
    have h2 := card_nonNbr G hreg y
    omega
  have hXb : ∀ x ∈ X, #(HV.filter fun z => z ≠ x ∧ ¬ G.Adj x z) + #X ≤ #HV := by
    intro x hx
    have hsub : HV.filter (fun z => z ≠ x ∧ ¬ G.Adj x z) ⊆ (nonNbr G x).erase vs := by
      intro z hz
      obtain ⟨hzH, hzx, hadj⟩ := mem_filter.1 hz
      exact mem_erase.2 ⟨fun e => hvsH (e ▸ hzH), mem_filter.2 ⟨mem_univ _, hzx, hadj⟩⟩
    have hv : vs ∈ nonNbr G x := mem_filter.2 ⟨mem_univ _, (mem_setX.1 (hXs hx)).2.1.symm,
      fun h => (mem_setX.1 (hXs hx)).2.2 h.symm⟩
    have h1 := card_le_card hsub
    rw [card_erase_of_mem hv] at h1
    have h3 := card_pos.2 ⟨vs, hv⟩
    have h2 := card_nonNbr G hreg x
    omega
  obtain ⟨M, ⟨hMG, hM, hMS⟩, hmax, hT, hT'⟩ := exists_good_matching G hXH hYH hXYd hYb hXb
  obtain ⟨D, hsvs, hivs, hDq, hsideM, hadjM, hRpos, hunm, σ, Bad, hBY, hB1, hσX, hσinj, hgood⟩ :=
    exists_stair G hM hMS hXYd hXH hYH hXY hvsH hT hT'
  obtain ⟨b, hb⟩ : ∃ b, Bad ⊆ {b} := by
    rcases Bad.eq_empty_or_nonempty with h | ⟨b, hb⟩
    · exact ⟨vs, by rw [h]; exact empty_subset _⟩
    · exact ⟨b, fun z hz => mem_singleton.2 (card_le_one.1 hB1 z hz b hb)⟩
  exact colorable_of_labelling hcard hreg hwv hHV hXs hYs hY0 hXY ⟨hMG, hM, hMS⟩ hmax D hsvs
    hivs hDq hsideM hadjM hRpos hunm hσX hσinj
    (fun y hy hyb hE => hgood y hy (fun h => hyb (mem_singleton.1 (hb h))) hE) hbud

/-- **Chetwynd–Hilton 1989, Theorem 2.** A `d`-regular graph on `2n` vertices with
`7 n² ≤ (d + n)²` (that is, `d ≥ ½(√7 − 1)·2n`) is `d`-edge-colourable. -/
theorem colorable_of_sqrt7 {d n : ℕ} (hcard : Fintype.card V = 2 * n)
    (hreg : ∀ v, G.degree v = d) (h7 : 7 * n ^ 2 ≤ (d + n) ^ 2) : G.lineGraph.Colorable d := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · haveI : IsEmpty V := Fintype.card_eq_zero_iff.1 (by omega)
    exact colorable_of_full_indep _ G le_rfl (fun v => (hreg v).le) fun u => isEmptyElim u
  haveI : Nonempty V := Fintype.card_pos_iff.1 (by omega)
  have hdlt : d + 1 ≤ 2 * n := by
    obtain ⟨v⟩ := ‹Nonempty V›
    have := G.degree_lt_card_verts v
    rw [hreg, hcard] at this; omega
  -- the complete graph
  rcases Nat.lt_or_ge (d + 1) (2 * n) with hr | hr
  swap
  · obtain ⟨w⟩ := ‹Nonempty V›
    have hadj : ∀ v, v ≠ w → G.Adj v w := by
      intro v hv
      have h1 := card_nonNbr G hreg v
      have h0 : nonNbr G v = ∅ := card_eq_zero.1 (by omega)
      by_contra h
      have : w ∈ nonNbr G v := mem_filter.2 ⟨mem_univ _, hv.symm, h⟩
      rw [h0] at this; exact notMem_empty _ this
    refine colorable_of_regular_keepAt G ⟨n, by omega⟩ hreg w (colorable_of_maxDegree_lt _ ?_)
    have : (keepAt G w ∅).maxDegree ≤ d - 1 := by
      refine maxDegree_le_of_forall_degree_le _ _ fun v => ?_
      by_cases hvw : v = w
      · subst hvw; rw [degree_keepAt_empty_self]; exact Nat.zero_le _
      · have := degree_keepAt_empty_add G w hvw
        rw [if_pos (hadj v hvw), hreg] at this
        omega
    omega
  -- the general case
  have hn4 : 4 ≤ n := four_le (by omega) h7
  obtain ⟨w, vs, hwv, hp⟩ := exists_pair_many_common G hreg (by omega)
  rw [hcard] at hp
  have hr' : #(setW G w) + d + 1 = Fintype.card V := card_nonNbr G hreg w
  rw [hcard] at hr'
  have hXY0 := card_X_eq_card_Y (G := G) hreg hwv
  -- `W = Y ∪ P ∪ ({v*} ∩ W)`
  have hW : #(setW G w) ≤ #(setY G w vs) + #(setP G w vs) + 1 := by
    have : setW G w ⊆ (setY G w vs ∪ setP G w vs) ∪ {vs} := by
      intro u hu
      simp only [mem_union, mem_singleton, setY, setP, mem_filter]
      by_cases h1 : u = vs
      · exact Or.inr h1
      · by_cases h2 : G.Adj vs u
        · exact Or.inl (Or.inl ⟨hu, h2⟩)
        · exact Or.inl (Or.inr ⟨hu, h1, h2⟩)
    have h := card_le_card this
    have := card_union_le (setY G w vs ∪ setP G w vs) {vs}
    have := card_union_le (setY G w vs) (setP G w vs)
    simp only [card_singleton] at *
    omega
  have hWY : #(setY G w vs) + #(setP G w vs) ≤ #(setW G w) := by
    rw [← card_union_of_disjoint]
    · refine card_le_card fun u hu => ?_
      rcases mem_union.1 hu with h | h
      · exact (mem_filter.1 h).1
      · exact (mem_filter.1 h).1
    · rw [Finset.disjoint_left]; intro u h1 h2
      exact (mem_filter.1 h2).2.2 (mem_filter.1 h1).2
  rcases (setX G w vs).eq_empty_or_nonempty with hX0 | ⟨x₀, hx₀⟩
  · -- `X = Y = ∅`
    have hY0 : setY G w vs = ∅ := card_eq_zero.1 (by rw [← hXY0, hX0, card_empty])
    refine colorable_of_sets hcard hreg hwv (X := ∅) (Y := ∅) (empty_subset _) (empty_subset _)
      rfl (by rw [hY0]; simp) ?_
    have h1 : #((∅ ∪ setW G w).erase vs) ≤ #(setW G w) := by
      rw [empty_union]; exact card_erase_le
    have := three_le hn4 h7
    omega
  · have hy : (setY G w vs).Nonempty := card_pos.1 (by rw [← hXY0]; exact card_pos.2 ⟨x₀, hx₀⟩)
    obtain ⟨y₀, hy₀⟩ := hy
    refine colorable_of_sets hcard hreg hwv (X := (setX G w vs).erase x₀)
      (Y := (setY G w vs).erase y₀) (erase_subset _ _) (erase_subset _ _)
      (by rw [card_erase_of_mem hx₀, card_erase_of_mem hy₀, hXY0]) ?_ ?_
    · have : setY G w vs \ (setY G w vs).erase y₀ ⊆ {y₀} := by
        intro z hz
        rw [mem_sdiff, mem_erase] at hz
        exact mem_singleton.2 (by by_contra h; exact hz.2 ⟨h, hz.1⟩)
      exact (card_le_card this).trans (by simp)
    · have hXW : Disjoint ((setX G w vs).erase x₀) (setW G w) := Finset.disjoint_left.2
        fun a ha hb => (mem_setW.1 hb).2 (mem_setX.1 (mem_of_mem_erase ha)).1
      have h1 : #(((setX G w vs).erase x₀ ∪ setW G w).erase vs) ≤
          #((setX G w vs).erase x₀) + #(setW G w) := by
        refine card_erase_le.trans ?_
        rw [card_union_of_disjoint hXW]
      rw [card_erase_of_mem hx₀] at h1
      have h5 := five_le (by omega) (by omega) h7 hp
      have hXc := card_pos.2 ⟨x₀, hx₀⟩
      omega

/-- **Chetwynd–Hilton 1989, Theorem 2**, real form: `d ≥ ½(√7 − 1)|V|`. -/
theorem colorable_of_real {d n : ℕ} (hcard : Fintype.card V = 2 * n)
    (hreg : ∀ v, G.degree v = d) (hd : (Real.sqrt 7 - 1) / 2 * (Fintype.card V : ℝ) ≤ d) :
    G.lineGraph.Colorable d :=
  colorable_of_sqrt7 hcard hreg (seven_le_of_real (by rw [← hcard]; exact_mod_cast hd))

end CH89
