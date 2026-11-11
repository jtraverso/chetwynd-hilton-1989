/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import OneFactor.Steps67
public import OneFactor.Main
public import OneFactor.Factors2
public import CH89.Swap

/-!
# Chetwynd–Hilton 1989, Theorem 1 (the factor-peeling engine)

`colorable_of_labelling`: let `G` be `d`-regular on `2n` vertices, `w ≠ v*`, `HV = (X ∪ W) − v*`
with `X ⊆ N(w) − N[v*]`, `Y ⊆ W ∩ N(v*)` missing at most one vertex `y₀` of `W ∩ N(v*)`. Given a
maximal matching `M` of `HV`, a staircase labelling `D` of `insert v* HV` compatible with `M`, and
a bijection `σ : Y → X` such that `σ y` is uncovered by the class of `v* y` for every `y ≠ b`, if
`n + |HV| + 3 ≤ d` then `G` is `d`-edge-colourable.

Proof (CH 1989, §4): peel off the staircase classes (without the edges `v* b`, `v* y₀`) and one
extra step for `v* b` as edge-disjoint near 1-factors of `G − w − M` (`exists_factors_var`); the
rest has the core of Theorem 5 (`core_colorable`); add back the factors missing `v*`, re-insert
`v*` (its only possible neighbour of maximum degree is `y₀`: pivot lemma,
`colorable_of_add_vertex_one`), add the other factors and re-insert `w`.
-/

@[expose] public section

namespace CH89

open SimpleGraph Finset OneFactor

open scoped Classical

attribute [-instance] SimpleGraph.Sdiff.adjDecidable SimpleGraph.Sup.adjDecidable

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Re-inserting a vertex with at most one neighbour of maximum degree** (Lemma 1 of
Chetwynd–Hilton 1985 with `d*(x) ≤ 1`). -/
theorem colorable_of_add_vertex_one (G : SimpleGraph V) [DecidableRel G.Adj] {k : ℕ}
    (hmax : ∀ v, G.degree v ≤ k) (x y₀ : V) (hx : ∀ z, G.Adj x z → z ≠ y₀ → G.degree z < k)
    (hcol : (keepAt G x ∅).lineGraph.Colorable k) : G.lineGraph.Colorable k := by
  by_cases hxy : G.Adj x y₀
  · set G₂ := G.deleteEdges {s(x, y₀)}
    have hle : G₂ ≤ G := deleteEdges_le _
    have hdeg : ∀ v, G₂.degree v ≤ G.degree v := fun v => degree_le_of_le hle
    have hk : keepAt G₂ x ∅ = keepAt G x ∅ := by
      ext a b
      rw [keepAt_empty_adj, keepAt_empty_adj, deleteEdges_adj]
      constructor
      · rintro ⟨⟨h, -⟩, ha, hb⟩; exact ⟨h, ha, hb⟩
      · rintro ⟨h, ha, hb⟩
        refine ⟨⟨h, fun he => ?_⟩, ha, hb⟩
        rcases Sym2.eq_iff.1 (Set.mem_singleton_iff.1 he) with ⟨rfl, -⟩ | ⟨-, rfl⟩
        · exact ha rfl
        · exact hb rfl
    have h2 : G₂.lineGraph.Colorable k := by
      refine colorable_of_add_vertex G₂ (fun v => (hdeg v).trans (hmax v)) x (fun z hz => ?_)
        (hk ▸ hcol)
      rw [deleteEdges_adj] at hz
      have hzy : z ≠ y₀ := fun h => hz.2 (by rw [h]; rfl)
      exact lt_of_le_of_lt (hdeg z) (hx z hz.1 hzy)
    exact colorable_of_pivot G hmax hxy h2 hx
  · exact colorable_of_add_vertex G hmax x (fun z hz => hx z hz fun h => hxy (h ▸ hz)) hcol

variable {G : SimpleGraph V}

/-- **Theorem 1 of Chetwynd–Hilton 1989**, from a labelling and a pairing. -/
theorem colorable_of_labelling {d n : ℕ} (hcard : Fintype.card V = 2 * n)
    (hreg : ∀ v, G.degree v = d) {w vs : V} (hwv : w ≠ vs) {X Y HV : Finset V}
    (hHV : ∀ v, v ∈ HV ↔ v ≠ vs ∧ (v ∈ X ∨ v ∈ setW G w))
    (hXs : X ⊆ setX G w vs) (hYs : Y ⊆ setY G w vs) (hY0 : #(setY G w vs \ Y) ≤ 1)
    (hXY : #X = #Y) {M : SimpleGraph V} (hMv : Valid G HV M)
    (hMmax : ∀ a b, a ∈ HV → b ∈ HV → G.Adj a b → a ∈ cover M ∨ b ∈ cover M)
    (D : StairData (insert vs HV)) (hsvs : D.side vs = true) (hivs : D.idx vs = D.m + 1)
    (hDq : D.q = #HV)
    (hsideM : ∀ u v, M.Adj u v → u ∈ HV ∧ v ∈ HV ∧ D.idx u = D.idx v ∧ D.side u ≠ D.side v)
    (hadjM : ∀ l r, l ∈ HV → r ∈ HV → D.side l = true → D.side r = false → D.idx l = D.idx r →
      M.Adj l r)
    (hRpos : ∀ v ∈ HV, D.side v = false → 1 ≤ D.idx v → v ∈ cover M)
    (hunm : ∀ v ∈ HV, v ∉ cover M → D.side v = false ∧ D.idx v ≤ 0)
    {σ : V → V} {b : V} (hσX : ∀ y ∈ Y, σ y ∈ X)
    (hσinj : ∀ y ∈ Y, ∀ y' ∈ Y, σ y = σ y' → y = y')
    (hgood : ∀ y ∈ Y, y ≠ b → D.Eplus G vs y → σ y ∉ D.cls G (D.stair vs y))
    (hbudget : n + #HV + 3 ≤ d) : G.lineGraph.Colorable d := by
  obtain ⟨hMG, hM, hMS⟩ := hMv
  set G' := keepAt G w ∅ with hG'
  have hvsH : vs ∉ HV := fun h => ((hHV vs).1 h).1 rfl
  have hwH : w ∉ HV := fun h => by
    rcases ((hHV w).1 h).2 with h' | h'
    · exact (mem_setX.1 (hXs h')).1.ne rfl
    · exact (mem_setW.1 h').1 rfl
  have hXH : X ⊆ HV := fun x hx => (hHV x).2 ⟨(mem_setX.1 (hXs hx)).2.1, Or.inl hx⟩
  have hSYH : setY G w vs ⊆ HV := fun y hy =>
    (hHV y).2 ⟨fun e => (mem_setY.1 hy).2.ne e.symm, Or.inr (mem_setW.2 (mem_setY.1 hy).1)⟩
  have hYH : Y ⊆ HV := hYs.trans hSYH
  have hXYd : Disjoint X Y := Finset.disjoint_left.2 fun a ha hb =>
    (mem_setY.1 (hYs hb)).1.2 (mem_setX.1 (hXs ha)).1
  have hσsurj : ∀ x ∈ X, ∃ y ∈ Y, σ y = x := by
    have himg : Y.image σ = X := by
      apply eq_of_subset_of_card_le
      · intro x hx; obtain ⟨y, hy, rfl⟩ := mem_image.1 hx; exact hσX y hy
      · rw [card_image_of_injOn (fun a ha b hb e => hσinj a ha b hb e), hXY]
    intro x hx
    rw [← himg] at hx
    obtain ⟨y, hy, rfl⟩ := mem_image.1 hx
    exact ⟨y, hy, rfl⟩
  -- the edges of the staircase at `v*`
  have hEvs : ∀ y, D.Eplus G vs y ↔ y ∈ setY G w vs := by
    intro y
    constructor
    · rintro ⟨-, hy, hadj, -⟩
      have hyH : y ∈ HV := (mem_insert.1 hy).resolve_left fun e => hadj.ne e.symm
      rcases ((hHV y).1 hyH).2 with h | h
      · exact absurd hadj (mem_setX.1 (hXs h)).2.2
      · exact mem_setY.2 ⟨mem_setW.1 h, hadj⟩
    · intro hy
      refine ⟨mem_insert_self _ _, mem_insert_of_mem (hSYH hy), (mem_setY.1 hy).2, ?_⟩
      cases hs : D.side y
      · have := D.hR y (mem_insert_of_mem (hSYH hy)) hs
        exact Or.inr (Or.inl ⟨hsvs, rfl, by omega⟩)
      · exact Or.inl ⟨hsvs, rfl⟩
  have hMnotE : ∀ u v, M.Adj u v → ¬ D.Eplus G u v := by
    intro u v huv hE
    obtain ⟨-, -, he, hne⟩ := hsideM u v huv
    obtain ⟨-, -, -, h⟩ := hE
    rcases h with ⟨h1, h2⟩ | ⟨-, -, h3⟩ | ⟨-, -, h3⟩
    · exact hne (h1.trans h2.symm)
    · omega
    · omega
  -- the steps
  obtain ⟨q, hq⟩ : ∃ q, q = #HV := ⟨_, rfl⟩
  set Ex := insert b (setY G w vs \ Y)
  have hbY : b ∈ Y ∨ b ∉ Y := em _
  let C : ℕ → SimpleGraph V := fun k =>
    if k < q then stairClass D G vs Ex ((k : ℤ) + 1)
    else if k = q ∧ b ∈ Y then SimpleGraph.fromEdgeSet {s(vs, b)} else ⊥
  let mis : ℕ → V := fun k =>
    if k < q then
      (if h : ∃ y, y ∈ Y ∧ y ≠ b ∧ D.stair vs y = (k : ℤ) + 1 then σ h.choose else vs)
    else if k = q ∧ b ∈ Y then σ b else vs
  have hC1 : ∀ k < q, C k = stairClass D G vs Ex ((k : ℤ) + 1) := fun k hk => by
    simp only [C, if_pos hk]
  have hCq : ∀ a c, (C q).Adj a c ↔ b ∈ Y ∧ s(a, c) = s(vs, b) ∧ a ≠ c := by
    intro a c
    simp only [C, lt_irrefl, if_false, true_and]
    by_cases hb : b ∈ Y
    · simp [hb, fromEdgeSet_adj]
    · simp [hb]
  have hstair : ∀ y ∈ setY G w vs, 1 ≤ D.stair vs y ∧ D.stair vs y ≤ q := fun y hy =>
    ⟨D.stair_pos ((hEvs y).2 hy), by have := D.stair_le ((hEvs y).2 hy); omega⟩
  -- the step of each `y ∈ Y`
  let stepOf : V → ℕ := fun y => if y = b then q else (D.stair vs y - 1).toNat
  have hmis_eq : ∀ y ∈ Y, ∀ k, k ≤ q → (mis k = σ y ↔ k = stepOf y) := by
    intro y hy k hkq
    have hσy := hσX y hy
    have hσne : σ y ≠ vs := fun h => (mem_setX.1 (hXs (h ▸ hσy))).2.1 rfl
    simp only [mis, stepOf]
    constructor
    · intro hk
      split_ifs at hk with h1 h2 h3
      · have hy' := hσinj _ h2.choose_spec.1 y hy hk
        have hb := h2.choose_spec.2.1
        have hst := h2.choose_spec.2.2
        rw [hy'] at hb hst
        rw [if_neg hb, hst]; omega
      · exact absurd hk.symm hσne
      · have hy' := hσinj _ h3.2 y hy hk
        rw [← hy', if_pos rfl]; exact h3.1
      · exact absurd hk.symm hσne
    · intro hk
      by_cases hb : y = b
      · subst hb
        rw [if_pos rfl] at hk
        subst hk
        rw [if_neg (lt_irrefl _), if_pos ⟨rfl, hy⟩]
      · rw [if_neg hb] at hk
        have hs := hstair y (hYs hy)
        have hkq' : k < q := by omega
        have hex : ∃ y', y' ∈ Y ∧ y' ≠ b ∧ D.stair vs y' = (k : ℤ) + 1 := ⟨y, hy, hb, by omega⟩
        rw [if_pos hkq', dif_pos hex]
        congr 1
        exact D.stair_inj ((hEvs _).2 (hYs hex.choose_spec.1)) ((hEvs _).2 (hYs hy))
          (by rw [hex.choose_spec.2.2]; omega)
  have hstep_le : ∀ y ∈ Y, stepOf y ≤ q := fun y hy => by
    simp only [stepOf]; split_ifs
    · exact le_rfl
    · have := hstair y (hYs hy); omega
  have hmis_mem : ∀ k, mis k ∈ X ∨ mis k = vs := by
    intro k
    simp only [mis]
    split_ifs with h1 h2 h3
    · exact Or.inl (hσX _ h2.choose_spec.1)
    · exact Or.inr rfl
    · exact Or.inl (hσX _ h3.2)
    · exact Or.inr rfl
  -- the factors
  have hdegM : ∀ v, M.degree v ≤ 1 := fun v => by
    by_cases hv : v ∈ cover M
    · rw [degree_eq_one_of_matching hM hv]
    · rw [degree_eq_zero_of_not_cover hv]; exact zero_le_one
  have hdegG' : ∀ v, v ≠ w → G'.degree v + (if G.Adj v w then 1 else 0) = d :=
    fun v hv => by rw [degree_keepAt_empty_add G w hv, hreg]
  have hMG' : M ≤ G' := fun a c h => (keepAt_empty_adj G w).2
    ⟨hMG h, fun e => hwH (e ▸ (hMS a c h).1), fun e => hwH (e ▸ (hMS a c h).2)⟩
  have hCle : ∀ k, C k ≤ G' \ M := by
    intro k a c hac
    rcases lt_or_ge k q with hk | hk
    · rw [hC1 k hk] at hac
      have hE := hac.1
      have hwS : w ∉ insert vs HV := fun h => (mem_insert.1 h).elim hwv hwH
      exact ⟨(keepAt_empty_adj G w).2 ⟨hE.2.2.1, fun h => hwS (h ▸ hE.1),
        fun h => hwS (h ▸ hE.2.1)⟩, fun hM' => hMnotE a c hM' hE⟩
    · by_cases hkq : k = q
      · subst hkq
        obtain ⟨hb, he, -⟩ := (hCq a c).1 hac
        have hGv : G.Adj vs b := (mem_setY.1 (hYs hb)).2
        have hbH := hYH hb
        rcases Sym2.eq_iff.1 he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact ⟨(keepAt_empty_adj G w).2 ⟨hGv, hwv.symm, fun h => hwH (h ▸ hbH)⟩,
            fun h => hvsH (hMS _ _ h).1⟩
        · exact ⟨(keepAt_empty_adj G w).2 ⟨hGv.symm, fun h => hwH (h ▸ hbH), hwv.symm⟩,
            fun h => hvsH (hMS _ _ h).2⟩
      · simp only [C, if_neg (show ¬ k < q by omega), hkq, false_and, if_false] at hac
        exact absurd hac (by simp)
  have hCm : ∀ k, IsMatchingGraph (C k) := by
    intro k
    rcases lt_or_ge k q with hk | hk
    · rw [hC1 k hk]; exact stairClass_matching _
    · by_cases hkq : k = q
      · subst hkq
        intro v a c ha hc
        obtain ⟨-, h1, h2⟩ := (hCq v a).1 ha
        obtain ⟨-, h3, h4⟩ := (hCq v c).1 hc
        rcases Sym2.eq_iff.1 h1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
          rcases Sym2.eq_iff.1 h3 with ⟨h5, rfl⟩ | ⟨h5, rfl⟩ <;>
          first
          | rfl
          | exact absurd h5 h2
          | exact absurd h5.symm h2
          | exact absurd h5 h4
          | exact absurd h5.symm h4
      · intro v a c ha
        simp only [C, if_neg (show ¬ k < q by omega), hkq, false_and, if_false] at ha
        exact absurd ha (by simp)
  have hCb : ∀ k < q + 1, 2 * n + #(cover (C k)) + 2 * k ≤ 2 * (d - 2) := by
    intro k hk
    rcases lt_or_ge k q with hkq | hkq
    · rw [hC1 k hkq]
      have h1 := card_le_card (cover_stairClass_subset (D := D) (G := G) (vs := vs) (Bad := Ex)
        ((k : ℤ) + 1))
      have h2 := D.card_cls_le (G := G) (i := (k : ℤ) + 1) (by omega)
      omega
    · have hk' : k = q := by omega
      subst hk'
      have : cover (C k) ⊆ {vs, b} := by
        intro v hv
        obtain ⟨u, hu⟩ := mem_cover.1 hv
        obtain ⟨-, h3, -⟩ := (hCq v u).1 hu
        rcases Sym2.eq_iff.1 h3 with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> simp
      have h1 := card_le_card this
      have h2 : #({vs, b} : Finset V) ≤ 2 := card_le_two
      omega
  have hmw : ∀ k, mis k ≠ w := fun k h => by
    rcases hmis_mem k with h' | h'
    · rw [h] at h'; exact (mem_setX.1 (hXs h')).1.ne rfl
    · exact hwv (h.symm.trans h')
  have hmC : ∀ k u, ¬ (C k).Adj (mis k) u := by
    intro k u hadj
    rcases lt_or_ge k q with hkq | hkq
    · rw [hC1 k hkq] at hadj
      by_cases hex : ∃ y, y ∈ Y ∧ y ≠ b ∧ D.stair vs y = (k : ℤ) + 1
      · have hmk : mis k = σ hex.choose := by simp only [mis, if_pos hkq, dif_pos hex]
        obtain ⟨hy, hb, hst⟩ := hex.choose_spec
        rw [hmk] at hadj
        apply hgood _ hy hb ((hEvs _).2 (hYs hy))
        rw [hst]
        exact (StairData.mem_cls _ _).2 ⟨hadj.1.1, u, hadj.1, hadj.2.1⟩
      · have hmk : mis k = vs := by simp only [mis, if_pos hkq, dif_neg hex]
        rw [hmk] at hadj
        obtain ⟨hE, hst, hb1, -⟩ := hadj
        have huY := (hEvs u).1 hE
        have huY' : u ∈ Y := by
          by_contra h
          exact hb1 ⟨rfl, mem_insert_of_mem (mem_sdiff.2 ⟨huY, h⟩)⟩
        have hub : u ≠ b := fun h => hb1 ⟨rfl, h ▸ mem_insert_self _ _⟩
        exact hex ⟨u, huY', hub, hst⟩
    · by_cases hk : k = q ∧ b ∈ Y
      · obtain ⟨rfl, hb⟩ := hk
        have hmk : mis k = σ b := by simp [mis, hb]
        rw [hmk] at hadj
        obtain ⟨-, h1, -⟩ := (hCq _ u).1 hadj
        have hxX := hσX b hb
        rcases Sym2.eq_iff.1 h1 with ⟨h2, -⟩ | ⟨h2, -⟩
        · exact (mem_setX.1 (hXs hxX)).2.1 h2
        · exact Finset.disjoint_left.1 hXYd hxX (by rw [h2]; exact hb)
      · simp only [C, if_neg (show ¬ k < q by omega), if_neg hk] at hadj
        exact absurd hadj (by simp)
  obtain ⟨F, hF, hdisj, hCF⟩ := exists_factors_var (G' \ M) (n := n) (N := q + 1) (D₀ := d - 2)
    hcard w (fun u h => ((keepAt_empty_adj G w).1 h.1).2.1 rfl)
    (fun v hv => by
      have h1 := Plantholt.degree_sdiff_add _ hMG' v
      have h2 := hdegM v
      have h3 := hdegG' v hv
      split_ifs at h3 <;> omega)
    C mis hCle hCm hCb hmw hmC
  -- facts about the factors
  set N := q + 1 with hN
  have hFle : ∀ k < N, F k ≤ G' := fun k hk => (hF k hk).le.trans sdiff_le
  have hFM : ∀ k < N, ∀ a c, (F k).Adj a c → ¬ M.Adj a c := fun k hk a c h => ((hF k hk).le h).2
  have hdisjR : ∀ j ∈ range N, ∀ k ∈ range N, j ≠ k → Disjoint (F j) (F k) := by
    intro j hj k hk hjk
    rcases lt_or_gt_of_ne hjk with h | h
    · exact hdisj j k h (mem_range.1 hk)
    · exact (hdisj k j h (mem_range.1 hj)).symm
  have hmatch : ∀ k ∈ range N, IsMatchingGraph (F k) := fun k hk => (hF k (mem_range.1 hk)).matching
  -- every staircase edge not at `v* y₀` lies in a factor
  have hHedge : ∀ a c, D.Eplus G a c → ¬ (a = vs ∧ c ∈ setY G w vs \ Y) →
      ¬ (c = vs ∧ a ∈ setY G w vs \ Y) → ∃ j < N, (F j).Adj a c := by
    intro a c hE h1 h2
    have key : ∀ k < N, (C k).Adj a c → ∃ j < N, (F j).Adj a c := fun k hk hC => by
      obtain ⟨j, hj, hj'⟩ := (finsetSup_adj _).1 (hCF k hk hC)
      exact ⟨j, by have := mem_range.1 hj; omega, hj'⟩
    by_cases hb1 : a = vs ∧ c = b
    · obtain ⟨rfl, rfl⟩ := hb1
      have hcY : c ∈ Y := by
        by_contra h; exact h1 ⟨rfl, mem_sdiff.2 ⟨(hEvs c).1 hE, h⟩⟩
      exact key q (by omega) ((hCq _ _).2 ⟨hcY, rfl, hE.2.2.1.ne⟩)
    by_cases hb2 : c = vs ∧ a = b
    · obtain ⟨rfl, rfl⟩ := hb2
      have haY : a ∈ Y := by
        by_contra h; exact h2 ⟨rfl, mem_sdiff.2 ⟨(hEvs a).1 hE.symm, h⟩⟩
      exact key q (by omega) ((hCq _ _).2 ⟨haY, Sym2.eq_swap, hE.2.2.1.ne⟩)
    have hs1 := D.stair_pos hE
    have hs2 := D.stair_le hE
    obtain ⟨k, hk⟩ : ∃ k, k = (D.stair a c - 1).toNat := ⟨_, rfl⟩
    have hkq : k < q := by omega
    refine key k (by omega) ?_
    rw [hC1 k hkq]
    refine ⟨hE, by omega, fun ⟨e1, e2⟩ => ?_, fun ⟨e1, e2⟩ => ?_⟩
    · rcases mem_insert.1 e2 with e | e
      · exact hb1 ⟨e1, e⟩
      · exact h1 ⟨e1, e⟩
    · rcases mem_insert.1 e2 with e | e
      · exact hb2 ⟨e1, e⟩
      · exact h2 ⟨e1, e⟩
  -- the missed counts
  have hcntX : ∀ x ∈ X, ∀ T ⊆ range N, (∀ y ∈ Y, σ y = x → stepOf y ∈ T) →
      #(T.filter fun k => x ≠ w ∧ x ≠ mis k) + 1 = #T := fun x hx T hT hst => by
    obtain ⟨y, hy, rfl⟩ := hσsurj x hx
    have : T.filter (fun k => σ y ≠ w ∧ σ y ≠ mis k) = T.erase (stepOf y) := by
      ext k
      simp only [mem_filter, mem_erase]
      have hxw : σ y ≠ w := (mem_setX.1 (hXs (hσX y hy))).1.ne'
      constructor
      · rintro ⟨hk, -, hne⟩
        exact ⟨fun e => hne ((hmis_eq y hy k (by have := mem_range.1 (hT hk); omega)).2 e).symm, hk⟩
      · rintro ⟨hne, hk⟩
        exact ⟨hk, hxw, fun e => hne ((hmis_eq y hy k
          (by have := mem_range.1 (hT hk); omega)).1 e.symm)⟩
    rw [this, card_erase_add_one (hst y hy rfl)]
  have hcntO : ∀ v, v ≠ w → v ∉ X → v ≠ vs → ∀ T : Finset ℕ,
      #(T.filter fun k => v ≠ w ∧ v ≠ mis k) = #T := fun v hvw hvX hvs T => by
    congr 1
    rw [filter_eq_self]
    intro k _
    refine ⟨hvw, fun he' => ?_⟩
    rcases hmis_mem k with h | h
    · exact hvX (he' ▸ h)
    · exact hvs (he'.trans h)
  have hXadj : ∀ x ∈ X, G.Adj x w := fun x hx => (mem_setX.1 (hXs hx)).1.symm
  have hnotW : ∀ v, v ≠ w → v ∉ setW G w → G.Adj v w := fun v hv hW => by
    by_contra h; exact hW (mem_setW.2 ⟨hv, fun h' => h h'.symm⟩)
  have hstepR : ∀ x ∈ X, ∀ y ∈ Y, σ y = x → stepOf y ∈ range N :=
    fun x _ y hy _ => mem_range.2 (by have := hstep_le y hy; omega)
  -- Phase 1: the core
  obtain ⟨U, hU⟩ : ∃ U, U = (range N).sup F := ⟨_, rfl⟩
  have hUle : U ≤ G' := hU ▸ Finset.sup_le fun k hk => hFle k (mem_range.1 hk)
  have hdegU : ∀ v, U.degree v = #((range N).filter fun k => v ≠ w ∧ v ≠ mis k) := fun v => by
    subst hU; exact degree_finsetSup_factors hF hdisjR subset_rfl v
  have hdegGU : ∀ v, (G' \ U).degree v + U.degree v = G'.degree v :=
    fun v => Plantholt.degree_sdiff_add _ hUle v
  set G₁ := keepAt (G' \ U) vs ∅
  have hdeg1 : ∀ v, G₁.degree v ≤ (G' \ U).degree v := fun v =>
    degree_le_of_le (keepAt_le _ vs ∅)
  have hmax1 : ∀ v, G₁.degree v ≤ d - N := by
    intro v
    have h1 := hdeg1 v
    have h2 := hdegGU v
    have h3 := hdegU v
    by_cases hvw : v = w
    · have : G'.degree v = 0 := by rw [hvw]; exact degree_keepAt_empty_self G w
      omega
    have h4 := hdegG' v hvw
    by_cases hvX : v ∈ X
    · have h5 := hcntX v hvX _ subset_rfl (hstepR v hvX)
      rw [card_range] at h5
      rw [if_pos (hXadj v hvX)] at h4
      omega
    · by_cases hvs : v = vs
      · subst hvs; rw [degree_keepAt_empty_self]; exact Nat.zero_le _
      · have h5 := hcntO v hvw hvX hvs (range N)
        rw [card_range] at h5
        split_ifs at h4 <;> omega
  have hsmall1 : ∀ v, v ∉ HV → G₁.degree v < d - N := by
    intro v hvH
    by_cases hvs : v = vs
    · subst hvs; rw [degree_keepAt_empty_self]; omega
    have h1 := hdeg1 v
    have h2 := hdegGU v
    have h3 := hdegU v
    by_cases hvw : v = w
    · have : G'.degree v = 0 := by rw [hvw]; exact degree_keepAt_empty_self G w
      omega
    have hvX : v ∉ X := fun h => hvH (hXH h)
    have hvW : v ∉ setW G w := fun h => hvH ((hHV v).2 ⟨hvs, Or.inr h⟩)
    have h4 := hdegG' v hvw
    rw [if_pos (hnotW v hvw hvW)] at h4
    have h5 := hcntO v hvw hvX hvs (range N)
    rw [card_range] at h5
    omega
  have hG1col : G₁.lineGraph.Colorable (d - N) := by
    refine core_colorable D (subset_insert vs _) M _ hmax1 hsmall1 ?_ hM hsideM hadjM hRpos hunm
      ?_ ?_
    · intro a c hac
      obtain ⟨ha, hc⟩ := hMS a c hac
      refine (keepAt_empty_adj _ vs).2 ⟨⟨hMG' hac, fun hU' => ?_⟩, fun h => hvsH (h ▸ ha),
        fun h => hvsH (h ▸ hc)⟩
      rw [hU] at hU'
      obtain ⟨k, hk, hk'⟩ := (finsetSup_adj _).1 hU'
      exact hFM k (mem_range.1 hk) a c hk' hac
    · intro u v hu hv huv
      exact hMmax u v hu hv ((keepAt_empty_adj G w).1 (keepAt_le _ vs ∅ huv).1).1
    · intro u v hu hv huv
      have h1 := keepAt_le _ vs ∅ huv
      have hnE : ¬ D.Eplus G u v := by
        intro hE
        obtain ⟨j, hj, hj'⟩ := hHedge u v hE (fun h => hvsH (h.1 ▸ hu))
          (fun h => hvsH (h.1 ▸ hv))
        apply h1.2
        rw [hU]
        exact (finsetSup_adj _).2 ⟨j, mem_range.2 hj, hj'⟩
      have hGuv : G.Adj u v := ((keepAt_empty_adj G w).1 h1.1).1
      have huS : u ∈ insert vs HV := mem_insert_of_mem hu
      have hvS : v ∈ insert vs HV := mem_insert_of_mem hv
      cases hsu : D.side u <;> cases hsv : D.side v
      · exact Or.inl ⟨rfl, rfl⟩
      · right; right
        refine ⟨rfl, rfl, ?_⟩
        by_contra hlt
        exact hnE ⟨huS, hvS, hGuv, Or.inr (Or.inr ⟨hsu, hsv, by omega⟩)⟩
      · right; left
        refine ⟨rfl, rfl, ?_⟩
        by_contra hlt
        exact hnE ⟨huS, hvS, hGuv, Or.inr (Or.inl ⟨hsu, hsv, by omega⟩)⟩
      · exact absurd ⟨huS, hvS, hGuv, Or.inl ⟨hsu, hsv⟩⟩ hnE
  -- Phase 2: the factors missing `v*`
  obtain ⟨J, hJ⟩ : ∃ J, J = (range N).filter fun k => mis k = vs := ⟨_, rfl⟩
  obtain ⟨A, hA⟩ : ∃ A, A = (range N).filter fun k => ¬ mis k = vs := ⟨_, rfl⟩
  have hJsub : J ⊆ range N := hJ ▸ filter_subset _ _
  have hAsub : A ⊆ range N := hA ▸ filter_subset _ _
  have hAJ : #J + #A = N := by rw [hJ, hA, card_filter_add_card_filter_not, card_range]
  have hG2col : (G₁ ⊔ J.sup F).lineGraph.Colorable (d - N + #J) := by
    refine colorable_sup_family J (fun k hk => hmatch k (hJsub hk)) (fun k hk => ?_)
      (fun a ha c hc hac => hdisjR a (hJsub ha) c (hJsub hc) hac) hG1col
    have hFU : F k ≤ U := hU ▸ le_sup (f := F) (hJsub hk)
    exact (disjoint_sdiff_self_left.mono_left (keepAt_le _ vs ∅)).mono_right hFU
  -- Phase 3
  have hAle : A.sup F ≤ G' := Finset.sup_le fun k hk => hFle k (mem_range.1 (hAsub hk))
  have heq : keepAt (G' \ A.sup F) vs ∅ = G₁ ⊔ J.sup F := by
    ext a c
    rw [keepAt_empty_adj, sup_adj, keepAt_empty_adj, sdiff_adj, sdiff_adj, finsetSup_adj,
      finsetSup_adj, hU, finsetSup_adj]
    constructor
    · rintro ⟨⟨hac, hA'⟩, ha, hc⟩
      by_cases hU' : ∃ k ∈ range N, (F k).Adj a c
      · obtain ⟨k, hk, hk'⟩ := hU'
        have hmk : mis k = vs := by
          by_contra hne
          exact hA' ⟨k, by rw [hA]; exact mem_filter.2 ⟨hk, hne⟩, hk'⟩
        exact Or.inr ⟨k, by rw [hJ]; exact mem_filter.2 ⟨hk, hmk⟩, hk'⟩
      · exact Or.inl ⟨⟨hac, hU'⟩, ha, hc⟩
    · rintro (⟨⟨hac, hU'⟩, ha, hc⟩ | ⟨k, hk, hk'⟩)
      · exact ⟨⟨hac, fun ⟨j, hj, hj'⟩ => hU' ⟨j, hAsub hj, hj'⟩⟩, ha, hc⟩
      · have hkN := mem_range.1 (hJsub hk)
        have hmk : mis k = vs := by rw [hJ] at hk; exact (mem_filter.1 hk).2
        refine ⟨⟨hFle k hkN hk', fun ⟨j, hj, hj'⟩ => ?_⟩, fun ha => ?_, fun hc => ?_⟩
        · have hjk : j ≠ k := fun h => by
            rw [hA] at hj; exact (mem_filter.1 hj).2 (h ▸ hmk)
          exact (disjoint_iff_inf_le.1 (hdisjR j (hAsub hj) k (hJsub hk) hjk)) ⟨hj', hk'⟩
        · exact (hF k hkN).miss_m c (by rw [hmk, ← ha]; exact hk')
        · exact (hF k hkN).miss_m a (by rw [hmk, ← hc]; exact hk'.symm)
  have hG3col : (keepAt (G' \ A.sup F) vs ∅).lineGraph.Colorable (d - #A) := by
    rw [heq]
    have : d - N + #J = d - #A := by omega
    rw [← this]; exact hG2col
  -- Phase 4: re-insert `v*`
  have hdegA : ∀ v, (A.sup F).degree v = #(A.filter fun k => v ≠ w ∧ v ≠ mis k) :=
    fun v => degree_finsetSup_factors hF hdisjR hAsub v
  have hdegG3 : ∀ v, (G' \ A.sup F).degree v + (A.sup F).degree v = G'.degree v :=
    fun v => Plantholt.degree_sdiff_add _ hAle v
  have hstepA : ∀ x ∈ X, ∀ y ∈ Y, σ y = x → stepOf y ∈ A := fun x hx y hy hxy => by
    rw [hA]
    refine mem_filter.2 ⟨mem_range.2 (by have := hstep_le y hy; omega), fun h => ?_⟩
    have := (hmis_eq y hy (stepOf y) (hstep_le y hy)).2 rfl
    rw [h] at this
    exact (mem_setX.1 (hXs (this ▸ hσX y hy))).2.1 rfl
  have hmax3 : ∀ v, (G' \ A.sup F).degree v ≤ d - #A := by
    intro v
    have h1 := hdegG3 v
    have h2 := hdegA v
    by_cases hvw : v = w
    · have : G'.degree v = 0 := by rw [hvw]; exact degree_keepAt_empty_self G w
      omega
    have h4 := hdegG' v hvw
    by_cases hvX : v ∈ X
    · have h5 := hcntX v hvX A hAsub (hstepA v hvX)
      rw [if_pos (hXadj v hvX)] at h4
      omega
    · by_cases hvs : v = vs
      · subst hvs
        have h5 : A.filter (fun k => v ≠ w ∧ v ≠ mis k) = A := by
          rw [filter_eq_self]
          intro k hk
          rw [hA] at hk
          exact ⟨hvw, fun he' => (mem_filter.1 hk).2 he'.symm⟩
        rw [h5] at h2
        split_ifs at h4 <;> omega
      · have h5 := hcntO v hvw hvX hvs A
        split_ifs at h4 <;> omega
  obtain ⟨y₀, hy₀⟩ : ∃ y₀, setY G w vs \ Y ⊆ {y₀} := by
    rcases (setY G w vs \ Y).eq_empty_or_nonempty with h | ⟨y₀, hy₀⟩
    · exact ⟨vs, by rw [h]; exact empty_subset _⟩
    · exact ⟨y₀, fun z hz => mem_singleton.2 (card_le_one.1 hY0 z hz y₀ hy₀)⟩
  have hx3 : ∀ z, (G' \ A.sup F).Adj vs z → z ≠ y₀ → (G' \ A.sup F).degree z < d - #A := by
    intro z hz hzy
    obtain ⟨hGz, hvsw', hzw⟩ := (keepAt_empty_adj G w).1 hz.1
    have hzX : z ∉ X := fun h => (mem_setX.1 (hXs h)).2.2 hGz
    have hzs : z ≠ vs := hGz.ne'
    have hzW : z ∉ setW G w := by
      intro hzW
      have hzY : z ∈ setY G w vs := mem_setY.2 ⟨mem_setW.1 hzW, hGz⟩
      have hzY' : z ∈ Y := by
        by_contra h
        exact hzy (mem_singleton.1 (hy₀ (mem_sdiff.2 ⟨hzY, h⟩)))
      obtain ⟨j, hj, hj'⟩ := hHedge vs z ((hEvs z).2 hzY)
        (fun h => (mem_sdiff.1 h.2).2 hzY') (fun h => hzs h.1)
      have hmj : ¬ mis j = vs := fun h => (hF j hj).miss_m z (by rw [h]; exact hj')
      exact hz.2 ((finsetSup_adj _).2 ⟨j, by rw [hA]; exact mem_filter.2 ⟨mem_range.2 hj, hmj⟩,
        hj'⟩)
    have h1 := hdegG3 z
    have h2 := hdegA z
    have h4 := hdegG' z hzw
    rw [if_pos (hnotW z hzw hzW)] at h4
    have h5 := hcntO z hzw hzX hzs A
    omega
  have hG3full := colorable_of_add_vertex_one _ hmax3 vs y₀ hx3 hG3col
  -- Phase 5: the factors through `v*`
  have hG'col : G'.lineGraph.Colorable d := by
    have := colorable_sup_family (B := G' \ A.sup F) A (fun k hk => hmatch k (hAsub hk))
      (fun k hk => disjoint_sdiff_self_left.mono_right (le_sup (f := F) hk))
      (fun a ha c hc hac => hdisjR a (hAsub ha) c (hAsub hc) hac) hG3full
    rw [sdiff_sup_cancel hAle, Nat.sub_add_cancel (by omega)] at this
    exact this
  -- Phase 6: re-insert `w`
  exact colorable_of_regular_keepAt G ⟨n, by omega⟩ hreg w hG'col


end CH89
