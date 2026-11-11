/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import OneFactor.Label67

/-!
# Choosing the matching `M₀` (the repair of the ordering step)

`HV` is split into `X`, `Y` and the rest. For a matching `M` inside `HV`, `tsum M HV X Y` is
`u_Y − u_X − μ`, where `u_X, u_Y` count the unmatched vertices of `X, Y` and `μ` the vertices of
`X ∪ Y` matched outside their own class (`Mixed`). We show (`exists_good_matching`) that, if every
`y ∈ Y` has at most `|HV| − |Y|` non-neighbours in `HV − y` and every `x ∈ X` at most
`|HV| − |X|`, some maximal matching has `tsum M HV X Y ≤ 1` and `tsum M HV Y X ≤ 1`: minimize
`−K·#cover + max(T, T′)`; an unmatched `y` adjacent to a vertex `v` of an edge `v v′` with
`v, v′ ∉ Y` can take `v` (`swap`), which lowers `T` by `2` and raises `T′` by at most `2`; if no such
move exists, counting the non-neighbours of an unmatched `y` gives `T ≤ 1`.
-/

@[expose] public section

namespace CH89

open SimpleGraph Finset OneFactor

open scoped Classical

attribute [-instance] SimpleGraph.Sdiff.adjDecidable SimpleGraph.Sup.adjDecidable

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A matching of `G` inside `HV`. -/
def Valid (G : SimpleGraph V) (HV : Finset V) (M : SimpleGraph V) : Prop :=
  M ≤ G ∧ IsMatchingGraph M ∧ ∀ a b, M.Adj a b → a ∈ HV ∧ b ∈ HV

/-- `+1` on `X`, `−1` on `Y`. -/
def hval (X Y : Finset V) (v : V) : ℤ := if v ∈ X then 1 else if v ∈ Y then -1 else 0

/-- `v` is matched outside its own class. -/
def Mixed (M : SimpleGraph V) (X Y : Finset V) (v : V) : Prop :=
  (v ∈ X ∧ ∃ u, M.Adj v u ∧ u ∉ X) ∨ (v ∈ Y ∧ ∃ u, M.Adj v u ∧ u ∉ Y)

/-- The contribution of `v` to `u_Y − u_X − μ`. -/
noncomputable def tau (M : SimpleGraph V) (X Y : Finset V) (v : V) : ℤ :=
  if ∃ u, M.Adj v u then (if Mixed M X Y v then -1 else 0) else -hval X Y v

/-- `u_Y − u_X − μ`. -/
noncomputable def tsum (M : SimpleGraph V) (HV X Y : Finset V) : ℤ := ∑ v ∈ HV, tau M X Y v

theorem mixed_comm {M : SimpleGraph V} {X Y : Finset V} {v : V} : Mixed M Y X v ↔ Mixed M X Y v :=
  Or.comm

theorem tau_bounds (M : SimpleGraph V) (X Y : Finset V) (v : V) :
    -1 ≤ tau M X Y v ∧ tau M X Y v ≤ 1 := by
  unfold tau hval; split_ifs <;> omega

theorem tau_add_le {X Y : Finset V} (hXY : Disjoint X Y) (M : SimpleGraph V) (v : V) :
    tau M X Y v + tau M Y X v ≤ 0 := by
  have e : Mixed M Y X v ↔ Mixed M X Y v := mixed_comm
  have hv : v ∈ X → v ∉ Y := fun h => Finset.disjoint_left.1 hXY h
  unfold tau hval
  by_cases a : ∃ u, M.Adj v u
  · rw [if_pos a, if_pos a]
    by_cases b : Mixed M X Y v
    · rw [if_pos b, if_pos (e.2 b)]; omega
    · rw [if_neg b, if_neg (fun c => b (e.1 c))]; omega
  · rw [if_neg a, if_neg a]
    by_cases hx : v ∈ X
    · simp [hx, hv hx]
    · by_cases hy : v ∈ Y <;> simp [hx, hy]

theorem tsum_bounds (M : SimpleGraph V) (HV X Y : Finset V) :
    -(#HV : ℤ) ≤ tsum M HV X Y ∧ tsum M HV X Y ≤ #HV := by
  unfold tsum
  constructor
  · have := sum_le_sum (s := HV) fun v _ => (tau_bounds M X Y v).1
    simpa using this
  · have := sum_le_sum (s := HV) fun v _ => (tau_bounds M X Y v).2
    simpa using this

theorem tsum_add_le {X Y : Finset V} (hXY : Disjoint X Y) (M : SimpleGraph V) (HV : Finset V) :
    tsum M HV X Y + tsum M HV Y X ≤ 0 := by
  unfold tsum
  rw [← sum_add_distrib]
  exact sum_nonpos fun v _ => tau_add_le hXY M v

theorem tau_congr {M M' : SimpleGraph V} {X Y : Finset V} {z : V} (h : ∀ u, M.Adj z u ↔ M'.Adj z u) :
    tau M X Y z = tau M' X Y z := by
  have h1 : (∃ u, M.Adj z u) ↔ ∃ u, M'.Adj z u := exists_congr h
  have h2 : Mixed M X Y z ↔ Mixed M' X Y z := by unfold Mixed; simp_rw [h]
  unfold tau
  by_cases a : ∃ u, M.Adj z u
  · rw [if_pos a, if_pos (h1.1 a)]
    by_cases b : Mixed M X Y z
    · rw [if_pos b, if_pos (h2.1 b)]
    · rw [if_neg b, if_neg (fun c => b (h2.2 c))]
  · rw [if_neg a, if_neg (fun c => a (h1.2 c))]

/-! ### Adding an edge -/

theorem add_edge {G : SimpleGraph V} {HV : Finset V} {M : SimpleGraph V} (hM : Valid G HV M)
    {a b : V} (ha : a ∈ HV) (hb : b ∈ HV) (hab : G.Adj a b) (hac : a ∉ cover M)
    (hbc : b ∉ cover M) :
    Valid G HV (M ⊔ fromEdgeSet {s(a, b)}) ∧ #(cover (M ⊔ fromEdgeSet {s(a, b)})) = #(cover M) + 2 := by
  obtain ⟨hMG, hMm, hMS⟩ := hM
  have hna : ∀ u, ¬ M.Adj a u := fun u h => hac (mem_cover.2 ⟨u, h⟩)
  have hnb : ∀ u, ¬ M.Adj b u := fun u h => hbc (mem_cover.2 ⟨u, h⟩)
  have hadj : ∀ u v, (M ⊔ fromEdgeSet {s(a, b)}).Adj u v ↔ M.Adj u v ∨ (s(u, v) = s(a, b) ∧ u ≠ v) := by
    intro u v; simp [fromEdgeSet_adj]
  have hne : a ≠ b := hab.ne
  refine ⟨⟨fun u v h => ?_, fun v x y hx hy => ?_, fun u v h => ?_⟩, ?_⟩
  · rcases (hadj u v).1 h with h | ⟨he, -⟩
    · exact hMG h
    · rcases Sym2.eq_iff.1 he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hab
      · exact hab.symm
  · rcases (hadj v x).1 hx with hxM | ⟨hex, hvx⟩ <;>
      rcases (hadj v y).1 hy with hyM | ⟨hey, hvy⟩
    · exact hMm v x y hxM hyM
    · exfalso
      rcases Sym2.eq_iff.1 hey with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hna x hxM
      · exact hnb x hxM
    · exfalso
      rcases Sym2.eq_iff.1 hex with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hna y hyM
      · exact hnb y hyM
    · rcases Sym2.eq_iff.1 hex with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
        rcases Sym2.eq_iff.1 hey with ⟨h1, rfl⟩ | ⟨h1, rfl⟩ <;> simp_all
  · rcases (hadj u v).1 h with h | ⟨he, -⟩
    · exact hMS u v h
    · rcases Sym2.eq_iff.1 he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨ha, hb⟩
      · exact ⟨hb, ha⟩
  · have : cover (M ⊔ fromEdgeSet {s(a, b)}) = insert a (insert b (cover M)) := by
      ext z
      simp only [mem_cover, hadj, mem_insert]
      constructor
      · rintro ⟨u, hu | ⟨he, -⟩⟩
        · exact Or.inr (Or.inr ⟨u, hu⟩)
        · rcases Sym2.eq_iff.1 he with ⟨rfl, -⟩ | ⟨rfl, -⟩
          · exact Or.inl rfl
          · exact Or.inr (Or.inl rfl)
      · rintro (rfl | rfl | ⟨u, hu⟩)
        · exact ⟨b, Or.inr ⟨rfl, hne⟩⟩
        · exact ⟨a, Or.inr ⟨Sym2.eq_swap, hne.symm⟩⟩
        · exact ⟨u, Or.inl hu⟩
    rw [this, card_insert_of_notMem, card_insert_of_notMem hbc]
    simp [hne, hac]

/-! ### The swap -/

/-- `y` takes `v` from the edge `v v′`. -/
def swapG (M : SimpleGraph V) (y v v' : V) : SimpleGraph V :=
  M.deleteEdges {s(v, v')} ⊔ fromEdgeSet {s(y, v)}

section Swap

variable {G : SimpleGraph V} {HV : Finset V} {M : SimpleGraph V} {y v v' : V}

theorem swapG_adj (a b : V) : (swapG M y v v').Adj a b ↔
    (M.Adj a b ∧ s(a, b) ≠ s(v, v')) ∨ (s(a, b) = s(y, v) ∧ a ≠ b) := by
  simp [swapG, fromEdgeSet_adj]

variable (hMm : IsMatchingGraph M) (hyu : ∀ u, ¬ M.Adj y u) (hvv : M.Adj v v')
include hMm hyu hvv

theorem swap_ne : y ≠ v ∧ y ≠ v' ∧ v ≠ v' :=
  ⟨fun h => hyu v' (h ▸ hvv), fun h => hyu v (h ▸ hvv.symm), hvv.ne⟩

theorem swap_adj_y (u : V) : (swapG M y v v').Adj y u ↔ u = v := by
  obtain ⟨h1, -, -⟩ := swap_ne hMm hyu hvv
  rw [swapG_adj]
  constructor
  · rintro (⟨h, -⟩ | ⟨he, -⟩)
    · exact absurd h (hyu u)
    · rcases Sym2.eq_iff.1 he with ⟨-, rfl⟩ | ⟨rfl, -⟩
      · rfl
      · exact absurd rfl h1
  · rintro rfl; exact Or.inr ⟨rfl, h1⟩

theorem swap_adj_v (u : V) : (swapG M y v v').Adj v u ↔ u = y := by
  obtain ⟨h1, -, -⟩ := swap_ne hMm hyu hvv
  rw [swapG_adj]
  constructor
  · rintro (⟨h, hne⟩ | ⟨he, -⟩)
    · exact absurd (by rw [hMm v u v' h hvv]) hne
    · rcases Sym2.eq_iff.1 he with ⟨rfl, -⟩ | ⟨-, rfl⟩
      · exact absurd rfl h1
      · rfl
  · rintro rfl; exact Or.inr ⟨Sym2.eq_swap, Ne.symm h1⟩

theorem swap_adj_v' (u : V) : ¬ (swapG M y v v').Adj v' u := by
  obtain ⟨-, h2, h3⟩ := swap_ne hMm hyu hvv
  rw [swapG_adj]
  rintro (⟨h, hne⟩ | ⟨he, -⟩)
  · exact hne (by rw [hMm v' u v h hvv.symm, Sym2.eq_swap])
  · rcases Sym2.eq_iff.1 he with ⟨h, -⟩ | ⟨h, -⟩
    · exact h2 h.symm
    · exact h3 h.symm

theorem swap_adj_other {z : V} (hz1 : z ≠ y) (hz2 : z ≠ v) (hz3 : z ≠ v') (u : V) :
    M.Adj z u ↔ (swapG M y v v').Adj z u := by
  rw [swapG_adj]
  constructor
  · intro h
    refine Or.inl ⟨h, fun he => ?_⟩
    rcases Sym2.eq_iff.1 he with ⟨h', -⟩ | ⟨h', -⟩
    · exact hz2 h'
    · exact hz3 h'
  · rintro (⟨h, -⟩ | ⟨he, -⟩)
    · exact h
    · rcases Sym2.eq_iff.1 he with ⟨h', -⟩ | ⟨h', -⟩
      · exact absurd h' hz1
      · exact absurd h' hz2

theorem swap_valid (hM : Valid G HV M) (hy : y ∈ HV) (hyv : G.Adj y v) :
    Valid G HV (swapG M y v v') := by
  obtain ⟨hMG, -, hMS⟩ := hM
  obtain ⟨h1, h2, h3⟩ := swap_ne hMm hyu hvv
  refine ⟨fun a b h => ?_, fun z a b ha hb => ?_, fun a b h => ?_⟩
  · rcases (swapG_adj a b).1 h with ⟨h, -⟩ | ⟨he, -⟩
    · exact hMG h
    · rcases Sym2.eq_iff.1 he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hyv
      · exact hyv.symm
  · by_cases hzy : z = y
    · subst hzy; rw [swap_adj_y hMm hyu hvv] at ha hb; rw [ha, hb]
    by_cases hzv : z = v
    · subst hzv; rw [swap_adj_v hMm hyu hvv] at ha hb; rw [ha, hb]
    by_cases hzv' : z = v'
    · subst hzv'; exact absurd ha (swap_adj_v' hMm hyu hvv a)
    rw [← swap_adj_other hMm hyu hvv hzy hzv hzv'] at ha hb
    exact hMm z a b ha hb
  · rcases (swapG_adj a b).1 h with ⟨h, -⟩ | ⟨he, -⟩
    · exact hMS a b h
    · rcases Sym2.eq_iff.1 he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨hy, (hMS _ _ hvv).1⟩
      · exact ⟨(hMS _ _ hvv).1, hy⟩

theorem swap_cover : cover (swapG M y v v') = insert y ((cover M).erase v') := by
  obtain ⟨h1, h2, h3⟩ := swap_ne hMm hyu hvv
  ext z
  rw [mem_insert, mem_erase, mem_cover, mem_cover]
  by_cases hzy : z = y
  · subst hzy; simp only [true_or, iff_true]; exact ⟨v, (swap_adj_y hMm hyu hvv v).2 rfl⟩
  by_cases hzv : z = v
  · subst hzv
    simp only [hzy, false_or]
    exact ⟨fun _ => ⟨h3, v', hvv⟩, fun _ => ⟨y, (swap_adj_v hMm hyu hvv y).2 rfl⟩⟩
  by_cases hzv' : z = v'
  · subst hzv'
    simp only [hzy, false_or, ne_eq, not_true_eq_false, false_and, iff_false]
    exact fun ⟨u, hu⟩ => swap_adj_v' hMm hyu hvv u hu
  simp only [hzy, hzv', false_or, ne_eq, not_false_eq_true, true_and]
  simp_rw [← swap_adj_other hMm hyu hvv hzy hzv hzv']

theorem card_swap_cover : #(cover (swapG M y v v')) = #(cover M) := by
  obtain ⟨h1, h2, h3⟩ := swap_ne hMm hyu hvv
  have hyc : y ∉ cover M := fun h => by obtain ⟨u, hu⟩ := mem_cover.1 h; exact hyu u hu
  have hv'c : v' ∈ cover M := mem_cover.2 ⟨v, hvv.symm⟩
  rw [swap_cover hMm hyu hvv, card_insert_of_notMem (fun h => hyc (mem_of_mem_erase h)),
    card_erase_of_mem hv'c]
  have : 0 < #(cover M) := card_pos.2 ⟨v', hv'c⟩
  omega

variable {X Y : Finset V} (hXY : Disjoint X Y) (hyY : y ∈ Y) (hvY : v ∉ Y) (hv'Y : v' ∉ Y)
include hXY hyY hvY hv'Y

theorem tsum_swap (hM : Valid G HV M) (hy : y ∈ HV) :
    tsum (swapG M y v v') HV X Y + 2 ≤ tsum M HV X Y ∧
      tsum (swapG M y v v') HV Y X ≤ tsum M HV Y X + 2 := by
  obtain ⟨h1, h2, h3⟩ := swap_ne hMm hyu hvv
  have hyX : y ∉ X := fun h => Finset.disjoint_left.1 hXY h hyY
  have hv : v ∈ HV := (hM.2.2 _ _ hvv).1
  have hv' : v' ∈ HV := (hM.2.2 _ _ hvv).2
  have hS : ({y, v, v'} : Finset V) ⊆ HV := by
    intro z hz; simp only [mem_insert, mem_singleton] at hz
    rcases hz with rfl | rfl | rfl <;> assumption
  -- differences vanish outside `{y, v, v'}`
  have hdiff : ∀ A B : Finset V, tsum (swapG M y v v') HV A B - tsum M HV A B =
      ∑ z ∈ ({y, v, v'} : Finset V), (tau (swapG M y v v') A B z - tau M A B z) := by
    intro A B
    unfold tsum
    rw [← sum_sub_distrib]
    refine (sum_subset hS fun z _ hz => ?_).symm
    simp only [mem_insert, mem_singleton, not_or] at hz
    rw [tau_congr (swap_adj_other hMm hyu hvv hz.1 hz.2.1 hz.2.2)]
    ring
  have hsum3 : ∀ f : V → ℤ, ∑ z ∈ ({y, v, v'} : Finset V), f z = f y + f v + f v' := by
    intro f
    rw [sum_insert (by simp [h1, h2]), sum_insert (by simp [h3]), sum_singleton]
    ring
  -- the values
  have ay : ∀ u, (swapG M y v v').Adj y u ↔ u = v := swap_adj_y hMm hyu hvv
  have av : ∀ u, (swapG M y v v').Adj v u ↔ u = y := swap_adj_v hMm hyu hvv
  have av' : ∀ u, ¬ (swapG M y v v').Adj v' u := swap_adj_v' hMm hyu hvv
  have mv : ∀ u, M.Adj v u ↔ u = v' := fun u => ⟨fun h => hMm v u v' h hvv, fun h => h ▸ hvv⟩
  have mv' : ∀ u, M.Adj v' u ↔ u = v := fun u =>
    ⟨fun h => hMm v' u v h hvv.symm, fun h => h ▸ hvv.symm⟩
  have bv := tau_bounds M X Y v
  have bv' := tau_bounds M X Y v'
  have cv := tau_bounds M Y X v
  have cv' := tau_bounds M Y X v'
  have e1 : tau (swapG M y v v') X Y y = -1 := by
    unfold tau Mixed; simp [ay, hyY, hvY]
  have e2 : tau M X Y y = 1 := by
    unfold tau hval; simp [hyu, hyY, hyX]
  have e3 : tau (swapG M y v v') X Y v ≤ tau M X Y v := by
    unfold tau Mixed at *; simp only [av, mv] at *
    by_cases hvX : v ∈ X <;> simp_all
  have e4 : tau (swapG M y v v') X Y v' ≤ tau M X Y v' := by
    unfold tau Mixed hval at *; simp only [av', mv'] at *
    by_cases hvX : v' ∈ X <;> simp_all
  have f1 : tau (swapG M y v v') Y X y ≤ tau M Y X y := by
    unfold tau Mixed hval; simp [ay, hyu, hyY, hvY, hyX]
  have f2 : tau (swapG M y v v') Y X v ≤ tau M Y X v := by
    unfold tau Mixed at *; simp only [av, mv] at *
    by_cases hvX : v ∈ X <;> simp_all
  have f3 : tau (swapG M y v v') Y X v' ≤ 1 := (tau_bounds _ Y X v').2
  constructor
  · have := hdiff X Y; rw [hsum3] at this; linarith
  · have := hdiff Y X; rw [hsum3] at this; linarith

end Swap

/-! ### Counting at a local optimum -/

/-- If `T ≥ 2`, an unmatched `y ∈ Y` has a neighbour in `HV` that is unmatched or matched with
both ends outside `Y`. -/
theorem exists_move {G : SimpleGraph V} {HV X Y : Finset V} {M : SimpleGraph V}
    (hM : Valid G HV M) (hYH : Y ⊆ HV)
    (hYb : ∀ y ∈ Y, #(HV.filter fun z => z ≠ y ∧ ¬ G.Adj y z) + #Y ≤ #HV)
    (hT : 2 ≤ tsum M HV X Y) :
    ∃ y ∈ Y, (∀ u, ¬ M.Adj y u) ∧ ∃ v ∈ HV, G.Adj y v ∧
      ((∀ u, ¬ M.Adj v u) ∨ ∃ v', M.Adj v v' ∧ v ∉ Y ∧ v' ∉ Y) := by
  obtain ⟨-, hMm, hMS⟩ := hM
  set UY := Y.filter fun z => ∀ u, ¬ M.Adj z u
  set MY := Y.filter fun z => ∃ u, M.Adj z u ∧ u ∉ Y
  -- `T ≤ #UY − #MY`
  have hTle : tsum M HV X Y ≤ #UY - #MY := by
    have h1 : ∀ z ∈ HV, tau M X Y z ≤ (if z ∈ UY then 1 else 0) - (if z ∈ MY then 1 else 0) := by
      intro z _
      unfold tau Mixed hval
      simp only [UY, MY, mem_filter]
      by_cases hc : ∃ u, M.Adj z u
      · have : ¬ ∀ u, ¬ M.Adj z u := fun h => by obtain ⟨u, hu⟩ := hc; exact h u hu
        split_ifs <;> simp_all
      · push_neg at hc
        split_ifs <;> simp_all
    have h2 := sum_le_sum h1
    rw [sum_sub_distrib, sum_boole, sum_boole] at h2
    have e1 : HV.filter (· ∈ UY) = UY := by
      ext z; simp only [mem_filter, and_iff_right_iff_imp]
      exact fun h => hYH (filter_subset _ _ h)
    have e2 : HV.filter (· ∈ MY) = MY := by
      ext z; simp only [mem_filter, and_iff_right_iff_imp]
      exact fun h => hYH (filter_subset _ _ h)
    rw [e1, e2] at h2
    exact h2
  have hpos : 0 < #UY := by omega
  obtain ⟨y, hy⟩ := card_pos.1 hpos
  have hyY : y ∈ Y := (mem_filter.1 hy).1
  have hyu : ∀ u, ¬ M.Adj y u := (mem_filter.1 hy).2
  by_contra hno
  push_neg at hno
  have hno' : ∀ v ∈ HV, G.Adj y v → (∃ u, M.Adj v u) ∧ ∀ v', M.Adj v v' → v ∉ Y → v' ∈ Y := by
    intro v hv hyv
    obtain ⟨u, hu⟩ := hno y hyY hyu v hv hyv |>.1
    exact ⟨⟨u, hu⟩, (hno y hyY hyu v hv hyv).2⟩
  -- the sets
  set A := HV.filter fun z => z ∉ Y ∧ ∀ u, ¬ M.Adj z u
  set B := HV.filter fun z => z ∉ Y ∧ ∃ u, M.Adj z u ∧ u ∉ Y
  set C := HV.filter fun z => z ∉ Y ∧ ∃ u, M.Adj z u ∧ u ∈ Y
  set Q := HV.filter fun z => z ≠ y ∧ ¬ G.Adj y z
  have hHV : #HV ≤ #Y + #A + #B + #C := by
    have : HV ⊆ Y ∪ A ∪ B ∪ C := by
      intro z hz
      simp only [A, B, C, mem_union, mem_filter]
      by_cases hzY : z ∈ Y
      · exact Or.inl (Or.inl (Or.inl hzY))
      by_cases hc : ∃ u, M.Adj z u
      · obtain ⟨u, hu⟩ := hc
        by_cases huY : u ∈ Y
        · exact Or.inr ⟨hz, hzY, u, hu, huY⟩
        · exact Or.inl (Or.inr ⟨hz, hzY, u, hu, huY⟩)
      · push_neg at hc
        exact Or.inl (Or.inl (Or.inr ⟨hz, hzY, hc⟩))
    refine (card_le_card this).trans ?_
    refine (card_union_le _ _).trans ?_
    have := card_union_le (Y ∪ A ∪ B) C
    have := card_union_le (Y ∪ A) B
    have := card_union_le Y A
    omega
  have hQ : #(UY.erase y) + #A + #B ≤ #Q := by
    have hsub : UY.erase y ∪ A ∪ B ⊆ Q := by
      intro z hz
      simp only [Q, mem_union, mem_erase, mem_filter, UY, A, B] at hz ⊢
      rcases hz with ((⟨hzy, hzY, hzu⟩ | ⟨hz, hzY, hzu⟩) | ⟨hz, hzY, u, hu, huY⟩)
      · refine ⟨hYH hzY, hzy, fun hyz => ?_⟩
        obtain ⟨⟨u, hu⟩, -⟩ := hno' z (hYH hzY) hyz
        exact hzu u hu
      · refine ⟨hz, fun h => hzY (h ▸ hyY), fun hyz => ?_⟩
        obtain ⟨⟨u, hu⟩, -⟩ := hno' z hz hyz
        exact hzu u hu
      · refine ⟨hz, fun h => hyu u (h ▸ hu), fun hyz => ?_⟩
        exact huY ((hno' z hz hyz).2 u hu hzY)
    have hd1 : Disjoint (UY.erase y) A := by
      rw [Finset.disjoint_left]; intro z h1 h2
      exact (mem_filter.1 h2).2.1 (mem_filter.1 (mem_of_mem_erase h1)).1
    have hd2 : Disjoint (UY.erase y ∪ A) B := by
      rw [Finset.disjoint_left]; intro z h1 h2
      obtain ⟨-, -, u, hu, -⟩ := mem_filter.1 h2
      rcases mem_union.1 h1 with h | h
      · exact (mem_filter.1 (mem_of_mem_erase h)).2 u hu
      · exact (mem_filter.1 h).2.2 u hu
    have := card_le_card hsub
    rw [card_union_of_disjoint hd2, card_union_of_disjoint hd1] at this
    exact this
  have hCMY : #C ≤ #MY := by
    refine card_le_card_of_injOn (partner M) (fun z hz => ?_) (fun a ha b hb e => ?_)
    · obtain ⟨-, hzY, u, hu, huY⟩ := mem_filter.1 hz
      rw [partner_eq hMm hu]
      exact mem_filter.2 ⟨huY, z, hu.symm, hzY⟩
    · obtain ⟨-, -, u, hu, -⟩ := mem_filter.1 ha
      obtain ⟨-, -, u', hu', -⟩ := mem_filter.1 hb
      rw [partner_eq hMm hu, partner_eq hMm hu'] at e
      subst e
      exact hMm u a b hu.symm hu'.symm
  have hyQ : #Q + #Y ≤ #HV := hYb y hyY
  have hUY : #(UY.erase y) + 1 = #UY := card_erase_add_one hy
  omega

/-- **One swap.** At a maximal matching with `T ≥ 2`, a swap lowers `T` by `2` and raises `T′`
by at most `2`, keeping the number of covered vertices. -/
theorem exists_swap {G : SimpleGraph V} {HV A B : Finset V} {M : SimpleGraph V}
    (hM : Valid G HV M) (hmax : ∀ a b, a ∈ HV → b ∈ HV → G.Adj a b → a ∈ cover M ∨ b ∈ cover M)
    (hAB : Disjoint A B) (hBH : B ⊆ HV)
    (hBb : ∀ y ∈ B, #(HV.filter fun z => z ≠ y ∧ ¬ G.Adj y z) + #B ≤ #HV)
    (hT : 2 ≤ tsum M HV A B) :
    ∃ M', Valid G HV M' ∧ #(cover M') = #(cover M) ∧ tsum M' HV A B + 2 ≤ tsum M HV A B ∧
      tsum M' HV B A ≤ tsum M HV B A + 2 := by
  obtain ⟨y, hyB, hyu, v, hv, hyv, hmove⟩ := exists_move hM hBH hBb hT
  rcases hmove with hvu | ⟨v', hvv, hvB, hv'B⟩
  · exfalso
    rcases hmax y v (hBH hyB) hv hyv with h | h
    · obtain ⟨u, hu⟩ := mem_cover.1 h; exact hyu u hu
    · obtain ⟨u, hu⟩ := mem_cover.1 h; exact hvu u hu
  exact ⟨swapG M y v v', swap_valid hM.2.1 hyu hvv hM (hBH hyB) hyv,
    card_swap_cover hM.2.1 hyu hvv, tsum_swap hM.2.1 hyu hvv hAB hyB hvB hv'B hM (hBH hyB)⟩

/-! ### The good matching -/

/-- **The choice of `M₀`.** A maximal matching inside `HV` with `T ≤ 1` and `T′ ≤ 1`. -/
theorem exists_good_matching (G : SimpleGraph V) {HV X Y : Finset V}
    (hXH : X ⊆ HV) (hYH : Y ⊆ HV) (hXY : Disjoint X Y)
    (hYb : ∀ y ∈ Y, #(HV.filter fun z => z ≠ y ∧ ¬ G.Adj y z) + #Y ≤ #HV)
    (hXb : ∀ x ∈ X, #(HV.filter fun z => z ≠ x ∧ ¬ G.Adj x z) + #X ≤ #HV) :
    ∃ M : SimpleGraph V, Valid G HV M ∧
      (∀ a b, a ∈ HV → b ∈ HV → G.Adj a b → a ∈ cover M ∨ b ∈ cover M) ∧
      tsum M HV X Y ≤ 1 ∧ tsum M HV Y X ≤ 1 := by
  set S := (univ : Finset (SimpleGraph V)).filter fun M => Valid G HV M
  have hne : S.Nonempty := ⟨⊥, mem_filter.2 ⟨mem_univ _, bot_le,
    fun v a b h => absurd h (by simp), fun a b h => absurd h (by simp)⟩⟩
  let Φ : SimpleGraph V → ℤ := fun M =>
    -(2 * #HV + 2) * #(cover M) + max (tsum M HV X Y) (tsum M HV Y X)
  obtain ⟨M, hMS, hmin⟩ := S.exists_min_image Φ hne
  have hM : Valid G HV M := (mem_filter.1 hMS).2
  have hmin' : ∀ M', Valid G HV M' → Φ M ≤ Φ M' := fun M' h =>
    hmin M' (mem_filter.2 ⟨mem_univ _, h⟩)
  have b1 := tsum_bounds M HV X Y
  have b2 := tsum_bounds M HV Y X
  have hsum := tsum_add_le hXY M HV
  -- maximality
  have hmax : ∀ a b, a ∈ HV → b ∈ HV → G.Adj a b → a ∈ cover M ∨ b ∈ cover M := by
    intro a b ha hb hab
    by_contra hc
    push_neg at hc
    obtain ⟨hv, hcard⟩ := add_edge hM ha hb hab hc.1 hc.2
    have h := hmin' _ hv
    have b3 := tsum_bounds (M ⊔ fromEdgeSet {s(a, b)}) HV X Y
    have b4 := tsum_bounds (M ⊔ fromEdgeSet {s(a, b)}) HV Y X
    simp only [Φ, hcard] at h
    push_cast at h
    have m1 := max_le b3.2 b4.2
    have m2 := le_trans b1.1 (le_max_left (tsum M HV X Y) (tsum M HV Y X))
    have m0 : (0 : ℤ) ≤ #HV := by positivity
    nlinarith
  refine ⟨M, hM, hmax, ?_, ?_⟩
  · by_contra hT
    push_neg at hT
    obtain ⟨M', hv, hc, t1, t2⟩ := exists_swap hM hmax hXY hYH hYb (by omega)
    have h := hmin' _ hv
    simp only [Φ, hc] at h
    have : max (tsum M' HV X Y) (tsum M' HV Y X) < max (tsum M HV X Y) (tsum M HV Y X) := by
      rw [max_lt_iff]
      exact ⟨lt_of_lt_of_le (by linarith) (le_max_left _ _),
        lt_of_lt_of_le (by linarith) (le_max_left _ _)⟩
    linarith
  · by_contra hT
    push_neg at hT
    obtain ⟨M', hv, hc, t1, t2⟩ := exists_swap hM hmax hXY.symm hXH hXb (by omega)
    have h := hmin' _ hv
    simp only [Φ, hc] at h
    have : max (tsum M' HV X Y) (tsum M' HV Y X) < max (tsum M HV X Y) (tsum M HV Y X) := by
      rw [max_lt_iff]
      exact ⟨lt_of_lt_of_le (by linarith) (le_max_right _ _),
        lt_of_lt_of_le (by linarith) (le_max_right _ _)⟩
    linarith

end CH89
