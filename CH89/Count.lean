/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import OneFactor.Labels
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic.Ring

/-!
# Chetwynd–Hilton 1989, Lemma 3: a pair with many common non-neighbours

`exists_pair_many_common`: in a `d`-regular graph on `N` vertices (`r = N − 1 − d`) there are two
distinct vertices `w, v*` whose set `P = W − N[v*]` of common non-neighbours satisfies
`r (r − 1) ≤ (N − 1) |P|` (average over the ordered pairs: each vertex is the centre of
`r (r − 1)` ordered paths of length two in the complement).
-/

@[expose] public section

namespace CH89

open SimpleGraph Finset OneFactor

open scoped Classical

attribute [-instance] SimpleGraph.Sdiff.adjDecidable SimpleGraph.Sup.adjDecidable

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)

theorem sum_setP_offDiag :
    ∑ p ∈ (univ : Finset V).offDiag, #(setP G p.1 p.2) =
      ∑ z : V, (#(nonNbr G z) * #(nonNbr G z) - #(nonNbr G z)) := by
  have h1 : ∀ p : V × V, #(setP G p.1 p.2) =
      ∑ z : V, if (p.1 ∈ nonNbr G z ∧ p.2 ∈ nonNbr G z) then 1 else 0 := by
    intro p
    rw [sum_boole, Nat.cast_id]
    congr 1
    ext z
    simp only [mem_setP, nonNbr, mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨⟨h1, h3⟩, h2, h4⟩
      exact ⟨⟨Ne.symm h1, fun h => h3 h.symm⟩, ⟨Ne.symm h2, fun h => h4 h.symm⟩⟩
    · rintro ⟨⟨h1, h3⟩, ⟨h2, h4⟩⟩
      exact ⟨⟨Ne.symm h1, fun h => h3 h.symm⟩, Ne.symm h2, fun h => h4 h.symm⟩
  simp_rw [h1]
  rw [sum_comm]
  refine sum_congr rfl fun z _ => ?_
  rw [← offDiag_card, sum_boole, Nat.cast_id]
  congr 1
  ext p
  simp only [mem_filter, mem_offDiag, mem_univ, true_and]
  tauto

/-- **Lemma 3.** Some pair of distinct vertices has at least the average number of common
non-neighbours: `r (r − 1) ≤ (|V| − 1) · |P|`. -/
theorem exists_pair_many_common {d : ℕ} (hreg : ∀ v, G.degree v = d) (h2 : 2 ≤ Fintype.card V) :
    ∃ w v : V, w ≠ v ∧
      (Fintype.card V - 1 - d) * (Fintype.card V - 1 - d - 1) ≤
        (Fintype.card V - 1) * #(setP G w v) := by
  obtain ⟨N, hN⟩ : ∃ N, N = Fintype.card V := ⟨_, rfl⟩
  obtain ⟨r, hrd⟩ : ∃ r, r = Fintype.card V - 1 - d := ⟨_, rfl⟩
  rw [← hN] at h2 ⊢
  rw [show N - 1 - d = r by omega]
  have hr : ∀ z, #(nonNbr G z) = r := fun z => by
    have := card_nonNbr G hreg z; omega
  by_contra hcon
  push_neg at hcon
  have hlt : ∑ p ∈ (univ : Finset V).offDiag, (N - 1) * #(setP G p.1 p.2) <
      ∑ p ∈ (univ : Finset V).offDiag, r * (r - 1) := by
    apply sum_lt_sum_of_nonempty
    · obtain ⟨a, b, hab⟩ := Fintype.exists_pair_of_one_lt_card (α := V) (by omega)
      exact ⟨(a, b), by simp [hab]⟩
    · intro p hp
      exact hcon p.1 p.2 (mem_offDiag.1 hp).2.2
  rw [← mul_sum, sum_setP_offDiag, sum_const, offDiag_card, card_univ] at hlt
  simp_rw [hr] at hlt
  rw [sum_const, card_univ, smul_eq_mul, smul_eq_mul, ← hN] at hlt
  have e1 : r * r - r = r * (r - 1) := by
    rw [Nat.mul_sub, mul_one]
  have e2 : N * N - N = N * (N - 1) := by rw [Nat.mul_sub, mul_one]
  rw [e1, e2] at hlt
  have : (N - 1) * (N * (r * (r - 1))) = N * (N - 1) * (r * (r - 1)) := by ring
  omega

end CH89
