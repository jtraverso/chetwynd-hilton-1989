/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CH89.Main
public import Plantholt.Main

/-!
# Consequences: `RegularOneFactorable ((√7 − 1)/2)` and Plantholt's criterion

* `regularOneFactorable`: Theorem 2 in the form `Plantholt.RegularOneFactorable ((√7 − 1)/2)`.
* `overfull_criterion`: Plantholt's theorem (PALOMAR-2026-11-04-000016) with
  `c* = (√7 − 1)/2`: if `G` has even order `n` and `(√7 − 1) n ≤ 3δ − Δ`, then `G` is Class 1 if
  and only if it has no `Δ`-overfull subgraph.
-/

@[expose] public section

namespace CH89

open SimpleGraph

universe u

theorem three_quarters_le : (3 / 4 : ℝ) ≤ (Real.sqrt 7 - 1) / 2 := by
  have h : (5 / 2 : ℝ) ≤ Real.sqrt 7 := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  linarith

/-- **Theorem 2 as `RegularOneFactorable`.** -/
theorem regularOneFactorable : Plantholt.RegularOneFactorable.{u} ((Real.sqrt 7 - 1) / 2) := by
  intro W _ _ H _ d hev hreg hcd
  classical
  obtain ⟨n, hn⟩ := hev
  exact colorable_of_real (G := H) (n := n) (d := d) (by omega) (fun v => by convert hreg v) hcd

/-- **Plantholt's criterion with `c* = (√7 − 1)/2`.** -/
theorem overfull_criterion {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hev : Even (Fintype.card V))
    (hdeg : (Real.sqrt 7 - 1) * Fintype.card V ≤ 3 * (G.minDegree : ℝ) - G.maxDegree) :
    G.lineGraph.Colorable G.maxDegree ↔ ¬ Plantholt.HasOverfullSubgraph G :=
  Plantholt.theorem_1_2 three_quarters_le regularOneFactorable G hev (by linarith)

end CH89
