/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib

/-!
# Chetwynd–Hilton 1989: regular graphs of degree at least ½(√7 − 1)|V| are 1-factorizable

**A. G. Chetwynd and A. J. W. Hilton, *1-factorizing regular graphs of high degree — an improved
bound*, Discrete Math. 75 (1989) 103–112, Theorem 2.** A `d`-regular simple graph `G` of even
order with `d ≥ ½(√7 − 1)|V(G)|` (`≈ 0.823 |V(G)|`) is 1-factorizable, i.e. `χ′(G) = d`; an edge
colouring with `d` colours is a colouring of the line graph.

* `CH89.lineGraph_colorable_of_isRegular_sqrt7`: the theorem as stated in the article.
* `CH89.lineGraph_colorable_of_isRegular_nat`: the same with the threshold in integers: order
  `2n` and `7 n² ≤ (d + n)²` (equivalent to `d ≥ (√7 − 1) n`).
-/

@[expose] public section

namespace CH89

open SimpleGraph

/-- **Chetwynd–Hilton 1989, Theorem 2.** A `d`-regular graph of even order with
`d ≥ ½(√7 − 1)|V|` is `d`-edge-colourable. -/
theorem lineGraph_colorable_of_isRegular_sqrt7 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {d : ℕ} (hev : Even (Fintype.card V))
    (hreg : G.IsRegularOfDegree d) (hd : (Real.sqrt 7 - 1) / 2 * Fintype.card V ≤ d) :
    G.lineGraph.Colorable d := by
  sorry

/-- **Chetwynd–Hilton 1989, Theorem 2**, integer form: order `2n` and `7 n² ≤ (d + n)²`. -/
theorem lineGraph_colorable_of_isRegular_nat {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {d n : ℕ} (hcard : Fintype.card V = 2 * n)
    (hreg : G.IsRegularOfDegree d) (hd : 7 * n ^ 2 ≤ (d + n) ^ 2) :
    G.lineGraph.Colorable d := by
  sorry

end CH89
