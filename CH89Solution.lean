/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib
public import CH89.Main

/-!
# Chetwynd–Hilton 1989, Theorem 2 (solution)

The statements of `CH89Challenge`, proved from `CH89.colorable_of_sqrt7` (the repaired proof of
Theorems 1 and 2 of the article, see `NOTES.md`).
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
  classical
  obtain ⟨n, hn⟩ := hev
  exact colorable_of_real (G := G) (n := n) (d := d) (by omega) (fun v => by convert hreg v) hd

/-- **Chetwynd–Hilton 1989, Theorem 2**, integer form: order `2n` and `7 n² ≤ (d + n)²`. -/
theorem lineGraph_colorable_of_isRegular_nat {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {d n : ℕ} (hcard : Fintype.card V = 2 * n)
    (hreg : G.IsRegularOfDegree d) (hd : 7 * n ^ 2 ≤ (d + n) ^ 2) :
    G.lineGraph.Colorable d := by
  classical
  exact colorable_of_sqrt7 (G := G) hcard (fun v => by convert hreg v) hd

end CH89
