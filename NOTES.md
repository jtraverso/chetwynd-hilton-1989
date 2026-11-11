# Chetwynd–Hilton 1989, Theorem 2 — repaired argument

Paper: A. G. Chetwynd, A. J. W. Hilton, *1-factorizing regular graphs of high degree — an improved
bound*, Discrete Math. 75 (1989) 103–112. Copy: `C:\lean\ch1989_paper\ch89.pdf` / `ch89.txt`.

**Target.** `G` `d`-regular on `2n` vertices, `d ≥ (√7 − 1) n` (i.e. `(d + n)² ≥ 7 n²`) ⇒ `χ′(G) = d`.

Notation: `r = 2n − 1 − d` (non-degree), `w, v*` two vertices, `W = V − N[w]` (`|W| = r`),
`p` = number of common non-neighbours of `w, v*`.
`X = N(w) − N[v*]`, `Y = W ∩ N(v*)`, `P = W − N[v*] − v*` (`|P| = p`); `|X| = |Y| = r − p − [v* ∈ W]`.

## 1. The gap (NOTES_CH.md in overfull_critical) and its repair

The step "we may moreover suppose that `x_j` comes before `w_j` in the list `(r_m, …, r_t, l_1, …, l_m)`"
is a ballot condition on the pair types of `M₀` and does not hold for an arbitrary maximal matching.
It does hold (up to one exceptional pair, which the paper already pays for with the step `q + 1`) for a
suitably chosen `M₀`:

**Pair types.** `M₀` matching of `H = G[(X ∪ W) − v*]`, `H = X ⊔ Y ⊔ P'` (`P'` = rest). Orient each
edge `(r, l)` (`r ∈ R`, `l ∈ L`): the `X` end goes to `R`, the `Y` end to `L` (so XY: `x ∈ R, y ∈ L`;
XP: `x ∈ R`; YP: `y ∈ L`). Counts: `a` XX, `b` YY, `c` XY, `e` YP, `f` XP pairs, `u_X, u_Y, u_P`
unmatched. `μ = 2c + e + f` (= number of `X ∪ Y` vertices matched outside their own class).
`T = u_Y − u_X − μ = 2(a − b − c − e)`, `T′ = u_X − u_Y − μ = 2(b − a − c − f)`, `T + T′ = −2μ ≤ 0`.

**Lemma A (choice of `M₀`).** Assume every `y ∈ Y` has at most `|X| + |P'|` non-neighbours in
`H − y`, and every `x ∈ X` at most `|Y| + |P'|`. Among the matchings of `H`, take one minimizing
`Φ = K·(#uncovered) + max(T, T′)` (`K = 3|H| + 1`). Then `M₀` is maximal and `T, T′ ≤ 1`.

*Proof.* Two uncovered adjacent vertices: add the edge (`Φ` drops by `≥ 2K − 2|H| > 0`).
If `T ≥ 2` then `u_Y ≥ 2`; if an uncovered `y ∈ Y` is adjacent to a vertex `v` of an XX, XP or PP pair
`{v, v′}`, replace `vv′` by `yv`. Effect (checked case by case): XX `ΔT = −4, ΔT′ = 0`; XP via `x`:
`−2, 0`; XP via `p`: `−2, +2`; PP: `−2, 0`. Since `T′ ≤ −T`, `max(T − 2, T′ + 2) < T`: `Φ` drops.
At the minimum no such `v` exists, so an uncovered `y` is non-adjacent to all other uncovered vertices
and to all vertices of XX/XP/PP pairs: `(u − 1) + N_XP ≤ |X| + |P'|` with
`N_XP = |X| + |P'| − u_X − u_P − |A₃|`, `A₃` = `X ∪ P'` vertices matched into `Y`, `|A₃| = μ_Y` (the
`Y` vertices matched outside `Y`). Hence `u_Y − 1 ≤ μ_Y` and `T = u_Y − u_X − μ_X − μ_Y ≤ 1`,
a contradiction. `T′` symmetric (swap `X ↔ Y`). ∎

The hypotheses hold: a vertex has `r` non-neighbours; `y ∈ Y` is non-adjacent to `w ∉ H`, and
`x ∈ X` to `v* ∉ H`, so each has `≤ r − 1` non-neighbours in `H`, and `|X| + |P'| ≥ r − 1`,
`|Y| + |P'| ≥ r − 1` in all cases below.

**Lemma B (ordering).** Put the pairs in the order (outer → inner): all pairs with
`h(r) ≥ 0 ≥ h(l)` (XY, XP, YP, PP), then XX and YY pairs alternately (XX first), then the surplus;
unmatched in the middle with `X` first, `P` next, `Y` last. Here `h = +1` on `X`, `−1` on `Y`, `0`
on `P'`. In the list `ℓ = (r_m, …, r_1, r_0, …, r_t, l_1, …, l_m)` every prefix has
`#Y ≤ #X + 1`.

*Proof.* With `F = Σ_pairs h(r)`, `S = Σ_pairs h(l)`: `F + h(U) + S = |X| − |Y| = 0` and pairwise
`h(r) − h(l)` = number of mixed ends, so `F − S = μ`; hence `S = T/2 ≤ 1/2`, `F = −T′/2 ≥ −1/2`.
Prefixes of the `R` part have `h ≥ min(0, F) ≥ −1` (first block `≥ 0`, alternation `≥ 0`, surplus
monotone); the middle has `h ≥ min(F, F + h(U)) = min(F, −S) ≥ −1`; a prefix ending in the `L` part
has `h = −(Σ h(l) over an outer block of pairs) ≥ −max(1, S) ≥ −1`. ∎

By Hall's theorem (one dummy `x`), there is a bijection `σ : Y → X` with `σ(y)` before `y` for all
`y` but at most one. "Before" means exactly that `σ(y)` is uncovered by the staircase class of
`v* y` (`R` before `L`; `r_k` before `r_{k'}` iff `k > k'`; `l_j` before `l_a` iff `j < a`; checked
on the staircase formulas `l_a l_b ↦ a + b − t`, `l_j r_k ↦ j − k`). The one exceptional pair gets
its own extra near 1-factor (step `q + 1`), exactly as in the paper.

## 2. Saving one vertex (the paper's `s = |W| − p − 1`)

In the formal factor lemma (`exists_factors_var`, `D₀ = d − 2`, perfect matching of `G* − m`) the
budget is one unit worse than the paper's Hamiltonian-cycle count. We recover a unit as the paper
does: if `X ≠ ∅`, drop one `x₀ ∈ X` (it leaves `H`) and one `y₀ ∈ Y` (it stays in `H`, now in `P'`);
the edge `v* y₀` is kept out of the staircase classes, so at re-insertion `v*` may have one neighbour
of maximum degree (`y₀`): handled by the pivot lemma (Lemma 1 with `d*(v*) ≤ 1`).

## 3. Budget

Step `k` (0-based) of `exists_factors_var` needs `2n + |V(C_k)| + 2k ≤ 2(d − 2)`; staircase classes
cover `≤ 2(q + 1 − k)` vertices, the extra step covers 2. With `q = |H|` and at most one extra step:
`n + q + 3 ≤ d`.
`q = 2|X′| + |P'|`: case `v* ∉ W`: `q = 2r − p − 1` (if `X ≠ ∅`) or `q = r` (`p = r`);
case `v* ∈ W`: `q = 2r − p − 3` or `q = r − 1`.

* Worst case `q = 2r − p − 1`: need `3d + p ≥ 5n`. Lemma 3 of the paper (averaging over ordered
  pairs: `(2n − 1) p ≥ r (r − 1)` for some pair) and the identity
  `r(r − 1) − (2n − 1)(5n − 3d − 1) = (d + n)² − 7n² + n + 1 > 0` give `(2n−1)p > (2n−1)(5n−3d−1)`,
  so `p ≥ 5n − 3d`. (Without the saved unit one would need `3d + p ≥ 5n + 1`, which fails, e.g.
  `n = 6, d = 10`; checked numerically: fails for ~19% of `n ≤ 2·10⁵`.)
* `q = r` (`X = ∅`, `v* ∉ W`): need `2d ≥ 3n + 2`; from `(d + n)² ≥ 7n²` this holds for `n ≥ 4`;
  `n ≤ 3` with `d ≥ (√7−1)n` forces `d = 2n − 1`, the complete graph, handled directly
  (`G − w` has maximum degree `d − 1`, Vizing, then re-insert `w`).
* Case `v* ∈ W` is 2 better.
* `r = 0` (complete graph): directly as above.

Numerical check (scratch `budget2.py`): for all `n ≤ 10⁵`, all `d ≥ (√7−1)n`, both cases, with
`p = ⌈r(r−1)/(2n−1)⌉`: `n + q + 3 ≤ d` holds except `K₆` (`n = 3, d = 5, r = 0`).
Ballot check (scratch `ballot.py`): the ordering of Lemma B has deficit `≤ 1` for all type counts
`≤ 4` satisfying `|T|, |T′| ≤ μ + 1`... (brute force, no failure).

**Conclusion.** The exact Theorem 2 (`d ≥ ½(√7 − 1)|V|`) follows; no weaker constant is needed.
