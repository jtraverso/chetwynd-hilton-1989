# Chetwynd–Hilton 1989: 1-factorizing regular graphs of degree ≥ ½(√7 − 1)|V|

A Lean 4 / Mathlib formalization of

> **A. G. Chetwynd and A. J. W. Hilton**, *1-factorizing regular graphs of high degree — an
> improved bound*, Discrete Mathematics 75 (1989) 103–112, **Theorem 2**: a regular simple graph
> `G` of even order with `d(G) ≥ ½(√7 − 1)|V(G)|` (≈ 0.823 |V(G)|) is 1-factorizable.

## Statements (`CH89Challenge.lean`)

* `CH89.lineGraph_colorable_of_isRegular_sqrt7`: `G` `d`-regular, `|V|` even,
  `(√7 − 1)/2 · |V| ≤ d` ⇒ `G.lineGraph.Colorable d`.
* `CH89.lineGraph_colorable_of_isRegular_nat`: `|V| = 2n`, `7 n² ≤ (d + n)²` ⇒ the same.

The library also proves `CH89.regularOneFactorable : Plantholt.RegularOneFactorable ((√7 − 1)/2)`
and Plantholt's overfull criterion with `c* = (√7 − 1)/2` (`CH89.overfull_criterion`).

## A gap in the article and its repair

The proof of Theorem 1 (§4) says "we may moreover suppose that `x_j` comes before `w_j` in the
list `(r_m, …, r_t, l_1, …, l_m)`". For an arbitrary maximal matching `M₀` this is false: it is a
ballot condition on the types of the edges of `M₀`. We prove it (up to the one exceptional pair the
article already pays for) for a suitable `M₀`: among the matchings of `H` minimize
`−K·#covered + max(T, T′)` with `T = u_Y − u_X − μ`, `T′ = u_X − u_Y − μ` (`CH89/Swap.lean`), then
order the edges (mixed ones outside, `XX`/`YY` alternately) and pair `X` with `Y` by Hall's theorem
(`CH89/Prefix.lean`, `CH89/Labelling.lean`). Details and all parameter inequalities: `NOTES.md`.

The factor lemma of the dependency (perfect matching instead of the article's Hamiltonian cycle) is
one unit weaker; the unit is recovered as in the article (`s = |W| − p − 1`): one vertex of `W ∩ N(v*)`
keeps its edge to `v*`, re-inserted by the pivot lemma (`colorable_of_add_vertex_one`).

## Layout

* `CH89/Count.lean` — Lemma 3 (a pair with many common non-neighbours).
* `CH89/Arith.lean` — the parameter inequalities (`(d + n)² ≥ 7n²` ⇒ budget).
* `CH89/Swap.lean` — the choice of `M₀`.
* `CH89/Ilv.lean`, `CH89/Order.lean`, `CH89/Label.lean`, `CH89/Prefix.lean`, `CH89/Ballot.lean`,
  `CH89/Labelling.lean` — the list `r_m … r_t l_1 … l_m`, the staircase labelling, the ballot
  condition and the pairing.
* `CH89/Engine.lean` — Theorem 1 (peeling near 1-factors, core of Theorem 5, re-insertions).
* `CH89/Main.lean` — Theorem 2. `CH89/Criterion.lean` — consequences.

## Dependencies

Requires `jtraverso/plantholt-overfull-criterion` @ `f8900944` (PALOMAR-2026-11-04-000016 v2:
staircase classes, Theorem 5 core, near 1-factors, re-insertion of `w`), which pulls in
`jtraverso/overfull-critical-graphs` @ `b85da9a` (PALOMAR-2026-11-04-000009, VAL / pivot lemma)
and `jtraverso/vizing` @ `33b2de8` (PALOMAR-2026-10-15-000004). Lean `v4.35.0-rc3`, Mathlib
`v4.35.0-rc3`.

## License

Apache 2.0.
