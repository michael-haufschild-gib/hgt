# Kleinbock–Margulis: Flows on homogeneous spaces and Diophantine approximation on manifolds

- **ID:** km98
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean)
- **Source:** arXiv math/9810036 = Ann. of Math. 148 (1998), 339–360
- **Statement:** Formalize, unconditionally and hypothesis-free, every lemma / proposition /
  theorem of Kleinbock–Margulis 1998 in the Lean corpus.

## Goal
Full Lean 4 certification of the KM quantitative-nondivergence machine:
`(C,α)`-good functions, the marked-point covering theorem, quantitative nondivergence on the
space of lattices, and strong extremality of nondegenerate manifolds (Sprindžuk's conjectures
H1, H2 / Baker's conjecture).

## Inventory of targets (paper order)

| Label | Statement | Lean module | Status |
|---|---|---|---|
| Lemma 2.1 | `(1.1M)` ⟹ `δ(g_t Λ_y) ≤ r` | `KleinbockMargulis/Reduction.lean` `lemma_2_1` | **DONE** |
| Cor 2.2 | VWMA ⟹ ∞ many `t ∈ ℤ₊ⁿ` with `δ(g_tΛ_y) ≤ e^{-γt}` | `Reduction.lean` `corollary_2_2` | **DONE** |
| Prop 2.3 | measure bound `|{x∈B : δ(g_tΛ_{f(x)})<ε}| ≤ D(ε/ρ)^{1/dl}|B|` | | TODO |
| Theorem A | a.e. nondegenerate ⟹ strongly extremal | | TODO |
| Lemma 3.1 | (a) `|f|`, (b) `λf`, (c) `sup_i|f_i|` stay `(C,α)`-good | `Good.lean` `isGood_abs_iff`, `IsGood.const_mul`, `IsGood.sup` | **DONE** |
| Prop 3.2 | `deg f ≤ k` ⟹ `(2k(k+1)^{1/k},1/k)`-good on ℝ | `PolynomialGood.lean` `isGood_polynomial` | **DONE** |
| Lemma 3.3 (+3.3.1, 3.3.2) | `C^k` derivative-sandwich ⟹ cube estimate `(3.5)` | `KleinbockMargulis/SmoothGood.lean` | TODO |
| Prop 3.4 | nondegenerate point ⟹ all linear combos of `1,f_1,…,f_n` are `(C,1/dl)`-good near it | `KleinbockMargulis/Nondegenerate.lean` | TODO |
| Theorem 4.1 | measure of unmarked points `≤ kC(3^d N_d)^k (ε/ρ)^α |B|` | `Marked.lean` `measure_not_marked_le` | **DONE** |
| Lemmas 4.2–4.6 | supporting | `Marked.lean` | **DONE** |
| Lemma 5.1 | `‖Λ‖ ≤ k‖Γ‖·‖v‖` | `LatticeNorm.lean` `lemma_5_1` (sharper constant `rank Γ + 1`) | **DONE** |
| Theorem 5.2 | quantitative nondivergence | `Nondivergence.lean` `theorem_5_2` | **DONE** |
| Theorem 5.3 | unipotent one-parameter version | | TODO |
| Theorem 5.4 | `h = g_t u_{f(x)}` version | | TODO |
| Theorem B (§6.3) | Khintchine-type convergence statement | | TODO |

## Missing infrastructure (mathlib gaps) to build
1. `(C,α)`-good functions — new.
2. Higher-order symmetry of `iteratedFDeriv` (mathlib has only `second_derivative_symmetric`),
   and polarization: symmetric multilinear map with vanishing diagonal is zero.
3. Sup-norm ("Plücker") norm on `⋀^j ℝ^k` for subgroups of `ℤ^k`, basis independence,
   and `‖w ∧ v‖ ≤ k‖w‖‖v‖`.
4. Poset of nonzero primitive subgroups of `ℤ^k`; length = rank.

Available in mathlib and to be reused: `Besicovitch.exist_disjoint_covering_families`,
`Besicovitch.multiplicity`, `Besicovitch.isEmpty_satelliteConfig_multiplicity`,
`Real.volume_pi_ball`, `Measure.addHaar_image_linearMap`.

## Approach
Work in `Fin d → ℝ` with the sup norm, where metric balls **are** cubes and Lebesgue measure is
`volume = Measure.pi`.  This removes the paper's cube/ball circumscription step.  Prop 3.4's
"rotation of the coordinate system" is replaced by a general invertible linear change of
variables (goodness is stable under `GL_d` with constant `C‖T‖^d/|det T|`), and the required
basis is produced by a one-parameter polynomial non-vanishing argument (`u_i = v + t e_i`)
rather than by a Haar-measure genericity argument on `O(d)`.

## Errata found in the published proof
* Theorem 5.2, last display: the chain `‖h(x)v‖ ≥ ‖h(x)Λ‖/(k‖h(x)Γ_{i-1}‖) ≥ ε/(kρ) ≥ ε` uses
  `‖h(x)Γ_{i-1}‖ ≤ ρ`, which fails for `i = 1`, where `Γ_0 = {0}` and `‖h(x)Γ_0‖ = 1 > ρ`.
  The case `i = 1` has to be treated separately: there `Λ = ℚv ∩ ℤ^k`, `v` is an integer multiple
  of a generator `w` of `Λ`, and `‖h(x)v‖ ≥ ‖h(x)w‖ = ‖h(x)Λ‖ ≥ ε` directly (equivalently, the
  constant in Lemma 5.1 is `rank Γ + 1`, which is `1` when `Γ = {0}`).

## Log
- 2026-08-21 — created; paper source read in full (arXiv e-print `mb.tex`).
- 2026-08-21 — §2 (Lemma 2.1, Cor 2.2), §3 (Lemma 3.1, Prop 3.2) and §4 (Theorem 4.1 with
  Lemmas 4.2-4.6) Lean-complete and wired into `GaloisForLFunctions.HTGeometry`.
- 2026-08-21 — §5 core complete: `WedgeNorm.lean` (Plücker calculus, `‖w∧v‖ ≤ (j+1)‖w‖‖v‖`),
  `PluckerSpan.lean` (Cramer's rule; the span is determined by the Plücker vector),
  `IntegerLattice.lean` (`rank(W ∩ ℤ^k) = dim_ℚ W`), `LatticeNorm.lean` (Lemma 5.1),
  `LatticeFinite.lean` (condition (A3)), `Nondivergence.lean` (Theorem 5.2).
  Remaining: Theorems 5.3, 5.4, Prop 2.3, Theorem A, Lemma 3.3, Prop 3.4, Theorem B.
