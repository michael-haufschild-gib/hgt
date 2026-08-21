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
| Lemma 2.1 | `(1.1M)` ⟹ `δ(g_t Λ_y) ≤ r` | `KleinbockMargulis/Lattice…` | TODO |
| Cor 2.2 | VWMA ⟹ ∞ many `t ∈ ℤ₊ⁿ` with `δ(g_tΛ_y) ≤ e^{-γt}` | | TODO |
| Prop 2.3 | measure bound `|{x∈B : δ(g_tΛ_{f(x)})<ε}| ≤ D(ε/ρ)^{1/dl}|B|` | | TODO |
| Theorem A | a.e. nondegenerate ⟹ strongly extremal | | TODO |
| Lemma 3.1 | (a) `|f|`, (b) `λf`, (c) `sup_i|f_i|` stay `(C,α)`-good | `KleinbockMargulis/Good.lean` | TODO |
| Prop 3.2 | `deg f ≤ k` ⟹ `(2k(k+1)^{1/k},1/k)`-good on ℝ | `KleinbockMargulis/PolynomialGood.lean` | TODO |
| Lemma 3.3 (+3.3.1, 3.3.2) | `C^k` derivative-sandwich ⟹ cube estimate `(3.5)` | `KleinbockMargulis/SmoothGood.lean` | TODO |
| Prop 3.4 | nondegenerate point ⟹ all linear combos of `1,f_1,…,f_n` are `(C,1/dl)`-good near it | `KleinbockMargulis/Nondegenerate.lean` | TODO |
| Theorem 4.1 | measure of unmarked points `≤ kC(3^d N_d)^k (ε/ρ)^α |B|` | `KleinbockMargulis/Marked.lean` | TODO |
| Lemmas 4.2–4.6 | supporting | same | TODO |
| Lemma 5.1 | `‖Λ‖ ≤ k‖Γ‖·‖v‖` | `KleinbockMargulis/LatticeNorm.lean` | TODO |
| Theorem 5.2 | quantitative nondivergence | `KleinbockMargulis/Nondivergence.lean` | TODO |
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

## Log
- 2026-08-21 — created; paper source read in full (arXiv e-print `mb.tex`).
