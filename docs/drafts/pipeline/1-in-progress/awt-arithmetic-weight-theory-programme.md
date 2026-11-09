# Arithmetic weight theory of Spec ℤ (AWT) — programme

- **ID:** awt-programme
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean), programme
- **Source:** docs/reports/review-0911/obstacles-summary.md §2.9
- **Statement:** Develop the field: families of Euler products with monodromy, `ζ` a special fibre, pure generic fibre, specialization of weights; answer Q1–Q3 of §2.9, build its tools.

## Goal
Answer: (Q1) which family carries `ζ` with big monodromy; (Q2) the analogue of `H²_c`; (Q3) the topology/direction of weight semicontinuity. Milestones M2 (generic fibre uniform moments), M3 (semicontinuity), M4 (`A_k = o(k)`).

Lean folder `formal/GaloisForLFunctions/ArithmeticWeightTheory/`, umbrella `ArithmeticWeightTheory.lean`, README there.

## Gates
- [x] 0 → 1 in-progress
- [ ] 1 → 2 / 2 → 3 per contribution below

## Approach (contributions; status)
1. `TheGenericFibreHasUniformWeights` — big monodromy `∫|Σ_p a_pχ_x(p)|^{2k} ≤ k!(Σ|a_p|²)^k`; a.e. fibre: uniform tensor moments `≪ N^{1+ε}` all `k`, traces `p^{o(1)}` (M2). **Lean, compiled.**
2. The jump at the trivial fibre: pole lower bound `T_0(log p) ≫ √p`; constant sets closed, conull union, miss a neighbourhood of `0`. — next.
3. Euler deformations: absolutely convergent prime perturbations are isozeric on `Re s > σ`; Haar-null class. — planned.
4. Geometric constancy of `M`: tensor series as sums over tuples of exponents; M4 ⇔ RH (`A_k ≥ 2k·width − 1`). — planned.
5. Top-layer monodromy: abscissa `1 + 2kb` for all `k` at an attained top; residue = Bohr mean of `F^{2k}`. — planned.
6. Curve calibration. — planned.

## Insights (for README)
- `M` is geometrically constant (Frobenius through `log n`); same for one curve over `𝔽_q`; Deligne's uniformity is a family statement (`X^k`, Lefschetz pencils).
- Gauge family is the Mellin family of the constant sheaf; trivial point = bad character: jump in `H⁰/H²` (pole), generic fibres have no cohomology right of `½`.
- Coherence: for nonnegative prime data the trivial fibre dominates every fibre; inequalities from the family run special ≥ generic.
- Constants vs exponents: constant sets are closed (Deligne direction holds for constants), exponents are tail invariants; the pole makes constants blow up at `0`.
- M4 as stated is RH.

## Log
- 2026-11-09 — created; README draft; contribution 1 compiled.
