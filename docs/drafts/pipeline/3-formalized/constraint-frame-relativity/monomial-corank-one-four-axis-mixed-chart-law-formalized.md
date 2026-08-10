# Quadratic-exponent monomial corank-one mixed-chart law — formalized

- **ID:** `cfr-monomial-four-axis-mixed-chart-formalized`
- **Stage:** 3-formalized
- **Paper proof:** `monomial-corank-one-four-axis-mixed-chart-law.md` (same directory)
- **Status:** `[LEAN COMPLETE] [UNCONDITIONAL] [NO SORRY] [NO NEW AXIOMS]`

## Lean modules

| Module | Path |
|---|---|
| `GaloisForLFunctions.HTGeometry.ConstraintFrameRelativity.MonomialMixedChart` | new |

Wired into `GaloisForLFunctions.HTGeometry`.

## Formal theorem chain

All declarations live in namespace `HTGeometry.ConstraintFrameRelativity`.

Section 1–3 — the maximal minors and the common support, card `(1)`, `(2)`, `(5)`, `(6)`:

1. `det_diagonal_minor` — the minor omitting the constant column is `∏_j d_j`, which for
   `d_j = T^{j} U^{j²}` is `T^{S_n} U^{Q_n}`.
2. `det_updateCol_one` — the minor omitting the `k`-th diagonal column is `∏_{j ≠ k} d_j`, which is
   `T^{S_n - k} U^{Q_n - k²}` up to the sign fixed by the column order.  The proof is the Leibniz
   expansion: any permutation other than the identity moves some index away from `k`, and that
   factor of the product vanishes.
3. `minors_ne_zero` — every maximal minor is nonzero once every `d_j` is, so the underlying matroid
   is the uniform matroid `U(n, n+1)`.  The arithmetic and phase-valuated specialisations are the
   two evaluations of the same product formula, so they share support while retaining different
   coefficients.

Section 4 — Gram orientation loss, card `(7)`, `(8)`, `(12)`:

4. `monomialChart` — the evaluated chart `[D ∣ 1]`.
5. `gram_monomialChart` — the boxed Gram formula `(12)`: `A Aᴴ = diag(ρ², …, ρ^{2n}) + 1 1ᵀ`, which
   in particular does not depend on `θ`.
6. `gram_rephase` — the boxed invariance `(8)`: any diagonal unitary rephasing of the columns
   leaves the Gram matrix unchanged.
7. `chartCircuit`, `monomialChart_circuit` — the unique circuit `(7)`, annihilated by the chart.
8. `circuit_sign_flip` — the anchored circuit coordinate is nonzero, so the `−1` rephasing of the
   first column genuinely changes it while the Gram matrix is fixed: this is the exact orientation
   loss.

Section 7 — quantitative aperture inverse loss, card `(3)`, `(4)`, `(14)`, `(15)`:

9. `chartRightInverse`, `chart_mul_rightInverse` — the distinguished diagonal right inverse.
10. `sum_normSq_chartRightInverse_le` — its norm bound `‖R‖ ≤ ρ^{-n}`, the upper bound of `(4)`;
    the exponent is exactly `n`, so each aperture extension loses one factor `ρ^{-1}`, which is
    card `(15)`.
11. `rayleighWitness`, `sum_rayleighWitness`, `sum_normSq_rayleighWitness` — the unit vector
    orthogonal to the constant column used in card `(14)`; combined with item 5 its Rayleigh
    quotient is `(ρ^{2(n-1)} + ρ^{2n})/2`, which bounds the least Gram eigenvalue and gives the
    lower bound of `(4)`.

Sections 5–6 — prolongation and winding, card `(9)`, `(10)`, `(11)`:

12. `prolongationVector` — the first logarithmic `U`-prolongation vector `J_n` of `(10)`.
13. `prolongationVector_ne` — it is nonconstant, so the bare support matroid cannot determine it.
14. `prolongationVector_not_constant` — it is not a multiple of the all-ones vector, i.e. its class
    modulo the common projective winding `(11)` is nonzero: the observed projective phase closes
    after one loop while the lifted history does not.

## Verification

```text
lake env lean GaloisForLFunctions/HTGeometry/ConstraintFrameRelativity/MonomialMixedChart.lean  # clean
#print axioms  ⇒  propext, Classical.choice, Quot.sound
```
