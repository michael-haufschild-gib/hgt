# The valuation tower is exactly solvable

- **ID:** rapt-valuation-tower-exactly-solvable
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** continues `rapt-archimedean-place-pays-the-tower-deficit`, `rapt-matched-prime-place-hodge-index-on-classes`.
- **Statement:** The matched prime place on the `p`-adic classes, `H_p = diag(j log p) + γ_p + log p − log p K_{p^{−1/2}}`,
  has the pole profile `p^{−j/2}` as eigenvector with eigenvalue `γ` and, for `k ≥ 1`, the valuation
  steps `p^{−j/2}(1_{j ≥ k} − (p − 1)^{−1} 1_{j = k − 1})` with eigenvalue `γ_p + k log p`. Eventually in
  `M`, on every class combination of depth `≤ J`:
  `P_M(x) + (p/(p − 1) − η) log p |x|² ≤ (log M − γ + η)|x|² + (log p/|w_0|²) ℓ(x)²`.

## Proof

Eigen-equations in the pole gauge: `(L y)_i = Σ_{j ≤ i}(y_i − y_j) + Σ_{j > i} p^{−(j−i)}(y_i − y_j)`;
for the step at `k` the three cases `i < k − 1`, `i = k − 1`, `i ≥ k` reduce to the geometric sums
`Σ_{t ≥ 0} p^{−(t+1)} = 1/(p − 1)` and its tails. Sharp gap: the row slack of the valuation Gram is at
least `m_J/(p − 1)` (`Σ_{k<K} m_{j+1+k} + m_{j+K}/(p−1) ≤ m_j/(p−1)` for descending masses); adding it
to the complete-graph comparison completes the tower mass to `Σ_{j ≤ J} m_j + m_J/(p − 1)`, whose ratio to
`m_0` tends to `Σ_{j≤J} p^{−j} + p^{−J}/(p − 1) = p/(p − 1)` exactly.

## Significance

The second eigenvalue of the matched prime place on the `p`-classes is exactly `γ + p log p/(p − 1)`
(first valuation step), uniformly in the depth. At `p = 2` this is `γ + 2 log 2`, which numerically is
the second eigenvalue of the full atomic prime form (`log N − λ₂(P_N) → γ + 2 log 2`, N ≤ 32000): the
second eigenvector of Weil's prime form is the first excitation of the 2-adic tower. Spectrum of the
Kronecker sum over primes: `γ + Σ_p ε_p`, `ε_p ∈ {0} ∪ {log p (k + 1/(p − 1))}` — a Riemann gas whose first
quantum at `p` carries the local Euler shift `log p/(p − 1)`.

## Status

Lean: `formal/GaloisForLFunctions/RenormalizedArithmeticPotentialTheory/TheValuationTowerIsExactlySolvable.lean`
(`towerGaugeOp`, `towerOp_pole`, `valuationStep`, `towerOp_step`, `sum_range_shift_add_tail_le`,
`valuationGram_mulVec_one_le_tail`, `sum_cross_add_sharpGap_le_valuation`,
`eventually_sum_classMass_add_tail_ge`, `eventually_atomicWeilForm_classCombination_sharpGap_le`).
Clean exact-file check; axioms `propext, Classical.choice, Quot.sound`; wired in the RAPT umbrella.

Open: the gap on all vectors (Poincaré inequality for the multiplicative walk; numerically ≈ 1.24–1.30,
Efron–Stein constant ≈ 1.26–1.31 for measure `1/m` on `[1, N]`).
