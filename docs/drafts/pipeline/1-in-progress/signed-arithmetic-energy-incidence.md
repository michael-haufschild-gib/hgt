# Signed Arithmetic Energy and Incidence Theory (SAEI)

- **ID:** saei
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean) — programme
- **Source:** docs/reports/review-2210/hard-obstacles-summary.md § 4
- **Statement:** How does exact multiplicative incidence constrain signed quadratic energies across
  scale, and which of those constraints survive coordinate change, regularization and completion?

## Goal
A Lean programme (`formal/GaloisForLFunctions/SignedArithmeticEnergyIncidence`) supplying the
interface theorems between O2–O5 and O7: local payment versus global positivity on signed
incidence graphs, defect accounting under completion, the graded norms of the damping chain,
profile compactness of adverse sequences, and the radial structure of damping continuation.

Non-circularity: every structural theorem is unconditional finite-dimensional or Hilbert-space
mathematics, and every arithmetic instance names its source (Möbius row, damping chain,
reciprocal observable) and its norm; nothing is selected from the zeros.

## Gates
- [x] 0 → 1  in-progress: objects fixed (signed incidence forms, pair payability, balance,
  polar defect, chain orbit, adverse sequences)
- [ ] 1 → 2  fully-proven: paper proofs of the pillars
- [ ] 2 → 3  formalized: Lean modules + umbrella wiring
- [ ] 3 → 4  n/a

## Approach
1. Signed incidence forms; pair payability; switching; ground-state transform.
2. Balanced incidence is locally payable (discrete Allegretto–Piepenbrink, compactness limit).
3. Frustration is the local–global gap (rank-one charges on three points; frustrated triangle).
4. Chain lending and the sine certificate for uniform trains (capacity `2cos(π/(L+1))`).
5. Polar defect law (rank-`r` Gram criterion; unbounded polar functionals kill every floor).
6. The receiver as the chain orbit of the reciprocal `1/k`; `ℓ²`-bounded chain implies admission;
   the uncentred transition is `ℓ²`-unbounded at every damping.
7. Residue modes in the receiver norm; sign-blind threshold at half damping.
8. Adverse profiles cannot vanish when the negative part is finite rank; escape model.
9. Radial loss law for signed continuation.

## Lean assets
(filled as modules land)
