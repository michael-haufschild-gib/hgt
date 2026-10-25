# Vaughan packet Gram identities

- **ID:** vaughan-packet-gram-identities
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** uniform-second-scale-vaughan-gram-at-all-cutoffs.md
- **Statement:** Finite centering commutes with Vaughan superposition, and the exact centered packet energy is the quadratic form of its Gram matrix.

For every real damping, both natural cutoffs, every real coefficient vector
`w : Fin 5 → ℝ`, and every horizon:

- The centered packet is exactly `Σ_i w_i p_iᶜ`.
- For the smooth sign vector `s=(0,0,−1,1,0)`, `Σ_i w_i s_i=w_3−w_2`.
- Its pronic energy is exactly `Σ_i Σ_j w_i w_j Gᶜ_ij`.
- Each centered row energy equals the corresponding Gram diagonal.

These finite algebraic identities require no convergence or analytic estimate.
They are shared by the subcritical logarithmic and endpoint packet laws.

## Lean audit

Module: [VaughanPacketGramIdentities.lean](../../../../formal/GaloisForLFunctions/BezoutValuationIncidence/VaughanPacketGramIdentities.lean).

- `pmPronicVaughanCentredPacket_eq_sum`
- `sum_mul_pmPronicVaughanSmoothSigns`
- `sq_pronicNorm_pmPronicVaughanCentredPacket_eq_gram`
- `sq_pronicNorm_pmPronicVaughanCentredPiece`

Producing and final direct `lake --old env lean` checks passed. All four
transitive axiom reports contain only `propext`, `Classical.choice`, and
`Quot.sound`. The mathlib APIs were already verified in earlier scratch files;
no redundant full scratch pass was needed. The BVI umbrella import is present,
the owned scratch was removed, and no limits were raised.

The uniform packet bounds are now checked in
`uniform-logarithmic-laws-for-vaughan-superpositions.md`. These finite identities
do not settle a fixed strip or full Q-I.
