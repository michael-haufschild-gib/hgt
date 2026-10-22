# Qubit--Bethe--GADC squaring universality law

- **ID:** qubit-bethe-gadc-squaring-universality
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean)
- **Source:** theorem-first closure of `PostselectedQubitRationalDynamics`,
  `BetheHolographicIsingRG`, and `GADCTreePopulationRG`
- **Statement:** The experimentally realized qubit orthogonalizer is exactly the depth-two
  noiseless Bethe/GADC tree renormalization map, independently of bath population; its homogeneous
  projective lift is conjugate to squaring and its zero-message multiplier is exactly two.

## Gates

- [x] 0 → 1 in-progress: generated from verified Lean endpoints
- [x] 1 → 2 fully-proven: dependency-closed paper proof, `[PROVED HERE]`
- [ ] 2 → 3 formalized: exact-file Lean passed; final axiom audit pending
- [ ] 3 → 4 publication-ready: post-proof literature audit complete; final audit pending

## Corpus inputs

- `qubitPowerCoordinate_after_experimental`
- `gadcTreePopulationRG_zeroDamping`
- `gadcTreePopulation_linearMultiplier`
- `betheHolographicIsing_linearMultiplier`
- definitions `experimentalQubitOrthogonalizer`, `experimentalQubitProjectiveMap`,
  and `betheHolographicIsingRG`

## Proof

`[PROVED HERE]` Expanding the depth-two, unit-transmissivity Bethe numerator gives
`(1+X)^2-(1-X)^2=4X`; its denominator gives
`(1+X)^2+(1-X)^2=2(1+X^2)`.  Cancelling their common scalar factor two in the rational-function
field leaves `2X/(1+X^2)`, exactly `experimentalQubitOrthogonalizer`.

The corpus zero-damping identity identifies every bath-population slice
`gadcTreePopulationRG 2 0 N` with that same Bethe map.  The corpus projective identity then
conjugates its homogeneous qubit lift `(2xy,x^2+y^2)` to coordinatewise squaring under
`(x,y) ↦ (x+y,y-x)`.  Finally, either the Bethe multiplier formula `p a` at `(p,a)=(2,1)` or the
GADC multiplier formula `p(1-d)` at `(p,d)=(2,0)` gives the exact multiplier two, independent of
`N`.  No computation or unproved analytic input is used.

## Lean certificate

- Module:
  `GaloisForLFunctions.HTGeometry.QubitBetheGADCSquaringUniversalityLaw`
- Main theorem:
  `GaloisForLFunctions.HTGeometry.qubitBetheGADCSquaringUniversality`
- Exact source check:
  `lake env lean GaloisForLFunctions/HTGeometry/QubitBetheGADCSquaringUniversalityLaw.lean`
  passed warning-free on 2026-07-23.
- Imported by `GaloisForLFunctions/HTGeometry.lean`.

## Novelty protocol

No literature search before exact Lean proof.

## Post-proof literature audit

Performed only after exact Lean source check passed.

- Zhu--Kalman--Wang--et al.,
  *Experimental orthogonalization of highly overlapping quantum states*
  ([arXiv:1910.10377](https://arxiv.org/abs/1910.10377)), supplies the experimental nonlinear
  postselected-qubit protocol.
- Okunishi--Takayanagi,
  *Statistical Mechanics Approach to the Holographic Renormalization Group: Bethe Lattice Ising
  Model and p-adic AdS/CFT*
  ([arXiv:2310.12601](https://arxiv.org/abs/2310.12601)), supplies the Bethe-lattice holographic RG
  setting.
- Targeted searches for the exact qubit/zero-damping-GADC/depth-two-Bethe identification and its
  simultaneous bath-independent multiplier/squaring-conjugacy law found no matching statement.
  Classical double-angle and rational-map conjugacy identities are adjacent, but the three-model
  identification was not found.

No exact literature match was found.  Door 2 remains open rather than claimed closed.

## Log

- 2026-07-23 — Shared-parent terminal scan exposed a missing exact connector between the
  experimental qubit map and noiseless depth-two tree renormalization.
- 2026-07-23 — Main theorem exact-checked warning-free, wired into the HTGeometry umbrella, and
  post-proof collision search found no exact three-model law.
