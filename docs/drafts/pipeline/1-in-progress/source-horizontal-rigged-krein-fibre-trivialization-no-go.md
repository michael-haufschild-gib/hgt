# Source-horizontal rigged Krein fibre trivialization no-go

- **ID:** source-horizontal-rigged-krein-fibre-trivialization-no-go
- **Stage:** 1-in-progress
- **Type:** CONJECTURE / PRODUCER-CLASS NO-GO
- **Source:** CCM-FU · `SUZUKI-FE-REFLECTED-WALL-WARD-ASSEMBLY`
- **Statement:** Any two off-wall pre-divisor rigged Witt fibres in one horizontal chamber are continuously diagonally congruent on the fixed Deninger height--Köthe source.

## Goal

Kill every CCM-FU producer depending only on the pointwise topological Krein-isomorphism class of
the already-built rigged source. This removes abstract index, radical, fundamental-symmetry, and
polarization arguments from the remaining Ward burden. A survivor must retain fixed source
coordinates or compare different fibres by a relative trace/connection.

Proof chain targeted:

`tame diagonal fibre congruence`
→ `pointwise Krein-isomorphism invariants are constant on each open half-strip`
→ `such invariants cannot force the critical wall for a hypothetical off-wall Xi copy`
→ kill this CCM-FU producer class before `SuzukiRectangularWardDefectBoundedness`.

## Gates

- [x] 0 → 1 in-progress: source-pure statement, exact transport, hostile falsifiers, literature audit
- [ ] 1 → 2 fully-proven: complete tame-multiplier and congruence proof
- [ ] 2 → 3 formalized: Lean theorem and route-kill certificate, targeted build and axiom audit
- [ ] 3 → 4 publication-ready

## Corpus basis

- `preDivisorRiggedPrimeWittPhaseObject_capstone`: fixed Köthe source, exact weights and pairing.
- `primeGammaCofinalBocksteinMagnitude_bounds`: each off-wall weight is comparable to
  `p^(|t|-1)` with positive grade-dependent lower constant.
- `deningerHeightSeminorm_mul_le`: polynomial-height multipliers act tamely.
- `preDivisorRiggedPrimeWittPairing_globalIndexClassification` and
  `preDivisorRiggedPrimeFundamentalSymmetry_capstone`: index/radical/polarization already closed.
- `fisherDeconvolvedSameCarrierOrientationLaw`: fixed-coordinate prescribed transport detects the
  wall; it does not contradict fibrewise equivalence after coordinate rescaling.

## Conjecture K1

For open-strip off-wall `s,t` with the same source orientation, put

`r_p(s,t)=sqrt(w_s(p))/sqrt(w_t(p))`.

Extend `r_p` by `1` off the positive valuation-one prime axes. Coordinate multiplication by this
field and by its reciprocal preserves `DeningerHeightKothe`, with finite seminorm loss, the maps
are inverse, and

`B_t(R_(s,t)a,R_(s,t)b)=B_s(a,b)`.

For opposite orientations the same formula gives anti-congruence.

## Paper attack

1. Off wall, every `w_t(p)>0`; hence `r_p` is defined and reciprocal.
2. Bockstein bounds give `c_t/p ≤ w_t(p) ≤ 1`. Therefore `r_p` and `r_p⁻¹` have at most
   polynomial prime growth. Since height of the valuation-one axis is `p`, both diagonal fields
   are tame Köthe multipliers.
3. Coordinatewise reciprocal identities give inverse linear maps.
4. `sqrt(w_t) r_p=sqrt(w_s)` and `w_t r_p²=w_s`; termwise identities transport both diagonal
   series and common reservoir functional, hence the full rank-one-difference pairing.

## Hostile audit

- Wall fibre excluded: every weight is zero there, so no inverse transport exists.
- Same fixed coordinates are not preserved; fixed-carrier Fisher descent can still detect neutral
  grade. Claimed kill concerns isomorphism-invariant pointwise geometry only.
- Imaginary part is irrelevant because corpus weights depend on `Re(s)`; no zero data enter.
- A mere algebraic finite-packet congruence is insufficient: both multiplier directions and finite
  Köthe seminorm loss are required.

## Literature audit (through 2026-08-31)

- Suzuki, arXiv:2606.09096v2, studies Weil quadratic forms and conjectural nonlocal finite-interval
  operator limits, not this pre-divisor prime-weighted Köthe family.
- Kalmes--Santacreu, arXiv:2301.11186, gives general weighted-shift criteria on Köthe echelon
  spaces; Dimant--Villafañe, arXiv:1706.04901, studies general diagonal multilinear operators.
- Connes--Consani, arXiv:1910.14368, analyzes semi-local Weil positivity and Li's failed route,
  not a continuous congruence classification of these rigged Bockstein fibres.
- No located source states K1 or its CCM-FU route-class consequence.

## Log

- 2026-09-01 — conjectured only after corpus rediscovery audit established existing unbounded
  index, exact global radical/index, fundamental symmetry, and positive polarization.
