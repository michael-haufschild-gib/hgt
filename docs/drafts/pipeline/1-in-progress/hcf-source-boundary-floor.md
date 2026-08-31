# HCF source-boundary floor

- **ID:** HCF-BOUNDARY-FLOOR
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** HCF/Plemelj source covariance
- **Statement:** Prove
  `CriticalFeatureCanonicalAsymptoticLower sourceBoundary (4*pi - 4/25)`
  without selecting the `XiC` divisor before scalarization.

## Exact frontier

Lean now proves

`phaseCovariance/N + sourceBoundary/N -> 4*pi`

and therefore proves that the desired `4/25` covariance ceiling is equivalent to this boundary
floor. Gamma winding and endpoint errors are fully eliminated.

Boundary carrier audit: each phase-averaged finite-lattice cutoff weight is at most `2*pi`, and the
Plemelj representation gives

`sourceBoundary(n) <= 2*pi * (multiplicity of real XiC zeros in the cutoff packet)`.

Hence phase averaging cannot manufacture missing mass. Remaining proof must establish almost-maximal
real-boundary mass from a prime/source identity. Any argument that invokes the real-zero packet to
obtain the lower bound is circular.

## Conjecture loop

- `[FAILED]` Balanced-Perron third difference: localizes Dirichlet coefficient index, not HCF height
  covariance; no source-only carrier weld.
- `[PROVED HERE]` Universal winding is `4*pi*N + o(N)`.
- `[PROVED HERE]` Covariance ceiling iff source-boundary floor.
- `[PROVED HERE]` Boundary phase averaging has a sharp `2*pi` per-real-zero upper capacity.
- `[OPEN]` Construct a pre-Plemelj prime/Gamma lower certificate for the boundary limit with total
  mass `(4*pi - 4/25)N + o(N)`.

## Lean status

Formalized in
`formal/GaloisForLFunctions/RHTower/HedenmalmCriticalFeatureFirstOrderWindingAsymptotic.lean`:

- `tendsto_criticalFeatureCanonicalFirstOrderPoleGammaWinding_div_zeroCount`
- `tendsto_criticalFeaturePhaseCovariance_add_boundary_div_zeroCount`
- `criticalFeaturePhaseCovariance_fourTwentyFifths_upper_iff_sourceBoundary_lower`
- `exists_criticalFeatureSourceBoundaryPhaseAverage_le_realZeroMultiplicity`
