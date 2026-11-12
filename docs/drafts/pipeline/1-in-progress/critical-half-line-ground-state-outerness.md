# Critical half-line ground-state outerness

- **Stage:** 1-in-progress
- **Target:** B104 and the outer-predictor obstruction in B4.
- **Conjecture:** The reflected actual critical state is cyclic for causal translations in the half-line L² space.
- **Status:** Open; not counted.

## Connection

The actual weak equation and causal reflection exclude open-right-half-plane Laplace zeros. Boundary exclusion is undergoing Lean verification in `critical-half-line-boundary-laplace-exclusion.md`. Neither statement alone establishes cyclicity: a delay preserves zero-freeness.

The arithmetic energy is translation invariant, while translating toward the endpoint strictly lowers the exponential mass. Thus a critical state should have positive L² mass in every interval `(-d,0)`, `d>0`: otherwise its right translate remains admitted and has negative full energy, contradicting endpoint nonnegativity.

## Remaining inputs

1. Verify the drafted actual-domain translation law and endpoint-mass theorem. The exact energy change for `F(u+c)` is `alias(R) (exp(8c)-1) I₈(F)`. If mass in `(-d,0)` vanishes, truncate at `-d/2`, obtaining an equal almost-everywhere representative, then shift right by `d/2`. Its strictly negative full energy contradicts endpoint nonnegativity.
2. Connect exponential integrability, closed-half-plane zero-freeness, and absence of a support gap to causal cyclicity. Corpus inner/outer factorization is available, but no applicable theorem eliminating a singular inner factor has yet been identified.

`PoissonBoundaryPositivity.exists_poissonRepresentation` supplies a finite representing measure. Its `measureReal_Icc_eq_zero_of_radial_tendsto_zero` requires arbitrarily small bounds at **every** radius, not merely near the boundary; it cannot directly justify this step. A local boundary-convergence version remains to be proved.

No implication to nonvanishing of the arithmetic polar pairing is established. Zero-freeness and endpoint support alone must not be substituted for a proof of cyclicity.

## Factorization route

Transport the bounded Laplace transform to a disk multiplier and use `DiskMultiplierInnerOuterFactor`. Closed-half-plane nonvanishing makes the logarithm of the inner factor's modulus harmonic. Local Poisson convergence of the outer logarithm would make its representing measure vanish away from the Cayley point at infinity. Concentration there would identify the inner factor as a pure exponential delay, up to a unit scalar.

`DiskSmirnovBoundary.exists_hardyDisk_of_memLp_two_circleBoundary` supplies the Hardy admission needed after removing that delay. Combine the Cayley boundary identification, half-plane Paley–Wiener theorem, `causal_laplace_delay`, and Laplace uniqueness to obtain an actual support gap, contradicting the endpoint-mass theorem. Local outer-logarithm convergence, concentration-to-exponential identification, and the final cyclic-span transport remain unproved.

An alternative avoids continuity of the outer logarithm and analytic continuation across the boundary. For a bounded factorization `f=IO`, the positive harmonic defect satisfies `0≤-log|I|≤log||O||∞-log|f|`. The actual profile's L¹ admission gives continuity of f on the closed right half-plane. Boundary nonvanishing therefore bounds the defect locally on every finite boundary arc. Its radial boundary value is zero almost everywhere because I is inner.

The needed local Poisson estimate is `ν([α,β])≤2∫_[α−η,β+η] u(re^{iθ})dθ` for `1−r≤η`: each boundary point in `[α,β]` contributes at least one half through its angular interval of radius `1−r`. Fubini proves the estimate. Local boundedness and almost-everywhere radial vanishing then remove arc mass by dominated convergence. This argument has a complete Lean draft but remains unverified. `BoundedPoissonTransformAbsoluteContinuity` supplies the analogous real-line mass mechanism.
