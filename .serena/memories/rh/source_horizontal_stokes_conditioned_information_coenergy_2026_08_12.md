# Source-horizontal Stokes-conditioned information coenergy (2026-08-12)

Frozen Frankenstein seam combining Route-P information virial (P-G55/P-G58), P-G70 reflected Stokes carrier, and Gamma-six strip-slack invariant.

For 0<s<1 and pk=(p,e), define J_s(pk) as sourceHorizontalPrimeGeometricKLScaleTerm p e ((1-s)/2) times gammaSewnMobiusApertureStokesReflectedWeight s pk. Proved unconditionally:

0 < J_s(p,e) <= 4(1-s) p^(-2) (p^(-s))^(2e)/(e+1)^2.

Consequently complete prime-power family is summable and total coenergy is strictly positive. Exact mechanism: KL gives r^(e+1); reflected inverse-gap weight gives r^e/r; together retain r^(2e). Fixed Möbius aperture yields p^-2. This supplies exactly two reciprocal prime-clock exponent units demanded by prior renewal-codimension/strip-slack no-go.

Lean module: formal/GaloisForLFunctions/RHTower/SourceHorizontalStokesConditionedInformationCoenergy.lean. Wired into RHTower.lean after GammaSewnMobiusApertureStokesReflectedCompactCarrier. Direct lake env lean check passed; exact leaf lake build passed; public theorem axiom audit only propext, Classical.choice, Quot.sound; no forbidden declarations/tokens.

Card: docs/drafts/pipeline/1-in-progress/source-horizontal-stokes-conditioned-information-coenergy.md (stage 3 formalized bridge survivor). Frontier map updated with seam.

Not RH. Sharp open core: prove a completed prime--Gamma seam identity placing this strictly positive coenergy against a source-forced zero or opposite sign. More damping/summability/Herglotz carrier construction is not progress.

Killed before seam: C0 fixed-matrix reciprocal properness on Route U (wrong type/circular); C1 naive P passive + Suzuki semibounded form positivity (false as stated; missing completion comparison). Novelty priority remains unverified; parent Herglotz/regularized Cauchy theory classical, exact arithmetic pairing not found.