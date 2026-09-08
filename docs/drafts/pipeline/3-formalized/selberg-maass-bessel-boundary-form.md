# Actual Maass cusp energy and the Bessel boundary form

- **ID:** SELBERG-MAASS-BESSEL-BOUNDARY-FORM
- **Stage:** 3-formalized.
- **Parent:** [Constructive Selberg loop](../1-in-progress/selberg-quarter-conjecturing-loop.md), cycle 23.
- **Scope:** Actual principal-congruence Maass cusp eigenforms with positive sub-quarter eigenvalue.

## Exact result

For the literal complex Fourier coefficient `a_n(y)`, let `k_n=|2*pi*n/(N+1)|` and let `B(k,y)` be the actual critical Bessel outgoing response. For every `n!=0` and every `Y>0`,

`integral_Y^infinity (|a_n'|^2+(k_n^2-1/(4*y^2))*|a_n|^2)`

`= B(k_n,Y)*|a_n(Y)|^2 + integral_Y^infinity |a_n'+B(k_n,y)*a_n|^2`.

Both integrands are integrable. The upper boundary current is proved to vanish from actual coefficient decay and the source Bessel envelope. The exceptional constant coefficient and its actual height derivative vanish.

Let `u` be the existing actual Maass Fourier trace at `Y=exp(T)`, in its proved Bessel form domain. The full physical quarter-energy tail satisfies

`(1/(N+1))*integral_Y^infinity quarterSlice`

`= boundaryForm(log(N+1),T,u) + sum_(n!=0) integral_Y^infinity |a_n'+B(k_n,y)*a_n|^2`.

The final series converges and every summand is nonnegative. Therefore the actual boundary form is a lower bound for the full physical cusp quarter-energy. Combining the previous exact flux identity gives

`-J(Y)+(lambda-1/4)*integral_Y^infinity M(y)/y^2`

`= boundaryForm(log(N+1),T,u) + sum_(n!=0) integral_Y^infinity |a_n'+B(k_n,y)*a_n|^2`.

This is the actual form previously expressed as principal frequency energy minus the positive compact correction. No substituted compact profile, assumed Maass Bessel ansatz, unknown upper boundary limit, or assumed interchange is used. The global Selberg bound remains unproved.

## Corpus-derived conjecture and proof choice

The existing `SelbergBesselBoundaryEnergy` factorization accepts compact real C¹ profiles. Applying it directly to complex noncompact Maass coefficients would be a type and mathematical mismatch. The inspected `ThetaCuspHawkingQuantumEnergyInequalityEndpoint` supplies the local density/current square pattern with the boundary retained. `DeningerTraceEnergy` supplies literal complex modal trace energy assembly. The direct real/imaginary algebra in `XiSquaredEulerApertureHilbertCorrelation` supports working with the complex square rather than inventing a real-profile instance.

The proposed finite-interval/logarithmic-height approach was replaced by a simpler physical-height argument: prove the current integrable and its endpoint limit zero, then use the improper fundamental theorem. For the full series, the inspected `HTGeometry.DominatedSeriesToLp` emphasizes explicit pointwise domination; Mathlib's inspected `hasSum_integral_of_dominated_convergence` supports an integrable height-dependent majorant on the infinite ray. The needed majorant comes from actual physical Parseval and the completed tail-energy theorem.

## Dependency-closed paper proof

1. Set `B(k,y)=(slope(k*y)-1/2)/y`. Differentiate the already-proved source Bessel Riccati equation to get `B'=B²-k²+1/(4*y²)`. The established outgoing envelope gives `k-1/(2*y)<B(k,y)<k`, so `B(k,y)->k` and `|B(k,y)|<=k+1/(2*Y)` on every positive tail.
2. For a literal complex coefficient, differentiate `|a|²` using its real and imaginary parts. This gives `(|a|²)'=2*Re(a'*conj(a))`. Polynomial expansion and the Bessel Riccati equation prove `(|a'+B*a|²-energy)=(B*|a|²)'`.
3. Each actual coefficient squared mass is bounded by the physical mass Parseval sum. Its actual squared height derivative is bounded by the physical gradient-energy sum. Thus both are tail-integrable. The hyperbolic coefficient mass is dominated by the actual hyperbolic slice mass. Consequently the signed mode energy is integrable.
4. The uniform tail bound on `B`, together with `|v+w|²<=2|v|²+2|w|²`, makes the actual square remainder integrable. The actual coefficient tends to zero; `B->k` therefore implies `B*|a|²->0`. The improper fundamental theorem gives the exact single-mode boundary identity.
5. The prior actual exceptional constant-term theorem gives `a_0=0` at every positive height. Local eventual equality with zero gives `a_0'=0`; hence its physical mode energy is zero.
6. For every mode, the absolute signed quarter-energy is bounded by the sum of its squared derivative, squared-frequency mass, and quarter-weighted mass. The majorant series has the literal Parseval sum `G(y)+M(y)/(4*y²)`, which is integrable on the infinite tail. Dominated convergence for series therefore identifies the sum of signed modal tail integrals with the normalized physical quarter-energy integral.
7. The actual boundary trace already lies in the Bessel form domain, so its seam series is summable. Match the positive physical frequency with the existing logarithmic `modeLog` and seam. Subtract the convergent seam series from the just-proved integrated energy series. The single-mode identities and the zero channel identify the result with the actual nonnegative square integrals. This proves their summability, the complete boundary-form identity, and its lower bound. Substitute the proved physical flux identity for the final capstone.

## Lean implementation and audit

- `GaloisForLFunctions.RHTower.SelbergMaassBesselRemainder`, namespace `SelbergMaassBessel`: response Riccati law and limit, actual coefficient integrability, noncompact complex square identity, boundary lower bound, zero constant-channel energy.
- `GaloisForLFunctions.RHTower.SelbergMaassBoundaryForm`, namespace `SelbergMaassBoundaryForm`: justified infinite mode/height interchange, exact actual trace/seam identification, convergent square series, full physical boundary-form and flux identities.

Both complete scratch proofs and direct source checks passed without warnings. Both serialized targeted final builds passed, each rebuilding its target alone: `/tmp/selberg_maass_bessel_remainder_build.log` and `/tmp/selberg_maass_boundary_form_build.log`. The existing `EvenL2LogUnitary` informational tactic message was replayed; neither new target produced a warning. No full or umbrella build ran.

All 28 public theorem axiom checks in `/tmp/selberg_maass_bessel_form_axioms.lean` report only `propext`, `Classical.choice`, and `Quot.sound` (`/tmp/selberg_maass_bessel_form_axioms.log`). Both modules are wired and indexed, and corpus searches return their capstones. Tracked and new task-file whitespace checks passed. **Latest repository-wide lint passed**, with existing large-file warnings (`/tmp/selberg_maass_bessel_form_lint.log`); the prior three unrelated unwired-module failures were resolved outside this task.

Every task-owned Lean/Lake invocation finished. A separate `DivisorTwentyTwoAnalyticBounds` Lean process was active at the final process audit and was not touched. This task made no commits.

## Remaining source question

The full physical cusp comparison is proved. The compact quotient core must now be attached, retaining its quarter-energy and matching every cusp boundary form. No positivity of that combined core form has been proved.

A fresh corpus search found `ThetaCuspHawkingBMModularLaplacian.chartLaplacian_modular_pullback`. Its public wrapper assumes `ChartSmooth`, while the inspected proof only uses real C² regularity at the image point and a holomorphic Möbius map. The actual Maass object provides C², not the stronger wrapper hypothesis. Next test a C² covariance theorem, then construct integral translates of the actual principal-congruence Maass object using the normalization of the real congruence image by integral `SL2Z`. This would transport the completed cusp identity to every integral cusp before attempting the finite quotient-core Green assembly. The core inequality remains an additional mathematical obligation.

The inspected finite-rank Schur and block-kernel corpus offers elimination identities, but no actual Maass core block, inverse, or positivity certificate is currently supplied. A matrix interface alone would not close this obligation, and none was added.
