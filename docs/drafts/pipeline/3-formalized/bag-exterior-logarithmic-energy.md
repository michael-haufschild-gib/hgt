# BAG complete exterior and global Mellin energy

2026-10-06,01ax. Dependency-closed paper proof; production Lean closure.
Module ChiCubicExteriorMellinEnergy:947lines/API5. Production99895/log01
terminal0 emptyPASS with lake --old env lean and explicit leaf olean.
All5 imported axioms37031/log01 terminal0 standard3 only.
Index85730/log01 terminal0/API5; RHTower import once; scoped diffcheckPASS.
Authoritative lint41249/log01 terminal1:362warnings,17 unrelated unreachable
modules, no finding on this leaf; global lint is NOT clean. Exact errors:
- error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.KontorovichLebedevInversion
- error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.KontorovichLebedevTransform
- error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.Sieve.TwistedSelbergCoefficient
- error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.Sieve.TwistedSelbergFactorization
- error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.Sieve.TwistedSelbergForms
- error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.Sieve.TwistedSelbergGcdLog
- error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.Sieve.TwistedSelbergGcdLogForms
- error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.Sieve.TwistedSelbergRatioForms
- error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.Sieve.TwistedSelbergSummability
- error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.VerticalProgressionRatioFibers
- error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.VerticalProgressionRatioForm
- error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.VerticalProgressionSecondMomentExpansion
- error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.HTGeometry: GaloisForLFunctions.HTGeometry.BernoulliShiftEntropy
- error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.HTGeometry: GaloisForLFunctions.HTGeometry.ConditionalEntropyGeneratingLimit
- error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.HTGeometry: GaloisForLFunctions.HTGeometry.CountableObservableEntropy
- error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.HTGeometry: GaloisForLFunctions.HTGeometry.FrozenHistoryEntropyClassification
- error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.HTGeometry: GaloisForLFunctions.HTGeometry.KolmogorovSinaiEntropy

Logs retained under /tmp/bag-exterior-mellin-*01ax.log.

Take the actual selected normalized cone f_N, with physical cutoff width
N^(1/4), and the fixed smooth chi supplied by CompactMellinLocalization.
The physical exterior is exactly f_N-chi*f_N. Since chi is one on an OPEN
neighborhood of the full stationary box[1/4,4]^2, every exterior jet vanishes
on that box. Outside, exact product rules and fixed cutoff jet bounds attach
the actual all-order physical decay. Thus orders0,1,2 have arbitrary N-saving
and arbitrary polynomial spatial decay on the ENTIRE positive quadrant.

For every positive Mellin parameter pair, logarithmic differentiation is
exactly the physical Euler operator E_i=-sigma_i-x_i D_i. Applying it twice
gives sigma_i^2*f+(2*sigma_i+1)*x_i*D_i*f+x_i^2*D_i^2*f. No cutoff term is
omitted. Sigma in[1,2]^2 gives uniform coefficients, so these actual Euler
combinations retain every requested polynomial spatial decay and N-saving.

Exact two-coordinate nonnegative logarithmic substitution gives density
x^(2*sigma0-1)*y^(2*sigma1-1)*|f(x,y)|^2. Both axis endpoints and both Jacobians
remain. A proved physical weight bound dominates this by a constant times
(1+|x|)^(-2)*(1+|y|)^(-2); native integration admits the majorant without
numerically evaluating it. This proves actual mass decay for the complete
exterior log profile and both pure second logarithmic derivatives.

Exact Fourier derivative norms retain(2*pi)^4; Schwartz Plancherel supplies
admitted mass. The full fourth weight is bounded by mass plus the two pure
fourth coordinate moments. Hence for EVERY natural k, ONE positive C bounds
full exterior H^2 energy by C/N^(2*k), eventually in N and for EVERY parameter
in[1,2]^2. No mixed derivative hypothesis or uniform Schwartz premise enters.

The public full profile is literally quadrantLogSchwartz applied to f_N.
It equals the existing compact localized profile plus the actual exterior,
pointwise as Schwartz maps. At every0<theta<1/2, full fractional energy of
the sum is at most twice the sum of energies. Exterior H^2 bounds its lower
H^(1+theta) energy; existing actual local energy closes the full global bound.
Public API: both actual profile definitions, exact decomposition, arbitrary
exterior energy decay, full selected Mellin uniform energy.

Conjecture progression: complex-specialized Euler algebra was repaired by
keeping native real-scalar differentiation polymorphic. Exact density was
kept through the axes; no stationary or compact replacement was used. The
final assembly passed after resolving dependent ENNReal numeral rewrites
and equivalent instance elaboration. No axioms, admissions or resource
increases were introduced.

Hard frontier remaining: complete source-weighted line tails, lower-growth
actual arithmetic envelope, moving-test signed cancellation, whole original
sharp-action bridge, growing moments/cofactors and deterministic common-height
return. Bare weightedL2 does not control the shrinking transverse source
concentration. Next P1 bag-source-saturated-pole-transfer records the actual
arithmetic/trace mechanism. This theorem does not prove RH.
