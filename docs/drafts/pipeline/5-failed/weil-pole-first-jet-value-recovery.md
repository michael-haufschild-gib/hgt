# Recovering a pole value from two mass totals and its first derivative

Status: generic recovery shortcut closed. The actual Weil pole route remains open.

**Claim rejected:** nonnegative arithmetic weights, their ordinary and reciprocal totals, and the resulting entire diagonal and cross first derivative determine the cross value. No claim about recoverability from the full literal Mangoldt sequence is rejected.

**Exact obstruction:** on the genuine prime-power support 2,3,4, every nonnegative triple with total six and reciprocal total two is `(2t,6(1-t),4t)`, `0≤t≤1`. The diagonal response is the fixed function `4exp(s)-12exp(-s)` and the cross derivative is always 16. The cross value is `16s-8log 3-t(13log 2-8log 3)`, with a strictly positive coefficient. Thus the derivative data do not determine its intercept.

**Strongest positive survivor:** complete classification of all model weights and an exact attainable cross-value interval, not only two counterexamples. In the actual source, the omitted value data are precisely the finite moment `H(a)=sum Lambda(n)(1+1/n)log n`; actual even nonnegativity is exactly `H(a)≥2a(psi(exp(2a))+M1(exp(2a)))-A(a)-C_sm(a)`. The stationarity equation separately forces square-root pointwise Chebyshev error at every actual stationary even pole above radius two, including actual interior gap minima.

**Paper proof:** dependency-closed in [stationary error and value moment](../3-formalized/weil-pole-stationary-error-and-value-moment.md).

**Lean:** `CCMRestrictedWeilPoleFirstJets`, `CCMRestrictedWeilPoleStationaryError`, `CCMRestrictedWeilPoleLogMoment`; key results `ccmWeilThreeAtom_mass_classification`, `ccmWeilThreeAtomCross_range_iff`, `ccmWeilThreeAtom_equal_jets_different_values`, `ccmWeilEvenPole_nonneg_iff_logMoment`, and `abs_prime_error_le_at_ccmWeilEvenPole_gap_minimum`. Final audit is recorded on the formalized card.

**Remaining arithmetic task:** prove the actual logarithmic-moment threshold or a stronger comparison implying it. Arbitrary nonnegative weight deformations cannot replace the original Mangoldt source.
