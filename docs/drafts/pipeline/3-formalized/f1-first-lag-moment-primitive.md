# The first odd lag cost retains a primitive square

- **ID:** F1-M1
- **Stage:** 3-formalized
- **Type:** THEOREM; individually Lean-audited
- **Source:** [Retained Gamma payment](f1-gamma-lag-moment-payment.md)
- **Statement:** For a real continuous odd source supported in `[-1/2,1/2]`,
  put `H(x)=∫_{−1}ˣF`, `E=∫F²`, and `C(t)=∫F(x)F(x+t)dx`. Then
  `∫₀¹tC(t)dt=−∫H²` and `M₁=E/2+∫H²`.

The corpus supplies the derivative identities `A_H′=crossCorr H` and
`(crossCorr H)′=−A_{H′}` in
`ArithmeticCompensationTheory.TheResolventIdentityAndSecondHorizonCorrection`.
Oddness makes `H` compactly supported and `H′=F`. Thus
`(A_H(t)−t A_H′(t))′=tC(t)`. Integration over the positive ray leaves
`−A_H(0)=−∫H²`; the correlation of `F` vanishes past one.

Integration by parts also gives `∫xF=−∫H` and
`∫2sinh(x/2)F=−∫cosh(x/2)H`. Thus the position square and sinh pole act on the
same primitive as the first lag cost.

For C² sources, combining the retained Gamma estimate with both lag identities gives

`ΓE+J∞−½(∫2sinh(x/2)F)² ≥ ∫₀¹(E−C)/t − (γ+logπ+log2+1/48)E
 −(∫H²)/24−(∫H)²/16−½(∫H cosh(x/2))²`.

**Lean:** `LatticeSectionTheory.WindowJumpCounts.OddAutocorrelationFirstMoment` proves
`derivative_autocorr_first_moment`, `unit_odd_primitive_regular`,
`unit_odd_autocorr_first_moment`, and `unit_odd_jump_first_moment`.
`WindowTowerOfSpecZ.TheGammaComparisonRetainsItsLagMoments` proves the position and sinh
identities and `unit_odd_gamma_pole_primitive_lower`. Both individual `lake --old env lean`
source audits pass; transitive axioms are `[propext, Classical.choice, Quot.sound]` only.
Both modules are wired into their umbrellas. The signed prime reflection still requires
joint payment; this lower bound does not establish its sign.
