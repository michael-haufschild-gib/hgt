# The first odd lag cost retains a primitive square

- **ID:** F1-M1
- **Stage:** 2-fully-proven; Lean formalization in progress
- **Type:** THEOREM (paper)
- **Source:** [Retained Gamma payment](../3-formalized/f1-gamma-lag-moment-payment.md)
- **Statement:** For a real continuous odd source supported in `[-1/2,1/2]`,
  put `H(x)=∫_{−1}ˣF`, `E=∫F²`, and `C(t)=∫F(x)F(x+t)dx`. Then
  `∫₀¹tC(t)dt=−∫H²` and `M₁=E/2+∫H²`.

The corpus supplies the derivative identities `A_H′=crossCorr H` and
`(crossCorr H)′=−A_{H′}` in
`ArithmeticCompensationTheory.TheResolventIdentityAndSecondHorizonCorrection`.
Oddness makes `H` compactly supported and `H′=F`. Thus
`(A_H(t)−t A_H′(t))′=tC(t)`. Integration over the positive ray leaves
`−A_H(0)=−∫H²`; the correlation of `F` vanishes past one.

Together with the exact second moment, the Gamma payment becomes

`ΓE+J∞ ≥ ∫₀¹(E−C)/t − (γ+logπ+log2+1/48)E
 −(∫H²)/24−(∫xF)²/16`.

This retains the two source-dependent losses. It does not establish the joint
prime-reflection and pole sign. Lean obligations: instantiate the compact primitive,
apply the correlation derivative identities, and audit the Gamma corollary.

Integration by parts also gives `∫xF=−∫H` and
`∫2sinh(x/2)F=−∫cosh(x/2)H`. Thus the position square and sinh pole act on the
same primitive as the first lag cost. These two identities are not yet Lean-audited here.
