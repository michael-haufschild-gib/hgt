# Regional logarithmic exterior and low-moment charges

- **ID:** F1-REI
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Source:** [Primitive variance payment](../1-in-progress/f1-primitive-variance-joint-payment.md)
- **Statement:** The logarithmic lag energy retains its exact exterior potential;
  the fifth regional gap retains its two explicit low odd moment charges.

For real odd C² `G` supported in `[-1,1]`, write `C_G(t)=∫G(x)G(x+t)dx` and
`J(G)=∬_{[-1,1]²}(G(x)−G(y))²/(2|x−y|)dxdy`. Then

`½∫₀²(C_G(0)−C_G(t))/t dt
 =J(G)/4+∫₀¹G(u)²[log2−½log(1−u²)]du`.

Consequently, for an odd C² unit-window test `F` and `G(u)=F(u/2)`,

`∫₀¹(C_F(0)−C_F(t))/t dt
 =J(G)/4+∫₀¹G(u)²[log2−½log(1−u²)]du`.

For any real odd C¹ `G`, let `M_n=∫_{−1}¹G P_n`, with `P_n` the Legendre polynomial.
No support restriction is needed for the regional inequality

`J(G)≥(137/30)∫_{−1}¹G²−(77/20)M₁²−(63/20)M₃²`.

## Proof

Put `I=∬_{(0,1)²}k_odd(x,y)(G(x)−G(y))²` and
`B=∫₀¹G(x)²[log(x+1)−log x]dx`. The audited reflected-pair identities give
`J=2I+4B` and `4L=4I+8∫₀¹G²K`, where
`K(x)=log2−½log(1−x²)+log(x+1)−log x` and
`L=∫₀²(C_G(0)−C_G(t))/t dt`.

Both parts of `K` are nonnegative on `(0,1)`. Their products with `G²` are
integrable by domination by the already integrable `G²K`. Thus the potential
integral splits exactly. Eliminating `I` and `B` gives the first identity.
Finally `C_G(t)=2C_F(t/2)` and substitution `t=2s` gives the second.

For the moment inequality, remove `P=(3M₁/2)P₁+(7M₃/2)P₃`. Orthogonality gives
zero first and third moments for `G−P`, while oddness kills its even moments.
The fifth harmonic gap gives `J(G−P)≥(137/30)∫(G−P)²`.
The removed mass is `3M₁²/2+7M₃²/2`; its energy, equal to the mixed pairing
of `G` with `P`, is `3M₁²+77M₃²/6`. Expanding the gap gives the stated charges.

## Complete-form assembly

For the unit source `F` and `G(u)=F(u/2)`, the
[primitive reduction](../3-formalized/f1-primitive-variance-reduction.md), the two preceding
identities and oddness give `D(G)≤P(F)+E/64≤Q(F)`, where `D` is exactly the explicit form in
[F1-PV](../1-in-progress/f1-primitive-variance-joint-payment.md).
Indeed `∫₀¹G²=∫F²`, `∫₀¹uG=2∫xF`, and each full regional odd moment is twice
its positive-half integral. Reflection and dilation give
`C_F(log2)=−½∫_{2log2−1}¹G(u)G(2log2−u)du`.
Thus the first-moment coefficient is `77/20+(39/64)/4`, the third is `63/20`,
and the signed prime term has coefficient `log2/√2`. No sign of `D` is used.

## Lean

LST `RegionalLogarithmicExteriorIdentity` and `RegionalLogarithmicLowOddMoments`
pass individual Lean and standard-only transitive axiom audits. WTZ
`TheFirstFoldRetainsTwoMomentCharges` contains the complete-form assembly;
its individual audit remains pending.
These retain the exterior term and the low projections discarded by the vanishing-moment
bound; they do not establish the joint first-fold sign.
