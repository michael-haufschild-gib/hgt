# Gamma remainder and joint first-fold floor

- **ID:** F1-GR
- **Stage:** 3-formalized
- **Type:** THEOREM; individually Lean-audited
- **Source:** [Joint first-fold payment](../1-in-progress/f1-joint-cubic-prime-payment.md)
- **Statement:** For every real odd C² unit-window test, the complete form satisfies
  `Q(F)≥P(F)+E/64`.
  Here `E=∫F²` and `P` is the source card's exact retained Gamma/prime/pole form.
  Some such test has `P(F)<0<Q(F)`.

## Proof

The exact omitted terms are `∫₀¹r(t)(E−C(t))dt+2δE`, with nonnegative first term and
`δ=Ω(1)−log2−π/4+1/4−1/96`. The positive Laplace expansion gives

`Ω(1)≥2[z+z⁵/5+z⁹/9]`, `z=e^(−1/2)>20/33`.

Indeed `ω(t)=Σₖ≥₀e^{−(2k+1/2)t}` has positive terms. Integrating its first three terms
on `(1,∞)` gives the displayed bound. From `e<2.7182818286<(33/20)²` follows
`z>20/33`. The rational inequality

`693147181/10⁹+(31416/10⁴)/4−1/4+1/96+1/128
 <2[20/33+(20/33)⁵/5+(20/33)⁹/9]`

and the proved upper bounds on `log2` and `π` give `δ>1/128`.
The nonnegative lag deficit and kernel remainder then give `Q−P≥2δE≥E/64`.
All integrals exist by compact C² regularity; the three retained modes are integrable
exponentials. Prime and pole terms cancel exactly in this comparison.

## Repair of the quintic direction

For `F(x)=2x(1−4x²)(1−2x²)` on the unit window, the exact lag data from the
[retained-form obstruction](../5-failed/f1-quintic-retained-gamma-obstruction.md) give
`−E/64<P(F)<0`. For the new lower bound, put `l=693147180/10⁹`, `h=693147181/10⁹`.
Replacing positive powers in its correlation polynomial by their values at `h`, and
negative powers by their values at `l`, gives a negative rational upper bound `c₊`.
The prime gain is at least `−2(49/100)c₊`.

The source has the sign of `x`; `|2sinh(x/2)|≤|x|cosh(1/4)` and `cosh(1/4)²≤16/15`
give `½(sinhPairing F)²≤(8/15)(11/210)²`. Also
`γ+logπ+log2≤577216/10⁶+1098613/10⁶+31416/30000−1+h`, using
`logπ≤log3+π/3−1`. Substitution in the exact lag formula gives `P(F)+E/64>0`
by rational arithmetic. This rational certificate is kernel-checked.

The support-preserving smooth approximants already converge in `P` and in mass.
Their eventual signs are therefore `P(Fₙ)<0<P(Fₙ)+Eₙ/64≤Q(Fₙ)`.
Thus the discarded Gamma remainder repairs the same negative retained direction.

**Lean:** `TheGammaComparisonRetainsItsLagMoments` retains the exact exterior tail;
its individual source and transitive-axiom audit passes with standard axioms only.
`TheGammaRemainderPaysAUniformReserve` proves `gamma_tail_one_reserve`,
`weilQuad_ge_retainedOddGamma_add_reserve`, and
`retainedOddGammaLowerForm_quintic_add_reserve_pos`. Its individual source audit passes,
with `[propext, Classical.choice, Quot.sound]` only; it is umbrella-imported.
`TheGammaRemainderCannotBeDiscarded` proves
`exists_odd_unit_retainedGamma_neg_weil_pos`, including the simultaneous C² signs.
All three individual `lake --old env lean` source audits pass with
`[propext, Classical.choice, Quot.sound]` only. All modules are umbrella-imported.

## Remaining sign

The sufficient floor `P≥−E/64` is [refuted by a smooth quadratic-cutoff approximation](../5-failed/f1-primitive-variance-joint-payment.md).
The complete form retains the exact local Gamma remainder and the exterior reserve beyond
`E/64`; their joint payment remains open. The earlier quintic repair above remains valid.
The [higher-lag reserve](f1-higher-gamma-reserve.md) proves stronger universal bounds
and repairs that same smooth quadratic-cutoff direction: `P+E/64<0<Q`.
