# Exact remainder of the retained Gamma comparison

- **ID:** F1-GE
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** [Joint first-fold payment](../1-in-progress/f1-joint-cubic-prime-payment.md)
- **Statement:** For every real odd C² function supported in `[-1/2,1/2]`,
  `Q(F)=P(F)+∫₀¹r(t)(E−C(t))dt+2δE`.

Here `P=retainedOddGammaLowerForm`, `E=∫F²`, `C(t)=∫F(x)F(x+t)dx`,
`r(t)=e^(t/2)/sinh t−1/t−1/2+t/24+t²/16`, and
`δ=archLevyAntideriv(1)−log2−π/4+1/4−1/96`.

## Proof

Split the exact Gamma jump integral at `t=1`. Its exterior part is
`2 archLevyAntideriv(1)E`, since `C(t)=0` for `t>1`.
On `(0,1]`, substitute
`e^(t/2)/sinh t=1/t+1/2−t/24−t²/16+r(t)`.
Oddness gives `∫₀¹(E−C)=E`; the exact second lag identity gives
`∫₀¹t²(E−C)=E/3+(∫xF)²`.
The Gamma constant then leaves `2δE` beyond `P`.
Only prime two acts on this window, and the even pole vanishes by oddness;
the remaining prime and sinh terms agree exactly with those in `P`.
All summands are integrable: the original Gamma integrand and logarithmic
jump term are integrable, and the polynomial lag terms are continuous.

## Lean status

WTZ `TheGammaRemainderHasAnExactEnergyIdentity` proves
`weilQuad_eq_retainedOddGamma_add_remainder` and
`retainedGammaRemainder_integrable_nonneg`.

The individual `lake --old env lean` source check passes. Both declarations
have only `propext`, `Classical.choice`, and `Quot.sound` as transitive axioms.
The identity alone supplies no new sign for `P` or `Q`.
