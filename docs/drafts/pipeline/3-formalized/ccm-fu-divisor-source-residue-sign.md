# CCM-FU: positivity of the literal residue scalar

- **Stage:** 3-formalized; all three leaves passed scratch and exact-file checks, and all nine public theorems passed their axiom audits. Lake packaging audit remains pending.
- **Parent:** [physical signed dilation mean](ccm-fu-fixed-core-physical-dilation-mean.md).
- **Target:** Prove the real scalar B(-1/2)>0 for the actual source B=-zeta'-zeta^2+2*gamma*zeta. No numerical experiment or pointwise head asymptotic is used.

## Exact positive statement

The literal complex source at -1/2 is real, and

`B(-1/2) > 1/(272*pi) > 0`.

Lean also proves that the fixed-core physical limit has sign
(-1)^(card(P)+1), and that W_P(Y) has this strict sign for all sufficiently
large Y, for every nonempty finite prime core. The [discrete-to-physical
identity](ccm-fu-discrete-physical-prime-release.md) transfers this to actual
distant-prime release coefficients. Uniform renewable reserve still
requires control through changing cores and cutoffs.

## Reflection of the actual source

Put Z=zeta(3/2), D=-zeta'(3/2) and

`c=log(8*pi)-gamma-2-pi/2`.

Both Z and D are real: their absolutely convergent series are
sum_(n>=1) n^(-3/2) and sum_(n>=1) log(n)*n^(-3/2).
The corpus's exact functional equation is zeta(s)=chi(s)*zeta(1-s),
with chi(s)=Gamma_R(1-s)/Gamma_R(s). The Gamma_R recurrence gives

`chi(-1/2)=-1/(4*pi)`.

Indeed Gamma_R(3/2)=Gamma_R(-1/2)*(-1/2)/(2*pi), and the denominator
is nonzero because -1/2 is not a Gamma_R pole. The proved logarithmic
derivative identity gives

`chi'/chi(-1/2)=log(pi)-(psi(-1/4)+psi(3/4))/2`.

Duplication and reflection give psi(3/4)=-gamma-3*log(2)+pi/2.
Recurrence gives psi(-1/4)=psi(3/4)+4. Therefore

`chi'/chi(-1/2)=log(8*pi)+gamma-2-pi/2`.

All functions are holomorphic near the two points in use, so differentiating
the exact functional equation yields zeta'(-1/2)=chi(-1/2)*(q*Z+D),
where q is this logarithmic derivative. Substituting in the literal B gives

`B(-1/2)=(D+c*Z-Z^2/(4*pi))/(4*pi)`.

This also proves its reality. No inverse zeta estimate enters this identity.

## Analytic lower bound for D

Set f(x)=log(x)*x^(-3/2) for x>=2. Since log(2)>2/3,

`f'(x)=x^(-5/2)*(1-(3/2)*log(x))<0`.

Thus f is positive and decreasing there. Comparing each unit interval
with its left endpoint, then taking the convergent positive tail, gives

`D >= integral_2^infinity f(x) dx = (2*log(2)+4)/sqrt(2)`.

The integral follows from the antiderivative
-(2*log(x)+4)/sqrt(x), whose limit at infinity is zero.
Since log(2)>2/3 and sqrt(2)<17/12 (squaring gives 288<289),

`D > (16/3)/(17/12) = 64/17`.

This is a monotone integral comparison of the full source series, not
a numerical truncation certificate.

## Remaining scalar bounds and conclusion

The corpus's absolute zeta bound gives 0<Z<=3. Existing bounds give
3<pi<63/20 and gamma<29/50. Existing exact logarithm bounds imply
log(2)>69/100 and log(3)>109/100. Hence

`log(8*pi)>log(24)=3*log(2)+log(3)>79/25`,

and therefore

`c > 79/25-29/50-2-63/40 = -199/200 > -1`.

Using Z>0, Z<=3 and pi>3,

`D+c*Z-Z^2/(4*pi) > 64/17-3-3/4 = 1/68`.

Division by 4*pi proves the asserted strict bound. Every inequality is
analytic or rational; there is no experimental input.

## Corpus dependencies

- `ZetaCarrier.zeta_eq_zetaChi_mul`, `zetaChi_analyticAt` and mathlib `Complex.Gammaℝ_add_two` supply the reflection and value.
- `SmoothAFEZetaChiShiftDerivative.logDeriv_zetaChi_off_poles` and `SeamDivisionSourceSplit` supply the logarithmic derivative and quarter digamma identities.
- `ZetaFisherVariance` supplies reality, absolute logarithmic-series summability and the actual zeta derivative identity.
- Mathlib `AntitoneOn.integral_le_tsum_comp_add` supplies the full monotone comparison. The specific antiderivative and its decay are proved in the new logarithmic-moment leaf.
- `RiemannXiSuzukiPointwiseFirstTailBarrier.eulerMascheroniConstant_lt_29_over_50`, `Real.pi_gt_three`, `Real.pi_lt_d2`, `Real.log_two_gt_d9` and `Real.log_three_gt_d9` supply the scalar bounds.

## Lean implementation and validation

- `ZetaThreeHalvesLogMoment.lean`: `eulerLogMass_three_halves_gt` proves D>64/17, including full series summability, the monotone integral comparison, exact antiderivative and vanishing endpoint.
- `DivisorSourceNegativeHalfReflection.lean`: `zetaChi_negative_half`, `logDeriv_zetaChi_negative_half` and `divisorSourceEntire_negative_half_eq` identify the exact factor, derivative and real reflected source.
- `DivisorSourceResidueOrientation.lean`: `divisorSourceEntire_negative_half_lower`, `divisorSourceEntire_negative_half_pos` and `divisorSourceEntire_negative_half_im` prove the strict scalar margin and reality. `divisorCoreMellinPairResidue_oriented_pos` and `eventually_mobiusDivisorDilationMean_oriented_pos` transfer it to the actual residue and signed physical average.

All three leaves passed foreground scratch and exact-file checks with
`lake env lean`; their leaf oleans were emitted. All nine public theorems
were audited once in an external scratch file. Every closure uses only
propext, Classical.choice and Quot.sound. The imports are wired into
RHTower without an umbrella build. No old theorem was re-audited, and
only one missing small prerequisite olean was emitted. Lake packaging
audit remains pending because of its known broad stale prerequisite
rebuild. Global formal lint passed and the declaration index was refreshed.
No numerical experiment or computed proof premise was used.

## Remaining arithmetic content

The source sign and discrete correlation identity are closed. Control
as the processed core and cutoff change remains open. The positive
odd-core and negative even-core signs must be retained in any renewal
construction; a universal positive release is not asserted. Thresholds
are presently allowed to depend on the fixed core. RH remains unproved.
