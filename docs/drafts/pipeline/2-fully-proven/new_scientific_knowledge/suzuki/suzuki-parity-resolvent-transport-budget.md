# Suzuki Parity-Resolvent Transport Budget

- **ID:** suzuki-parity-resolvent-transport-budget
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** Suzuki 2026 restricted-Weil parity resolvents; unconditional Xi first-defect bound
- **Statement:** A finite-shift Suzuki excursion above the Xi first defect requires a strict
  accumulated even-over-odd squared-resolvent hazard budget. Exact terminal ratio is
  `(1+kappa_Xi)/(1-kappa_Xi)>81/4`. On the literal infinite parity spectral measures, the hazard
  is exactly normalized lower-even-pair credit minus odd-below-even spectral-inversion debt.
- **Scientific status:** `[PAPER-PROVED] [LEAN-PROVED] [UNCONDITIONAL]`
  `[NOVELTY-BOUNDARY-AUDITED]`

## Goal

Turn the surviving interior-excursion branch from an existential inequality into a spectral
transport target. A claim that the even resolvent eventually dominates the odd one is too vague
and can hide the hard arithmetic. The correct quantity is the cumulative difference between
their squared-resolvent inverse-gap means.

This card proves the exact budget and identifies the literal restricted-Weil input still missing.
It does not prove that the budget is positive for Suzuki's operator, construct the meromorphic
limit, or imply RH.

## Setup

At one aperture let `mu_+` and `mu_-` be the even and odd source spectral measures of `A_a`, with
source vectors `cosh(x)` and `sinh(x)`. For `lambda` below the spectral floor put

```text
E(lambda)=integral (t-lambda)^(-1) dmu_+(t),
O(lambda)=integral (t-lambda)^(-1) dmu_-(t).             (1)
```

Both are positive where both source channels survive. Spectral differentiation gives

```text
E'(lambda)=integral (t-lambda)^(-2) dmu_+(t),
O'(lambda)=integral (t-lambda)^(-2) dmu_-(t).            (2)
```

Define log odds and the parity hazard gap

```text
L(lambda)=log(E(lambda)/O(lambda)),

H(lambda)=E'(lambda)/E(lambda)-O'(lambda)/O(lambda).     (3)
```

The two normalized terms in `H` are resolvent-tilted expectations of the inverse spectral gap
`(t-lambda)^(-1)`. Thus `H>0` says that, at that shift, the even source measure is more
lower-spectrum concentrated than the odd source measure.

## Theorem 1: exact transport identity

On every finite shift interval `[lambda_1,lambda_2]` on which the energies are positive and the
standard differentiation/integrability hypotheses hold,

```text
L'(lambda)=H(lambda),                                    (4)

integral_(lambda_1)^(lambda_2) H(lambda) dlambda
  =L(lambda_2)-L(lambda_1).                              (5)
```

### Proof

Differentiate `log(E/O)`:

```text
d/dlambda log(E/O)=E'/E-O'/O.
```

The fundamental theorem of calculus gives (5). Equation (2) identifies the derivative terms with
the actual squared resolvents; it is not a chosen statistical reweighting.

## Theorem 1b: exact cross-parity spectral-pair carrier

Let `t` denote the even spectral variable and `s` the odd spectral variable. Under the four exact
integrability hypotheses for the first and squared resolvent kernels, Fubini factorization gives

```text
E'(lambda)O(lambda)-E(lambda)O'(lambda)
 =double_integral
    (s-t)/[(t-lambda)^2(s-lambda)^2]
    dmu_+(t)dmu_-(s).                                  (5a)
```

Therefore

```text
H(lambda)
 =1/[E(lambda)O(lambda)] *
   double_integral
    (s-t)/[(t-lambda)^2(s-lambda)^2]
    dmu_+(t)dmu_-(s).                                  (5b)
```

This is the literal infinite-spectrum identity, not a finite spectral approximation.

Split the signed pair kernel into its positive and negative Jordan parts:

```text
C(lambda)
 =double_integral
    ((s-t)/[(t-lambda)^2(s-lambda)^2])_+
    dmu_+(t)dmu_-(s),

D(lambda)
 =double_integral
    ((s-t)/[(t-lambda)^2(s-lambda)^2])_-
    dmu_+(t)dmu_-(s).                                  (5c)
```

For positive parity energies,

```text
H(lambda)=[C(lambda)-D(lambda)]/[E(lambda)O(lambda)],

H(lambda)>0
iff
D(lambda)<C(lambda).                                   (5d)
```

Thus an even level below an odd level contributes transport credit; an odd level below an even
level creates spectral-inversion debt. Arbitrarily many local reversals are allowed. What matters
is the complete weighted product-measure balance.

For finite visible spectra `t_i,s_j` with source weights `a_i,b_j`, (5a) is exactly

```text
sum_i sum_j
 a_i b_j (s_j-t_i)/
 [(t_i-lambda)^2(s_j-lambda)^2].                       (5e)
```

### Proof

Pointwise,

```text
(s-t)/[(t-lambda)^2(s-lambda)^2]
 =1/(t-lambda)^2 * 1/(s-lambda)
  -1/(t-lambda) * 1/(s-lambda)^2.
```

Multiply by source weights and integrate against `mu_+ product mu_-`. Fubini turns the two product
integrals into `E'O` and `EO'`. The positive/negative-part decomposition of an integrable real
kernel proves (5c)--(5d). No ordering of the two spectra is used.

## Theorem 1c: every genuine interior excursion crosses the credit/debt wall

Suppose `lambda_L<lambda_M<lambda_R`, both endpoint angles lie below a target `kappa_*`, and
the middle angle lies above it:

```text
kappa(lambda_L)<kappa_*<kappa(lambda_M),
kappa(lambda_R)<kappa_*.                                (5f)
```

Under the same positivity, continuity, differentiation, and product-integrability hypotheses,
there are ordered points

```text
lambda_L<lambda_up<lambda_max<lambda_down<lambda_R       (5g)
```

such that `kappa(lambda_max)>kappa_*` and

```text
D(lambda_up)<C(lambda_up),
D(lambda_max)=C(lambda_max),
C(lambda_down)<D(lambda_down).                          (5h)
```

### Proof

The defect-angle derivative factors exactly as

```text
kappa'(lambda)
 =2E(lambda)O(lambda)/(E(lambda)+O(lambda))^2 * H(lambda). (5i)
```

The prefactor is strictly positive. The continuous angle attains a global maximum on
`[lambda_L,lambda_R]`; (5f) forces that maximum into the open interval and above `kappa_*`.
Fermat's theorem gives `H(lambda_max)=0`. Applying the mean-value theorem on the intervals from
the left endpoint to `lambda_max` and from `lambda_max` to the right endpoint gives, respectively,
a positive and a negative value of `H`. Equation (5d), together with its zero and negative
counterparts, yields (5h).

This is stronger than saying the integrated budget may tolerate sign changes. When both
endpoints are sub-target, a sign change and an exact credit/debt balance point are necessary.
Every globally one-signed hazard account is therefore impossible for a genuine interior loop.

## Theorem 1d: stationary above-Xi mean/variance wall

Assume in addition that the squared-resolvent responses are differentiable with

```text
E''(lambda)=2E_3(lambda),   O''(lambda)=2O_3(lambda),
E_3(lambda)=integral (t-lambda)^(-3) dmu_+(t),
O_3(lambda)=integral (s-lambda)^(-3) dmu_-(s).           (5j)
```

At the same maximizing point `lambda_max` from Theorem 1c, define the resolvent-tilted
probability laws and inverse-gap observable

```text
dpi_+(t)=dmu_+(t)/[E(lambda_max)(t-lambda_max)],
dpi_-(s)=dmu_-(s)/[O(lambda_max)(s-lambda_max)],
X(u)=1/(u-lambda_max).                                  (5k)
```

Then simultaneously

```text
E(lambda_max)/O(lambda_max)>R_Xi>81/4,
E'(lambda_max)/E(lambda_max)
  =O'(lambda_max)/O(lambda_max),                         (5l)

Var_pi+(X) <= Var_pi-(X).                               (5m)
```

### Proof

The first equality in (5l) is the zero-hazard/credit-debt balance already forced at the
maximum. The second derivative identity at that stationary point is

```text
kappa''(lambda_max)
 =4E O/(E+O)^2 * [Var_pi+(X)-Var_pi-(X)].
```

The prefactor is positive and a twice differentiable local maximum has nonpositive second
derivative, proving (5m). Equation (8) gives the exact ratio threshold in (5l).

Thus the balance point is not arbitrary. It is a high-ratio stationary resolvent wall with equal
tilted inverse-gap means and ordered dispersions. Any source proof of the interior Suzuki branch
must produce this three-moment configuration in the literal restricted-Weil parity measures.

## Theorem 2: unconditional Xi transport cost

Define the exact Xi even/odd threshold

```text
R_Xi=(1+kappa_Xi)/(1-kappa_Xi)>81/4.                      (6)
```

If a finite shift lies above the Xi calibration,

```text
kappa_Xi < (E(lambda_2)-O(lambda_2))
             /(E(lambda_2)+O(lambda_2)),                 (7)
```

then, exactly,

```text
kappa_Xi<kappa(lambda_2)
iff
E(lambda_2)/O(lambda_2)>R_Xi
iff
L(lambda_2)>log R_Xi.                                    (8)
```

In particular,

```text
E(lambda_2)>(81/4)O(lambda_2),
L(lambda_2)>log(81/4).                                   (9)
```

Consequently the exact interior-excursion budget is the equivalence

```text
kappa_Xi<kappa(lambda_2)
iff
integral_(lambda_1)^(lambda_2) H(lambda) dlambda
  > log R_Xi-L(lambda_1).                               (10)
```

### Proof

The exact target inequality is

```text
(1+kappa_Xi)O<(1-kappa_Xi)E.
```

The unconditional `kappa_Xi>77/85` gives

```text
(162/85)O<(8/85)E,
```

hence `R_Xi>81/4` and (9). Strict monotonicity of the logarithm turns the exact ratio inequality
into the exact log-odds inequality. Substitute (5) to obtain (10), in both directions.

## Cofinal free-end form

The far-negative free parity angle is

```text
kappa_free(a)=2a/sinh(2a).
```

Hence its even/odd source ratio is exactly

```text
R_free(a)
 =(1+kappa_free(a))/(1-kappa_free(a))
 =[sinh(2a)+2a]/[sinh(2a)-2a] -> 1.                     (11)
```

Taking `lambda_1` far negative in (10) shows what a cofinal interior proof must create:

```text
integrated even-minus-odd inverse-gap advantage
  > log R_Xi-log R_free(a)
  > log(81/4)-log R_free(a),                             (12)
```

whose exact right side tends to `log R_Xi`, with unconditional lower floor `log(81/4)`, not to
zero. The actual restricted-Weil spectrum must therefore create an order-one parity amplification
from an asymptotically balanced exponential source. This is substantially stronger than
noncollapse.

Equations (5b)--(5d) make (12) source-literal:

```text
integral_(lambda_1)^(lambda_2)
 [C_a(lambda)-D_a(lambda)]/[E_a(lambda)O_a(lambda)] dlambda
 >log R_Xi-L_a(lambda_1).                              (13)
```

Insert the exact `T_a+H_a` and `T_a-H_a` parity spectral measures. The hard arithmetic theorem is
now to show that their integrated lower-even-pair credit beats both the full inversion debt and
the order-one Xi cost. The existing generic positive-resolvent countermodel shows no
operator-positivity argument can supply this.

We call the cofinal source statement consisting of either the ground reflection cone or (13)
`SUZUKI-PARITY-SPECTRAL-TRANSPORT`. This name records the exact surviving source theorem; it is
not a proof of it and is not an additional route.

## Source-horizon provenance gate

The scalar pair budget is a terminal Suzuki consumer unless the pair-measure profile is proved to
come from a predeclared arithmetic source map. Let `E_src(rho)` be the injective mass-one
high-exponent source vector from
`source-horizon-riemann-divisor/main.tex`, and let

```text
T_lambda : source l1 -> F
```

be a bounded linear source-to-parity carrier. If every `T_lambda` is label-blind, the exact
bounded-observer theorem gives

```text
T_lambda E_src(rho)
 =T_lambda E_src(1-conj(rho))                            (14)
```

for every shift. Consequently *every* downstream function of the complete shift profile has the
same value on the reflected pair. This includes nonlinear hazard ratios, Jordan credit/debt
splitting, maximization, and the integrated budget. Therefore any bounded linear carrier whose
downstream Suzuki statistic separates a strict-right source point from its reflection must be
label-sensitive at some shift. A singular, nonclosable, or relation-valued producer is outside
this bounded-map theorem and remains live.

This does not prove that Suzuki's literal restricted-Weil source map factors through the
high-exponent frame, nor does it exclude a genuinely nonlinear source producer. It closes the
theatre loophole: satisfying (13) on freely chosen parity measures is not a source theorem.

`SUZUKI-PARITY-SPECTRAL-TRANSPORT` remains the exact within-carrier admission gate. Full Route G
requires the strengthened conjunction
`SUZUKI-SOURCE-POINTED-PARITY-TRANSPORT`: construct the literal parity carrier from a predeclared
arithmetic source, prove reflection separation before scalarization by a label-sensitive or
singular mechanism, and then prove the ground cone or the exact credit/debt budget.

## Hostile falsification audit

- Pointwise `H>0` is neither necessary nor sufficient by itself; exact integrated magnitude in
  (10) is decisive.
- A positive hazard on a short interval can still be too small. Required mass is logarithmic and
  order one cofinally.
- Ground reflection fidelity and interior hazard are different mechanisms. A pole can supply the
  endpoint without a long finite-shift budget; an interior excursion must pay (10).
- Global source imbalance does not help cofinally: `R_free(a)->1`.
- Monotone-likelihood order between all even and odd spectral nodes would force a hazard sign but
  is far stronger than (10) and is not assumed. In fact it is unavailable globally: a
  two-valued parity response is comonotone only if every visible odd node lies below every visible
  even node. If both visible parity spectra are unbounded above, neither this ordering nor its
  reverse can hold.
- Local inversions do not kill the interior branch. They enter exactly through `D_a`; failure
  occurs only when integrated credit minus debt cannot pay (13).
- Pointwise `C_a>D_a` on an entire interval is sufficient but not necessary. The exact criterion
  is the signed integrated budget (13), so hazard may change sign.
- If both ends of the selected interval are below the Xi wall and its interior is above, hazard
  must change sign: credit dominates on the rise, credit equals debt at an interior maximum, and
  debt dominates on the fall. A globally nonnegative or globally nonpositive hazard cannot
  realize that loop.
- At that same above-Xi balance maximum, the two tilted inverse-gap means are equal while the
  even-channel inverse-gap variance cannot exceed the odd-channel variance. A scalar excursion
  failing this third-resolvent wall is impossible.
- A finite spectral truncation is not evidence for the literal operator. The measure-level theorem
  requires and records the four resolvent integrability hypotheses before using Fubini.
- Replacing Suzuki's literal spectral measures by arbitrary positive measures would replay an
  interface and prove no arithmetic admission.
- Even the literal scalar credit/debt profile is not yet a reflection-oriented source theorem
  unless its construction is shown source-pointed before invariant scalarization. Bounded
  label-blind linear transport cannot be repaired by nonlinear downstream processing.

## Strongest positive conclusion

The interior branch is now a quantitative spectral-transport problem rather than a root-existence
problem. One must prove a cofinal order-one integrated advantage of the even restricted-Weil
source measure over the odd one. Conversely, a uniform upper bound at or below the exact right
side of (12) would kill every interior excursion, leaving only the bottom-pole branch.

The existing global monotone-likelihood producer cannot be imported wholesale: bi-unbounded
source-visible parity spectra rule out both global two-valued likelihood orientations. Any
successful proof must prove the source-literal credit/debt inequality (13), allowing local
reversals while winning the integrated budget.

If both endpoint branches are below Xi, the successful profile has a forced ordered topology:
credit domination, exact balance at an above-Xi maximum, then debt domination. The new balance
point is a sharper attack surface than an arbitrary positive-budget interval: it has ratio
`>R_Xi>81/4`, equal normalized squared-resolvent responses, and ordered third-resolvent
dispersion.

Source-horizon conservation adds an independent provenance obligation. A scalar Suzuki profile
can judge transported orientation, but it cannot create orientation after bounded label-blind
fusion. Full Route G therefore needs source-pointed parity transport, not only a scalar excursion.

The literal position torque now passes the faithful-source half of this obligation. Its coefficient
`Lambda(n)log(n)[sqrt(n)-n^(-3/2)]` is supported on positive prime powers and nonzero at every
prime and every valuation depth. Exact prime-source correspondence makes its analytic carrier
hypertranscendental over complete local-Euler residue--valuation fusion. Therefore the torque is
genuine global source data. The fixed-torque fibre theorem remains decisive: source authenticity
does not upgrade one commutator coordinate into the missing two-moment parity inequality.

## Novelty audit

The logarithmic derivative, Fubini product identity, Jordan decomposition, fundamental theorem of
calculus, resolvent differentiation, and log-transform cumulant/variance identity are classical
and are not claimed as new. General
Laplace/Stieltjes-transform ratio-monotonicity literature contains related kernel arguments.
Candidate new knowledge is restricted to exact Suzuki/Xi calibration: the source selector is
equivalent to accumulated product-measure credit minus spectral-inversion debt with exact threshold
`R_Xi`, unconditional floor `R_Xi>81/4`, cofinal free baseline (11), and the forced ordered
credit--balance--debt reversal for a two-sub-target-endpoint excursion, together with the
equal-mean/ordered-variance law at its same above-Xi maximum. The source-provenance
corollary is an exact composition of the independently proved complete-source label-blindness
theorem with arbitrary downstream processing; its generic functional logic is not claimed as new.
Candidate novelty is its Suzuki/Xi incidence and the sharpened source-pointed transport
specification. Targeted corpus and arXiv searches found general transform-ratio rules and Suzuki's
screw-function operator, but not this restricted-Weil/Xi credit-debt budget. Search absence does
not establish priority; specialist review remains required.

## Lean certificate

Module:

```text
formal/GaloisForLFunctions/RHTower/SuzukiParityResolventTransportBudget.lean
formal/GaloisForLFunctions/RHTower/SuzukiParitySpectralPairTransport.lean
formal/GaloisForLFunctions/RHTower/SuzukiInteriorExcursionSpectralTurningPoint.lean
```

Capstone declarations:

```text
hasDerivAt_suzukiParityResolventLogOdds
intervalIntegral_suzukiParityResolventHazardGap
primeArchSuzukiParityEvenOddThreshold_gt_eightyOne_div_four
primeArchSuzukiParityEnergy_angle_gt_iff_evenOddRatio
primeArchSuzukiParityEnergy_angle_gt_iff_logOdds
primeArchSuzukiParityEnergy_even_gt_eightyOne_div_four_mul_odd
primeArchSuzukiParityEnergy_logOdds_gt_log_eightyOne_div_four
primeArchSuzukiInteriorExcursion_iff_hazardBudget
primeArchSuzukiInteriorExcursion_hazardBudget
suzukiFiniteParityResolvent_crossWronskian_eq_pairSum
suzukiFiniteParityResolvent_hazardGap_eq_pairSum_div
intervalIntegral_suzukiFiniteParityNormalizedCrossGapMass
primeArchSuzukiFiniteParityInteriorExcursion_iff_crossGapBudget
suzukiFiniteParityCrossGapMass_eq_credit_sub_inversionDebt
suzukiFiniteParityResolvent_hazardGap_pos_iff_inversionDebt_lt_credit
not_suzukiParitySpectraComonotone_of_odd_unbounded
not_suzukiParitySpectraAntimonotone_of_even_unbounded
no_global_suzukiParitySpectralMonotoneLikelihood_of_biunbounded
suzukiParitySpectral_crossWronskian_eq_crossGapIntegral
integrable_suzukiParitySpectralCrossGapKernel
suzukiParitySpectral_hazardGap_eq_crossGapMass_div
suzukiParitySpectralCrossGapMass_eq_credit_sub_inversionDebt
suzukiParitySpectral_hazardGap_pos_iff_inversionDebt_lt_credit
suzukiParitySpectral_hazardGap_eq_zero_iff_inversionDebt_eq_credit
suzukiParitySpectral_hazardGap_neg_iff_credit_lt_inversionDebt
exists_rise_peak_fall_of_strict_interior_excursion
suzukiSecondDeriv_nonpos_of_isLocalMax
suzukiDefectAngleTiltVelocity_eq_hazardFactor
hasDerivAt_suzukiShiftResolventKernel_sq
hasDerivAt_integral_weighted_suzukiShiftResolventKernel_sq
suzukiParityCubedSpectralEnergy
suzukiParityTiltedInverseGapVariance
hasDerivAt_suzukiDefectAngleTiltVelocity_of_balance
suzukiStationaryAngleAcceleration_eq_tiltedVarianceDifference
suzukiParitySpectral_interiorExcursion_forces_creditBalanceDebt
suzukiLabelBlindParityCarrier_reflectionProfiles_eq
suzukiLabelBlindParityCarrier_postprocessing_reflectionBlind
suzukiReflectionSeparatingPostprocessing_forces_labelSensitive
```

The squared-resolvent derivative connector used in (2) is already formal as
`hasDerivAt_integral_weighted_suzukiShiftResolventKernel` in
`SuzukiShiftSpectralMonotoneRatio.lean`.

All new theorems are unconditional. No `axiom`, `sorry`, `admit`, `opaque`, `unsafe`, or
computation occurs.

## Log

- 2026-08-01 — exact parity log-odds transport and unconditional Xi hazard budget proved on paper
  and formalized; interior selector reduced to a cofinal order-one restricted-Weil spectral
  advantage. Literal infinite-spectrum Fubini carrier and exact lower-pair-credit versus
  inversion-debt law then proved and formalized.
