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
- A finite spectral truncation is not evidence for the literal operator. The measure-level theorem
  requires and records the four resolvent integrability hypotheses before using Fubini.
- Replacing Suzuki's literal spectral measures by arbitrary positive measures would replay an
  interface and prove no arithmetic admission.

## Strongest positive conclusion

The interior branch is now a quantitative spectral-transport problem rather than a root-existence
problem. One must prove a cofinal order-one integrated advantage of the even restricted-Weil
source measure over the odd one. Conversely, a uniform upper bound at or below the exact right
side of (12) would kill every interior excursion, leaving only the bottom-pole branch.

The existing global monotone-likelihood producer cannot be imported wholesale: bi-unbounded
source-visible parity spectra rule out both global two-valued likelihood orientations. Any
successful proof must prove the source-literal credit/debt inequality (13), allowing local
reversals while winning the integrated budget.

## Novelty audit

The logarithmic derivative, Fubini product identity, Jordan decomposition, fundamental theorem of
calculus, and resolvent differentiation are classical and are not claimed as new. General
Laplace/Stieltjes-transform ratio-monotonicity literature contains related kernel arguments.
Candidate new knowledge is restricted to exact Suzuki/Xi calibration: the source selector is
equivalent to accumulated product-measure credit minus spectral-inversion debt with exact threshold
`R_Xi`, unconditional floor `R_Xi>81/4`, and cofinal free baseline (11). Targeted corpus and arXiv
searches found general transform-ratio rules and Suzuki's screw-function operator, but not this
restricted-Weil/Xi credit-debt budget. Search absence does not establish priority; specialist
review remains required.

## Lean certificate

Module:

```text
formal/GaloisForLFunctions/RHTower/SuzukiParityResolventTransportBudget.lean
formal/GaloisForLFunctions/RHTower/SuzukiParitySpectralPairTransport.lean
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
