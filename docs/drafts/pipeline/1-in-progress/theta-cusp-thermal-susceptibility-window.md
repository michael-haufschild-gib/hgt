# Theta-cusp thermal susceptibility window

- **ID:** theta-cusp-thermal-susceptibility-window
- **Stage:** 1-in-progress
- **Type:** `[BRIDGE] [FORMALIZATION SOURCE] [OPEN ANALYTIC CORE]`
- **Physics source:** equilibrium fluctuation--response, Kubo susceptibility,
  Born--Witten ground-state scores, monotone-likelihood-ratio order, and Brascamp--Lieb variance
  inequalities for Gibbs measures
- **Statement:** The two live theta-cusp raw moment-ratio hypotheses are exactly a lower and an
  upper bound on the normalized variance of the energy coordinate in two adjacent size-biased
  theta states.

## Exact value relation

Let

```text
m_j = thetaCuspRawEvenMoment(j).
```

For each `k`, normalize the shifted moment sequence `m_(k+n)` and define

```text
mu_k  = m_(k+1)/m_k,
chi_k = m_(k+2)/m_k - (m_(k+1)/m_k)^2.
```

If `m_j` is represented by the positive theta-cusp measure in the variable `y=x^2`, these are the
mean and variance of `y` in the size-biased state

```text
dP_k(y) = y^k dP(y) / m_k.
```

Equivalently, `chi_k` is the zero-field static susceptibility for a field coupled linearly to
`y`.  The two existing source gates become exactly

```text
ThetaCuspUpperAdjacentRatioSeparation
  <-> 5 * mu_1^2 <= 9 * chi_1,                              (1)

ThetaCuspRelaxedFourthMomentConcentration
  <-> 16 * chi_0 <= 29 * mu_0^2.                           (2)
```

Thus the unresolved low block is a two-sided coefficient-of-variation window:

```text
chi_1 / mu_1^2 >= 5/9,
chi_0 / mu_0^2 <= 29/16.
```

The theta means are strictly positive, so the quotient window is now also a proved Lean interface.

## Pearson/Fisher information normalization

The next size-biased state satisfies

```text
dP_(k+1) / dP_k = y / mu_k.
```

Therefore its Pearson chi-square divergence from `P_k` is exactly

```text
D_k = chi^2(P_(k+1) || P_k)
    = E_k[(y / mu_k - 1)^2]
    = chi_k / mu_k^2.                                      (3)
```

The same dimensionless value has two further exact forms:

```text
1 + D_k
  = (m_(k+2) / m_(k+1)) / (m_(k+1) / m_k),                (4)

D_k = QFI_k(y) / (4 * mu_k^2).                             (5)
```

Equation `(4)` identifies Pearson information with the multiplicative discrete curvature of the
adjacent moment-ratio sequence.  Equation `(5)` identifies it with pure-state quantum Fisher
information per squared signal.  The complete low block is consequently

```text
5/9 <= D_1,
D_0 <= 29/16.                                              (6)
```

This is not a new analytic assumption: `(6)`, the susceptibility window, and the former raw ratio
split are proved equivalent.  Its utility is that any information-contraction, escort-state, or
quantum-metrology estimate can now feed the existing consumers without a bespoke moment rewrite.

## Size-bias mean-lift linearization

The standard size-bias waiting-time identity becomes, in the current moment notation,

```text
chi_k = mu_k * (mu_(k+1) - mu_k),                         (7)
D_k   = (mu_(k+1) - mu_k) / mu_k,                         (8)
QFI_k = 4 * mu_k * (mu_(k+1) - mu_k).                    (9)
```

The Hammersley--Chapman--Robbins chi-square inequality is saturated by this pair and the statistic
`y`:

```text
(mu_(k+1) - mu_k)^2 = chi_k * D_k.                       (10)
```

This is a useful route retirement.  A generic chi-square change-of-measure bound cannot sharpen
either theta gate: it reproduces an equality.  Any gain must bound the source-specific mean lift
or introduce a genuinely contracting source channel.

Because every theta `mu_k` is strictly positive, the two quadratic susceptibility gates are
equivalent to the linear normalized-mean window

```text
14 * mu_1 <= 9 * mu_2,
16 * mu_1 <= 45 * mu_0.
```

This is the smallest theorem surface found in this pass: the low block depends only on three
successive size-biased means.  It is directly equivalent to the Pearson, susceptibility, and raw
ratio formulations and has its own linear-Hankel and degree-two-tail/RH consumers.

## Robertson--Price response hierarchy

One size-bias step is also a selection/reweighting step.  For every power observable `y^n`, let

```text
M_(k,n) = E_k[y^n],
C_(k,n) = Cov_k(y,y^n).
```

The Robertson--Price covariance identity gives the exact static value relation

```text
C_(k,n) = mu_k * (M_(k+1,n) - M_(k,n))

M_(k+1,n) - M_(k,n) = C_(k,n) / mu_k.                    (11)
```

In moment coordinates,

```text
s_k^2 * C_(k,n)
  = s_k*s_(k+n+1) - s_(k+1)*s_(k+n).                    (12)
```

Thus response positivity is exactly a separated `2 x 2` Hankel minor, not a new probabilistic
hypothesis.  The existing all-order theta ratio monotonicity proves every minor in `(12)`
nonnegative.  Consequently Lean now proves, unconditionally,

```text
M_(k,n) <= M_(k+1,n)    for every k,n.
```

The case `n=1` is the previous susceptibility/mean-lift law.  The extension is useful because
future source estimates may be stated as monotonicity of any power observable and immediately
transported back to a cross-Hankel inequality.  It does not supply either quantitative constant
in `(6)`: it proves the zero-threshold response sign, while the lower gate needs the strict
`5/9` margin.

## Exact atom-mixture decomposition

The full theta moment state is a mixture of the dominant first atom and the complete higher-atom
tail.  For either bias level `k`, let

```text
w_1 = firstAtomMoment(k) / fullMoment(k),
w_H = higherAtomMoment(k) / fullMoment(k),
mu_1, chi_1atom = mean and susceptibility inside the first atom,
mu_H, chi_H     = mean and susceptibility inside the higher tail.
```

The law of total variance gives the exact identity

```text
chi_k = w_1 * chi_1atom + w_H * chi_H
      + w_1 * w_H * (mu_1 - mu_H)^2.                      (13)
```

All component masses are proved strictly positive in the source, so `(13)` is unconditional.  It
exposes the limitation of first-atom domination precisely:

- a lower susceptibility proof may exploit the nonnegative between-atom fluctuation;
- an upper susceptibility proof must control both the higher-tail variance and the mean mismatch,
  not merely bound each raw moment independently.

This gives a sharper route than the uniform `3005/2997` moment envelope: estimate the two explicit
tail costs in `(13)` instead of paying the same worst-case factor at every moment order.

The same split is now polarized for every Price-response covariance:

```text
C_(k,n) = w_1 * C_(1;k,n) + w_H * C_(H;k,n)
          + w_1*w_H*(mu_1 - mu_H)*(M_(1;k,n) - M_(H;k,n)). (14)
```

Unlike `(13)`, the between-atom term in `(14)` is not automatically a square.  It identifies the
exact missing datum for strengthening a higher-power response: the first atom and the tail must
order their ordinary means and their `n`-th power means in the same direction.  This is a direct
application of the new general law of total covariance in `HTGeometry`; no theta-specific
mixture algebra remains to be repeated.

## Born--Witten likelihood-ratio order

The exact source equation now supplies the missing pointwise ordering datum in `(14)`.  Write

```text
f_n(x) = thetaCuspSourceTerm(x,n),
B_n(x) = thetaCuspBornWittenSuperpotential(n,x).
```

For every positive index and `x > 0`, the existing Witten ground-state equation gives

```text
f_n'(x) = -2*B_n(x)*f_n(x).                               (MLR-1)
```

The explicit Morse coordinate gives the exact index-difference factorization

```text
B_n(x) - B_m(x)
  = (t_n(x)-t_m(x))
      * (1 + (3/2)/(q_n(x)*q_m(x))),                      (MLR-2)

t_n(x) = pi*(n*exp(x))^2,
q_n(x) = t_n(x)-3/2.
```

Every factor after `t_n-t_m` is positive.  Hence `B_m <= B_n` when `m <= n`, strictly when
`m < n`.  Combining `(MLR-1)` and `(MLR-2)` proves

```text
d/dx (f_n/f_1)
  = -2*(B_n-B_1)*(f_n/f_1) <= 0,                          (MLR-3)
```

with strict inequality for `n > 1`.  Positive summation preserves the order, so

```text
R_H(x) = (thetaCuspFullSource(x)-f_1(x))/f_1(x)
```

is antitone on `(0,infinity)`.  The formalized division-free consequence is

```text
(full(y)-f_1(y))*f_1(x) <= (full(x)-f_1(x))*f_1(y),
0 < x <= y.                                               (MLR-4)
```

For every increasing observable `g`, `(MLR-4)` makes the two-sample kernel

```text
(g(y)-g(x))
  * ((full(x)-f_1(x))*f_1(y) - (full(y)-f_1(y))*f_1(x))
```

nonnegative.  This applies directly to `g(x)=x^(2j)`: after the standard product-integral
symmetrization it orders every normalized higher-tail power expectation below the corresponding
first-atom expectation.  That is precisely the common-sign input for the between-atom factor in
`(14)`.  Both the general product-integral transport and its theta application are now written in
Lean source.  Consequently the between-atom term in `(14)` is nonnegative for every bias level and
every power, and the full covariance dominates the two weighted within-component covariances.

The atom family also has the exact translation law

```text
f_1(x+log n) = exp(log(n)/2)*f_n(x).                       (MLR-5)
```

Thus the same result can be read as a residual-life/aging order for translated first-atom
profiles.  No generic stochastic-order axiom is assumed: `(MLR-3)`--`(MLR-5)` are derived from
the existing theta source and Born--Witten formulas.

## Likelihood-ordered single-loss transfer `[PROVED ON PAPER]`

The likelihood-ratio order also sharpens both first-atom-to-full-source transfers. Write

```text
m_j=a_j+r_j,
c=3005/2997.
```

The formal cross-moment theorem gives

```text
r_(k+n)*a_k<=a_(k+n)*r_k,
```

so the relative tail weights `r_j/a_j` decrease with `j`. Combining this order with the existing
uniform bound `r_j<=(c-1)*a_j` proves on paper

```text
14*c*a_2^2<=9*a_1*a_3   -> 14*m_2^2<=9*m_1*m_3,
16*c*a_0*a_2<=45*a_1^2 -> 16*m_0*m_2<=45*m_1^2.          (MLR-6)
```

The currently formalized coordinatewise transfer pays `c^2` in both premises. Equation
`(MLR-6)` shows that only one factor is real: the ordered tail cannot independently inflate both
members of either moment ratio. This strictly weakens both remaining finite certificates and
replaces the Rayleigh--Ritz buffer `14*c^2-9` by `14*c-9` once formalized.

The complete proof is in
`../2-fully-proven/not_new_scientific_knowledge/theta-cusp-likelihood-ordered-tail-single-loss-transfer.md`.

## Anomalous boundary-equipartition recurrence

Let

```text
L_(k,n) = integral_(0,infinity) x^k b_n(x) dx,
T_(k,n) = integral_(0,infinity) x^k t_n(x) b_n(x) dx,
t_n(x)   = pi*n^2*exp(2x),
b_n'(x)  = (5/2 - 2*t_n(x))*b_n(x).
```

The half-line boundary current survives at power zero and vanishes at every positive power.  The
new source-level formalization records both cases exactly:

```text
2*T_(0,n) = b_n(0) + (5/2)*L_(0,n),                      (15)
2*T_(k,n) = k*L_(k-1,n) + (5/2)*L_(k,n),   k > 0.       (16)
```

For the first atom, `b_1(0)=exp(-pi)`.  Equation `(15)` therefore places the only non-moment scalar
in the rational enclosure package and the zeroth Gibbs moment in one exact source-energy value.
This is the endpoint anomaly predicted by the half-line quantum bootstrap, not a boundary term
that may be silently discarded.

On `x >= 0`, the source-defined Morse coordinate obeys

```text
t_n(x) >= pi*n^2*(1 + 2x).
```

Combining this affine tangent with `(16)` removes the inserted energy and gives the unconditional
moment recurrence

```text
4*pi*n^2*L_(k+1,n)
  + (2*pi*n^2 - 5/2)*L_(k,n) <= k*L_(k-1,n).             (17)
```

Since `n >= 1`, `pi > 3`, and every Gibbs moment is nonnegative, the same formal source derives the
rational-coefficient consequence

```text
12*L_(k+1,n) <= k*L_(k-1,n).                             (18)
```

Equations `(15)`--`(18)` apply to every positive theta atom, with direct first-atom specializations.
They constrain the exact `L_0,...,L_8` variables consumed by the open single-Gibbs certificate:
future enclosure proofs need not treat upper successor moments as an unconstrained collection of
boxes.  The coarse rational bound `(18)` does not by itself imply the very tight decimal boxes in
the current rational-enclosure gate, so no enclosure or RH hypothesis is claimed discharged.  Its
value is a source-proved recursive constraint and a consistency/propagation rule; `(17)` retains
the sharper `pi`-dependent middle-moment subtraction for an analytic enclosure proof.

## Why this strengthens the corpus

- It replaces four raw-moment products with two normalized fluctuation values.
- The existing Liouville Ward, Morse--Fisher, Born--Witten, and single-Gibbs modules can now target
  the same scalar kind of object: a variance under a positive state.
- The upper bound `(2)` is in the natural output form of Poincare/Brascamp--Lieb estimates.
- The lower bound `(1)` makes clear that ordinary log-convexity is insufficient: it gives only
  `chi_1 >= 0`, whereas the corpus needs the quantitative reverse-fluctuation margin
  `9 chi_1 >= 5 mu_1^2`.
- The packaged susceptibility window directly supplies every real linear-polynomial
  prime--Gamma Hankel test and, together with the existing degree-two tail, directly implies RH.
- The existing two-channel Stein--Robertson/Rayleigh--Ritz certificate now has an exact
  fluctuation consumer: it supplies the lower half `9 chi_1 >= 5 mu_1^2`.  In this coordinate the
  low-block physics is no longer two opaque ratio hypotheses: the two-channel uncertainty route
  owns the lower fluctuation bound, while the genuinely separate open input is the `k=0` upper
  bound `16 chi_0 <= 29 mu_0^2`.
- The atom split now consumes the general mixture API directly.  The full-source error is an exact
  within-tail variance plus one between-means square, rather than an undifferentiated momentwise
  domination loss.
- The Pearson normalization removes scale completely and exposes the exact adjacent size-bias
  divergence, the moment-ratio curvature `(4)`, and the quantum Fisher signal ratio `(5)`.
- The waiting-time/length-bias identity `(7)` linearizes both low-block conditions.  Producers may
  now control three successive normalized means instead of two variance inequalities or four raw
  moment products.
- The existing all-order completed theta moment log-convexity theorem now directly discharges
  `D_k >= 0` for every `k`.  This confirms the information interpretation throughout the current
  moment tower, while also locating the unresolved lower gate precisely at the quantitative jump
  from `0` to `5/9` at `k=1`.
- The same theorem now discharges every separated cross-Hankel sign through the Price identity,
  proving monotonicity of all power expectations under successive size bias rather than only the
  first moment.
- The total-covariance identity extends the exact atom split from susceptibility to every power
  response and exposes the signed between-atom ordering term explicitly.
- The Born--Witten score comparison now supplies a division-free, nonnegative ordering kernel for
  that signed term.  The general HTGeometry product-integral theorem transports it to every
  size-biased power expectation and discharges the between-component sign in the existing theta
  total-covariance identity.
- The half-line equipartition recurrence constrains all first-atom log-Gamma moments used by the
  rational enclosure and makes the `exp(-pi)` endpoint charge explicit at power zero.

This is useful even if the analytic route fails: any candidate physics estimate can now be
rejected immediately if it controls only one direction or proves only nonnegative variance.

## Cross-corpus application audit

- `XiCTaylorThetaTailMomentLogConvex.lean` already proves all-order strict moment positivity and
  adjacent log-convexity.  The new general Pearson/Hankel equivalence consumes those declarations
  directly and proves `thetaCuspSizeBiasPearsonChiSq_nonneg k` for every `k`; no new analytic
  premise is introduced.
- The coupled Sonin projective/Feshbach module already consumes the general normalized variance
  and QFI identities.  The size-bias/Pearson specialization is deliberately not asserted there:
  the current Sonin corpus proves positive zeroth mass at nondegenerate apertures, but not strict
  positivity of every consecutive trace moment needed for a probability likelihood ratio.
  Treating possibly signed odd trace moments as size-biased states would be invalid.
- The mean-lift and QFI laws remain general HTGeometry theorems and can be reused by any future
  positive moment representation without theta- or zeta-specific imports.
- The Price identity itself is algebraic and therefore available to a future positive coupled
  Sonin moment representation.  No Sonin response-sign theorem is asserted yet: the current
  source needs strict positivity of the relevant trace masses and a separated ratio comparison
  before division by the selecting mean is justified.
- The boundary-equipartition recurrence is theta-source-specific and is therefore not exported to
  the Sonin route.  The reusable cross-corpus part is the general total-covariance mixture law;
  applying it to Sonin still requires the already-missing positive component masses.
- The likelihood-ratio proof is also theta-source-specific, but its criterion is reusable without
  zeta: a positive component family whose exact logarithmic scores are ordered has ordered density
  ratios and therefore a signed total-covariance kernel.  The integration step is now a generic
  HTGeometry theorem; another hypertranscendental source needs only supply its component
  integrability and kernel sign.

## Formalization

General, non-zeta-specific infrastructure is in
`formal/GaloisForLFunctions/HTGeometry/NormalizedMomentQuantumVariance.lean`:

```text
momentSizeBiasedSequence,
momentNormalizedExpectation_X_sizeBiased,
momentNormalizedVariance_X_sizeBiased,
sq_mass_mul_momentNormalizedVariance_X_sizeBiased,
momentSizeBiasPearsonChiSq,
sq_next_mul_momentSizeBiasPearsonChiSq,
momentSizeBiasPearsonChiSq_nonneg_iff_adjacentHankel,
momentSizeBiasPearsonChiSq_add_one_eq_adjacentRatioQuotient,
momentNormalizedVariance_X_sizeBiased_eq_mean_mul_next_sub_mean,
momentSizeBiasPearsonChiSq_eq_relativeMeanLift,
pureStateQuantumFisherValue_sizeBiased_X_eq_meanLift,
momentSizeBiasPearsonChiSq_hcr_saturation,
momentSizeBiasPearsonChiSq_eq_quantumFisher_signalRatio,
momentNormalizedCovariance,
momentNormalizedCovariance_self,
momentNormalizedCovariance_comm,
momentNormalizedExpectation_X_pow_sizeBiased,
momentNormalizedCovariance_X_X_pow_sizeBiased,
sq_mass_mul_momentNormalizedCovariance_X_X_pow_sizeBiased,
momentNormalizedCovariance_X_X_pow_sizeBiased_nonneg_iff_crossHankel,
momentNormalizedCovariance_X_X_pow_sizeBiased_eq_mean_mul_response,
momentSizeBiasPriceEquation_X_pow,
momentNormalizedCovariance_sequenceSum,
momentNormalizedVariance_sequenceSum,
weighted_left_variance_le_sequenceSum.
```

The general, non-zeta-specific likelihood-kernel integration theorem is in
`formal/GaloisForLFunctions/HTGeometry/MonotoneLikelihoodRatio.lean`:

```text
integral_mul_integral_le_of_monotoneLikelihoodKernel.
```

The direct theta and RH consumers are in
`formal/GaloisForLFunctions/RHTower/PrimeArchThetaThermalSusceptibility.lean`:

```text
thetaCuspUpperAdjacentRatioSeparation_iff_susceptibility_lower,
thetaCuspRelaxedFourthMomentConcentration_iff_susceptibility_upper,
thetaCuspSizeBiasedSusceptibilityWindow_iff_ratioSplit,
thetaCuspSizeBiasPearsonWindow_iff_susceptibilityWindow,
thetaCuspSizeBiasPearsonWindow_iff_ratioSplit,
thetaCuspSizeBiasPearsonChiSq_nonneg,
thetaCuspSizeBiasedSusceptibility_eq_mean_mul_next_sub_mean,
thetaCuspSizeBiasPearsonChiSq_hcr_saturation,
thetaCuspSizeBiasMeanLiftWindow_iff_susceptibilityWindow,
thetaCuspSizeBiasMeanLiftWindow_iff_pearsonWindow,
thetaCuspSizeBiasMeanLiftWindow_iff_ratioSplit,
thetaCuspSizeBiasedPowerExpectation,
thetaCuspSizeBiasPowerCovariance,
thetaCuspSizeBiasedPowerExpectation_eq_momentRatio,
thetaCuspSizeBiasedPowerExpectation_one_eq_mean,
thetaCuspRawEvenMoment_cross_le,
thetaCuspSizeBiasPowerCovariance_nonneg,
thetaCuspSizeBiasPowerCovariance_eq_mean_mul_response,
thetaCuspSizeBiasPowerCovariance_one_eq_susceptibility,
thetaCuspSizeBiasPowerCovariance_eq_within_add_between,
thetaCuspSizeBiasedPowerExpectation_le_next,
thetaCuspSizeBiasedMean_le_next,
thetaCuspSizeBiasedSusceptibility_eq_within_add_between,
thetaCuspSizeBiasedSusceptibility_one_lower_of_twoChannelRayleighRitz,
thetaCuspSizeBiasedSusceptibilityWindow_of_twoChannelRayleighRitz,
forall_primeArchSourceTraceHankel_linear_nonneg_of_susceptibilityWindow,
forall_primeArchSourceTraceHankel_linear_nonneg_of_pearsonWindow,
forall_primeArchSourceTraceHankel_linear_nonneg_of_meanLiftWindow,
riemannHypothesis_of_thetaCuspSusceptibilityWindow_of_primeArchDegreeTwoTail,
riemannHypothesis_of_thetaCuspPearsonWindow_of_primeArchDegreeTwoTail,
riemannHypothesis_of_thetaCuspMeanLiftWindow_of_primeArchDegreeTwoTail.
```

The source-specific boundary recursion is in
`formal/GaloisForLFunctions/RHTower/PrimeArchThetaGibbsEquipartition.lean`:

```text
thetaCuspLiouvilleGibbsMoment_nonneg,
integrableOn_pow_mul_thetaCuspMorseScale_mul_liouvilleGibbsAtom,
deriv_thetaCuspLiouvilleGibbsAtom_eq_morseScore,
two_mul_thetaCuspLiouvilleGibbsMorseMoment_zero_eq,
two_mul_thetaCuspFirstAtomLiouvilleGibbsMorseMoment_zero_eq,
two_mul_thetaCuspLiouvilleGibbsMorseMoment_eq,
thetaCuspMorseScale_affine_lower,
pi_mul_sq_mul_gibbsMoment_affine_le_morseMoment,
thetaCuspLiouvilleGibbsMoment_succ_equipartition_upper,
twelve_mul_thetaCuspLiouvilleGibbsMoment_succ_le,
thetaCuspFirstAtomLiouvilleGibbsMoment_succ_equipartition_upper,
twelve_mul_thetaCuspFirstAtomLiouvilleGibbsMoment_succ_le.
```

The source-specific likelihood-ratio order is in
`formal/GaloisForLFunctions/RHTower/PrimeArchThetaAtomLikelihoodRatio.lean`:

```text
thetaCuspMorseScale_mono_nat,
thetaCuspMorseScale_strictMono_nat,
thetaCuspBornWittenSuperpotential_sub_eq_scaleDifference_mul,
thetaCuspBornWittenSuperpotential_mono_nat,
thetaCuspBornWittenSuperpotential_strictMono_nat,
thetaCuspSourceTerm_shift_one,
hasDerivAt_thetaCuspSourceTerm_eq_bornWittenScore,
thetaCuspAtomLikelihoodRatio,
thetaCuspAtomLikelihoodRatio_pos,
hasDerivAt_thetaCuspAtomLikelihoodRatio,
deriv_thetaCuspAtomLikelihoodRatio,
deriv_thetaCuspAtomLikelihoodRatio_nonpos,
deriv_thetaCuspAtomLikelihoodRatio_neg,
thetaCuspAtomLikelihoodRatio_antitoneOn,
thetaCuspAtomLikelihoodRatio_strictAntiOn,
thetaCuspHigherToFirstAtomLikelihoodRatio,
summable_thetaCuspHigherAtomLikelihoodRatios,
thetaCuspHigherToFirstAtomLikelihoodRatio_eq_tsum,
thetaCuspHigherToFirstAtomLikelihoodRatio_antitoneOn,
thetaCuspHigherFirst_crossProduct_order,
thetaCuspHigherFirst_monotoneObservableKernel_nonneg,
integrableOn_pow_mul_thetaCuspHigherSource,
thetaCuspHigherAtomRawEvenMoment_eq_integral_higherSource,
thetaCuspHigherFirst_rawEvenMoment_cross_le,
thetaCuspHigherAtomSizeBiasedPowerExpectation_le_first,
thetaCuspFirstHigher_betweenPowerFactor_nonneg,
thetaCuspSizeBiasPowerCovariance_within_le.
```

## Physics attack now exposed

1. Represent the `k=0` and `k=1` size-biased theta states by their explicit positive densities in
   `y=x^2`.
2. Reuse the two-channel Rayleigh--Ritz certificate for `(1)`; its direct susceptibility consumer
   is now formalized.  Proving that certificate remains a source-specific matrix estimate, but no
   further moment-ratio translation is needed.
3. Do not retry the ordinary curvature-only Brascamp--Lieb estimate: the existing formalized
   Robin/Witten audit records that its valid weighted bound misses the required first-atom
   constant.  A useful upper producer must be observable-specific: a sharpened Stein-kernel,
   higher-order response, or source-defined information-contraction estimate.
4. Use the proved normalized first/tail power order to retain the nonnegative between-atom term in
   lower-response estimates, or drop it soundly when a lower bound needs only the two within terms.
5. Use `(13)` to bound the higher-tail variance and between-mean mismatch separately for the upper
   gate; compare this
   with the existing uniform atom-domination loss before choosing the sharper producer.
6. A generic data-processing inequality alone is not a producer: the corpus does not yet expose a
   source-defined channel whose contraction gives `D_0 <= 29/16`.  Constructing such a channel is
   an explicit open core, not an implicit hypothesis discharge.
7. Transport any proved bounds through the equivalences above; do not re-expand them into the old
   raw cubic obstruction.

Neither the Pearson coordinate nor data processing discharges the bounds by itself.  The lower
half still waits on the existing two-channel certificate, and the upper half still requires a
source-specific estimate beyond ordinary Brascamp--Lieb.

## Literature provenance

1. H. B. Callen and T. A. Welton, *Irreversibility and Generalized Noise*, Physical Review 83
   (1951), 34--40, DOI
   [10.1103/PhysRev.83.34](https://doi.org/10.1103/PhysRev.83.34).
2. R. Kubo, *Statistical-Mechanical Theory of Irreversible Processes. I*, Journal of the Physical
   Society of Japan 12 (1957), 570--586, DOI
   [10.1143/JPSJ.12.570](https://doi.org/10.1143/JPSJ.12.570).
3. H. J. Brascamp and E. H. Lieb, *On extensions of the Brunn--Minkowski and
   Prekopa--Leindler theorems, including inequalities for log concave functions, and with an
   application to the diffusion equation*, Journal of Functional Analysis 22 (1976), 366--389,
   DOI
   [10.1016/0022-1236(76)90004-5](https://doi.org/10.1016/0022-1236(76)90004-5).
4. R. Arratia, L. Goldstein, and F. Kochman, *Size bias for one and all*, Probability Surveys 16
   (2019), 1--61, DOI
   [10.1214/13-PS221](https://doi.org/10.1214/13-PS221).
5. S. M. Ali and S. D. Silvey, *A General Class of Coefficients of Divergence of One Distribution
   from Another*, Journal of the Royal Statistical Society B 28 (1966), 131--142, DOI
   [10.1111/j.2517-6161.1966.tb00626.x](https://doi.org/10.1111/j.2517-6161.1966.tb00626.x).
6. D. G. Chapman and H. Robbins, *Minimum Variance Estimation Without Regularity Assumptions*,
   Annals of Mathematical Statistics 22 (1951), 581--586, DOI
   [10.1214/aoms/1177729548](https://doi.org/10.1214/aoms/1177729548).
7. G. R. Price, *Selection and Covariance*, Nature 227 (1970), 520--521, DOI
   [10.1038/227520a0](https://doi.org/10.1038/227520a0).
8. S. A. Frank and F. J. Bruggeman, *The fundamental equations of change in statistical
   ensembles and biological populations*, arXiv
   [2010.14544](https://arxiv.org/abs/2010.14544).
9. D. Berenstein and G. Hulsey, *Anomalous Bootstrap on the half line*, arXiv
   [2206.01765](https://arxiv.org/abs/2206.01765).
10. C. V. Sukumar, *Generalised Virial theorems in Classical and Quantum Physics*, arXiv
    [1410.5592](https://arxiv.org/abs/1410.5592).
11. S. Karlin and J. McGregor, *Classical diffusion processes and total positivity*, Journal of
    Mathematical Analysis and Applications 1 (1960), 163--183, DOI
    [10.1016/0022-247X(60)90020-2](https://doi.org/10.1016/0022-247X(60)90020-2).
12. M. Bagnoli and T. Bergstrom, *Log-concave probability and its applications*, Economic Theory
    26 (2005), 445--469,
    [author manuscript](https://escholarship.org/uc/item/0xt8k6sd).

The literature supplies the physics coordinate and candidate inequality technology.  The exact
constants and the application to the theta-cusp moment gates are corpus-specific `[BRIDGE]`
relations, proved algebraically in the Lean source.

## Verification status

Source inspection only.  Under the active user constraint, no Lean invocation, scratch
compilation, lint, axiom inspection, numerical check, targeted build, or full build was run.

## Gates

- [x] General size-biased normalized-moment value API written.
- [x] Both raw theta gates rewritten as exact susceptibility bounds.
- [x] Direct linear-Hankel and degree-two-tail/RH consumers written.
- [x] Existing two-channel Rayleigh--Ritz certificate connected to the lower susceptibility bound.
- [x] Full theta susceptibility decomposed exactly into first-atom, higher-tail, and between-atom
  fluctuations.
- [x] Successive size-bias Pearson information, adjacent-ratio curvature, and quantum Fisher
  signal normalization formalized in general HTGeometry and applied to the theta/RH consumers.
- [x] Size-bias mean-lift/QFI identity and Hammersley--Chapman--Robbins saturation formalized;
  both theta gates linearized and the generic chi-square-bound route retired.
- [x] Robertson--Price power-response identity formalized generally; existing theta
  log-convexity connected to every separated cross-Hankel sign and every power-response
  monotonicity theorem.
- [x] General total-covariance mixture identity formalized and applied to every theta atomwise
  power response.
- [x] Half-line endpoint anomaly, positive-power equipartition, affine Morse elimination, and
  rational two-step first-atom moment decay formalized without numerical input.
- [x] Exact theta-atom translation law, ordered Born--Witten scores, strict atom likelihood-ratio
  order, higher-tail likelihood-ratio order, and the division-free monotone-observable kernel
  written in Lean source.
- [x] Generic HTGeometry likelihood-kernel integration and its direct theta application written:
  all size-biased higher-tail power expectations are ordered below the first atom, discharging the
  signed between-atom covariance factor.
- [x] The likelihood order is used to remove one complete `3005/2997` loss from each first-atom
  transfer at paper level.
- [ ] Narrow source verification when explicitly authorized.
- [ ] Prove the upper susceptibility bound `(2)` from the explicit theta density.
- [ ] Prove the lower susceptibility bound `(1)` from a source-specific Ward/score estimate.
- [ ] RH.

## Reflected half-density normalization of the atom mixture `[PROVED ON PAPER]`

The completed endpoint value `XiC(I/2)=1/2` and the first-atom Ward--Laplace anchors determine the
entire exponential generating mass of the first/higher mixture.  If

```text
q=8/2997,
H=1/2-(4*pi-1)*exp(-pi),
W=a_0+a_1/8,
```

then the exponentially damped atom comparison proves `H<q*a_0<q*W`, while likelihood order gives
`r_0<=H` and `r_1/a_1<=H/W`.  Therefore the two susceptibility gates
follow from the finite first-atom conditions

```text
14*(W+H)*a_2^2<=9*W*a_1*a_3,
16*(a_0+H)*a_2<=45*a_1^2.
```

This is strictly weaker than paying the uniform tail enclosure once.  See
`../2-fully-proven/not_new_scientific_knowledge/theta-cusp-half-density-ward-laplace-budget-transfer.md`.
The unconditional branch activation is
`../2-fully-proven/not_new_scientific_knowledge/theta-cusp-half-density-damped-tail-domination.md`.
The remaining work is proving these two explicit first-atom inequalities and the independent
higher-degree Hankel tail.

## Turan-defect coordinate for the reflected first-atom gates `[PROVED ON PAPER]`

The two remaining first-atom susceptibility conditions have one common source coordinate.  With
`M_(2*j)=a_j/2` and

```text
D_m=M_(2*m)^2-(2*m-1)/(2*m+1)*M_(2*m-2)*M_(2*m+2),
delta=(a_0+a_1/8+H)/(a_0+a_1/8),
```

they are equivalent to

```text
D_1 >= (1/45+16*H/(45*a_0))*M_0*M_4,
D_2 <= (1-14*delta/15)*M_4^2.
```

A half-line Csordas--Varga identity expresses every `D_m` through
`E=(V'/x)'` for the explicit first-atom potential.  Its boundary pole is a closed nonnegative
odd-moment determinant, and the antisymmetric half-density reflection gives the exact exponential
budget of all those odd moments.  The regular curvature changes sign exactly once, while its two
order-specific crossing windows are positive and strictly unimodal.  The residue is therefore two
opposite inequalities for one signed seam paired against two explicit windows.  See
`../2-fully-proven/not_new_scientific_knowledge/theta-cusp-antisymmetric-half-density-turan-curvature-transfer.md`.
This replaces the vague request for separate Ward/score estimates by one one-dimensional
source comparison, tracked in `theta-cusp-one-seam-turan-window-balance.md`; the independent
higher-degree Hankel tail remains open.  The continuous cutoff constraints feeding that comparison
are proved in
`../2-fully-proven/not_new_scientific_knowledge/theta-cusp-continuous-half-density-residual-tail-chart.md`.
