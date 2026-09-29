# Gamma-six theta-saddle double-log clock transgression

- **ID:** ULF-GTSD-001
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Parents:** ULF-PHSR-001, ULF-UASA-001;
  `PrimeArchThetaGaussianApertureCurvatureFlow`,
  `PrimeArchThetaGaussianApertureScoreConcentration`,
  `HedenmalmThetaGammaSixWoldCarrier`
- **Purpose:** construct a source-independent moving theta clock from the literal first-atom
  saddle, compare it with the prime--Hodge residue clock, and identify the exact intermediate
  double-log anomaly.

## 1. Higher-law interpretation

ULF-PHSR-001 proves that fixed theta contrast time is too fast: its hazard lies above weak
`S_1`, whereas source history has residue `3`.  The corpus already contains the missing
nonstationary theta coordinate, but in a different route.  The exact first-atom Gaussian-aperture
saddle is a strictly increasing bijection from physical height to moment degree.  Its inverse
therefore turns each successive moment degree into one literal archimedean time increment.

Expressing that increment in the uniquely matching six-unit source clock produces a positive
compact operator with the *same* residue `3` as prime--Hodge history.  The two clocks are not trace-class
relatives.  Their remaining discrepancy is exactly one level smaller:

```text
fixed theta time       -> above weak S_1,
Gamma-six saddle time  -> weak S_1, residue 3,
prime--Hodge time      -> weak S_1, residue 3,
relative discrepancy  -> 3 log log N + finite part.
```

Thus the completion anomaly is stratified.  The first theta atom fixes ordinary logarithmic time;
its inverse-saddle Jacobian creates a double-log transgression; only after this second subtraction
does an ordinary trace-class finite-part problem begin.

## 2. Corpus audit before formulation

Lean-corpus searches for `theta cusp exact tail saddle degree tends infinity gamma scale`,
`theta saddle Wold history clock prime Hodge hazard`, `exact saddle degree inverse history
reparametrization theta completion`, `Gamma six theta saddle degree history`, and `double log
residue theta gamma six Wold carrier` found:

- `thetaCuspGaussianApertureExactTailSaddleDegree` is
  `J_lambda(x)=pi*x*exp(2x)-lambda*x^2-(9/4)x`;
- for every `lambda<=0`, `J_lambda` is a strictly increasing bijection `[0,infinity)` to itself;
- each Gamma shape `j+1/2` has a unique positive response-centered saddle height;
- the exact degree slope and curvature are positive;
- the physical theta flat boundary already has an exact Gamma-six/Wold sampling law;
- target-side theta--Möbius normal energy has a divisor-dependent double-log residue, zero on the
  critical line and one off it, but that is a receiver and supplies no source producer.

No corpus theorem compared inverse-saddle increments with the prime--Hodge hazard or extracted the
source-side `3 log log N` law below.

## 3. Canonical inverse-saddle clock

Fix `lambda<=0` and put

```text
J_lambda(x)=pi*x*exp(2x)-lambda*x^2-(9/4)x.          (GTSD.1)
```

For every `j>=0`, let `x_j(lambda)` be the unique positive number satisfying

```text
J_lambda(x_j)=j+1/2.                                 (GTSD.2)
```

Existence and uniqueness are the corpus theorem
`existsUnique_thetaCuspGaussianApertureResponseCenteredSaddle`; the chosen value is already named
`thetaCuspGaussianApertureResponseCenteredSaddleHeight`.

For a positive clock calibration `c`, define the saddle increment and its diagonal operator by

```text
alpha_j^(c)(lambda)=c(x_(j+1)(lambda)-x_j(lambda)),
A_lambda^(c) e_j=alpha_j^(c)(lambda)e_j.             (GTSD.3)
```

`HedenmalmThetaGammaSixWoldCarrier` independently identifies a Gamma-six shell as a literal Wold
sampling clock of the same theta boundary mode, but it does not by itself justify multiplying
saddle height by six.  That calibration must be earned by the comparison below.

**Theorem GTSD-A (canonical moving theta clock).**  For every fixed `lambda<=0`, the sequence
`alpha_j^(c)(lambda)` is positive, decreases to zero, and

```text
j alpha_j^(c)(lambda) -> c/2.                        (GTSD.4)
```

Consequently `A_lambda^(c)` is positive compact, measurable weak `S_1`, not `S_1`, belongs to every
`S_p` for `p>1`, and

```text
Res(A_lambda^(c))=c/2.                               (GTSD.5)
```

The unique positive calibration whose residue equals the independently proved source residue
`Res(D_1)=3` is therefore `c=6`.  From now on write `alpha_j=alpha_j^(6)` and
`A_lambda=A_lambda^(6)`.

**Proof.**  Direct differentiation gives

```text
J'_lambda(x)=pi*exp(2x)(1+2x)-2lambda*x-9/4,
J''_lambda(x)=4pi*exp(2x)(1+x)-2lambda.              (GTSD.6)
```

For `x>=0` and `lambda<=0`, both are positive; hence `J_lambda` is increasing and strictly convex.
Its inverse is increasing and strictly concave.  Therefore the successive inverse increments in
`(GTSD.3)` are positive and decreasing.  Since `J_lambda(x)->infinity`, the saddle heights tend to
infinity and the increments tend to zero.

The leading first-atom term gives

```text
J_lambda(x)/(pi*x*exp(2x)) -> 1,
J'_lambda(x)/(pi*exp(2x)(1+2x)) -> 1.                (GTSD.7)
```

Taking logarithms of `(GTSD.2)` yields

```text
2x_j/log j -> 1.                                    (GTSD.8)
```

By the mean value theorem, for some `xi_j` between `x_j` and `x_(j+1)`,

```text
x_(j+1)-x_j=1/J'_lambda(xi_j).                       (GTSD.9)
```

The increment tends to zero, so `(GTSD.7)--(GTSD.9)` give

```text
j/J'_lambda(xi_j) -> 1/2.
```

Multiplication by `c` proves `(GTSD.4)`.  Monotonicity identifies the diagonal with the singular
values; harmonic comparison proves the ideal classification and residue `(GTSD.5)`.  Equality
`c/2=3` is equivalent to `c=6`. QED.

## 4. Double-log transgression to the prime--Hodge clock

Let

```text
h_j=6/(2j+9),
D_1 e_j=h_j e_j                                      (GTSD.10)
```

be the source hazard from ULF-PHSR-001, and define the signed relative clock

```text
B_lambda=D_1-A_lambda.                               (GTSD.11)
```

**Theorem GTSD-B (pointwise double-log scale).**

```text
j log j (h_j-alpha_j(lambda)) -> 3.                  (GTSD.12)
```

In particular the diagonal of `B_lambda` is positive for all sufficiently large `j`, and
`B_lambda` is compact but not trace class.

**Proof.**  From `(GTSD.7)` and `(GTSD.9)`, retaining the first relative correction rather than
only its limit,

```text
6j(x_(j+1)-x_j)
 =6x_j/(1+2x_j)+o(1/x_j)
 =3-3/(1+2x_j)+o(1/x_j).                             (GTSD.13)
```

The replacement of `x_j` by `xi_j` changes the expression by `O(1/j)`, because
`J''/J'` stays bounded and `xi_j-x_j=O(1/j)`.  Also

```text
j h_j=3+O(1/j),
log j/(1+2x_j)->1                                   (GTSD.14)
```

by `(GTSD.8)`.  Subtract `(GTSD.13)` from `(GTSD.14)` and multiply by `log j` to obtain
`(GTSD.12)`.  Eventual positivity follows from the positive limit, and harmonic-logarithmic
comparison makes the absolute diagonal nonsummable. QED.

Let `B_lambda^+` be obtained by deleting the finite negative head of `B_lambda`.  It differs from
`B_lambda` by finite rank.

**Corollary GTSD-C (measurable double-log anomaly).**

```text
lim_(N->infinity)
  (1/log log N) sum_(j<N) s_j(B_lambda^+) =3.        (GTSD.15)
```

At ordinary weak-trace scale this anomaly has zero residue:

```text
lim_(N->infinity)
  (1/log N) sum_(j<N) s_j(B_lambda^+) =0.            (GTSD.16)
```

**Proof.**  Equation `(GTSD.12)` says the positive tail is
`3/(j log j)(1+o(1))`.  Finite rearrangement does not change this asymptotic.  Integral comparison
with `1/(x log x)` proves `(GTSD.15)`, and `log log N=o(log N)` proves `(GTSD.16)`. QED.

This explains why an ordinary Dixmier residue sees source and moving theta clocks as identical
while trace-class comparison still fails.

## 5. Exact second finite part

The new anomaly has a canonical finite coordinate, again fixed before divisor specialization.
Define

```text
FP_2(B_lambda)=lim_(N->infinity)
  (sum_(j<N)(h_j-alpha_j(lambda))-3 log log N).       (GTSD.17)
```

**Theorem GTSD-D (double-log finite part).**  The limit exists and equals

```text
FP_2(B_lambda)
 =3 log(pi/2)-3 psi(9/2)+6x_0(lambda).               (GTSD.18)
```

**Proof.**  Both sums telescope exactly:

```text
sum_(j<N) h_j
 =3[psi(N+9/2)-psi(9/2)],
sum_(j<N) alpha_j
 =6[x_N(lambda)-x_0(lambda)].                        (GTSD.19)
```

The digamma asymptotic gives `psi(N+9/2)-log N->0`.  From `(GTSD.1)--(GTSD.2)`,

```text
log N=log pi+log x_N+2x_N+o(1),
log x_N-log log N -> -log 2.                         (GTSD.20)
```

Insert `(GTSD.19)--(GTSD.20)` into `(GTSD.17)` to obtain `(GTSD.18)`. QED.

The constants are all source-owned: `pi` and `9/4` come from the literal theta first atom,
`psi(9/2)` from the prime--Hodge history origin, `6` is the unique calibration matching the source
residue `3` (and is compatible with the separate Gamma-six/Wold carrier), and `x_0` comes from the
unique response-centered theta saddle.

## 6. Joint reconstruction and prediction

The source defect `mathsf T` now has a two-step singular environment:

```text
Gamma-six theta saddle clock A_lambda
  + double-log anomaly B_lambda
  = prime--Hodge clock D_1,

prime--Hodge clock D_1
  + integral nuclear unit mathsf T
  = finite-part translation by +1.                   (GTSD.21)
```

The first line is an exact pre-divisor equality with a nontrivial ideal classification; the second
is PHSR-E.  Together they construct a three-level filtration:

```text
ordinary logarithmic residue  -> cubic dimension 3,
double-log relative residue   -> archimedean clock anomaly 3,
ordinary finite part          -> integral formation translation 1.
```

This predicts why the existing target-side
`HedenmalmThetaMobiusPrimeNormalHalfDensityDoubleLogBoundaryResidue` lives at double-log scale.
The target theorem assigns residue one to one nonneutral completed copy.  The present theorem
produces the missing source-side double-log scale without using any Xi copy.  It does **not** yet
identify the target unit residue with one of the three source channels; that comparison must be
proved, not inferred from the matching normalization.

## 7. Exact RH edge after this theorem

ULF-ARCFP-001 no longer needs an arbitrary history-dependent theta clock.  Candidate clock is the
canonical inverse-saddle Gamma-six clock `A_lambda`.  Remaining completion theorem has three
precise parts:

1. Poisson self-duality selects physical `lambda` and transports the exact double-log
   transgression `B_lambda`, including the unsquared odd prime amplitude.
2. After subtracting `B_lambda`, the completed relative correction is trace class and preserves
   the source finite-part origin.
3. Target exhaustion identifies every strict-right rank-one horizon as an uncompensated positive
   unit translation in that same finite-part frame.

Then actual-minus-neutral finite part is zero at source and the number of strict-right horizons at
target.  Conservation forces that number to zero; reflection gives RH.

The theorem would be circular if physical `lambda` or the target frame were chosen using the zero
divisor.  Every construction above is pre-divisor; the open transport must remain so.

## 8. Hostile audit

- `[CORPUS]` Exact saddle degree, inverse existence/uniqueness, Gamma-six theta sampling, source
  hazard, and target double-log receiver were already separately formalized.
- `[CLASSICAL]` Inverse-function asymptotics, Lambert-W scale, and harmonic/double-harmonic sums
  are standard.
- `[LITERATURE/BRIDGE]` Multi-level logarithmic residue filtrations are not a new field: Lesch,
  *On the noncommutative residue for pseudodifferential operators with log-polyhomogeneous
  symbols*, arXiv:dg-ga/9708010, already develops higher log-residue structure.  Only the exact
  corpus-derived saddle/source identification below is potentially new.
- `[NEW CORPUS FUSION]` Gamma-six inverse-saddle increments have residue `3`; their difference
  from prime--Hodge time has pointwise scale `3/(j log j)`, double-log residue `3`, and exact finite
  part `(GTSD.18)`.
- `[NEW MODEL-CLASS RESTRICTION]` One anomaly subtraction is insufficient.  Completion must
  preserve a two-step singular filtration before trace-class horizon counting is meaningful.
- `[NO RH CLAIM]` Physical aperture selection, oriented Poisson transport, and target exhaustion
  remain open.

## 9. Lean status

Paper proof dependency-closed.  No Lean file was written during the current read-only research
phase.  Existing Lean supplies `J_lambda`, its derivatives, strict convexity ingredients,
bijectivity, unique saddles, Gamma-six sampling, and source hazard.  Stage 3 should formalize the
inverse-increment asymptotics and the two logarithmic limits in a batched module.

## Lean certificate

- [x] 2 → 3: Lean `GaloisForLFunctions.HTGeometry.GammaSixSaddleDoubleLogClock`; `lake env lean` + module build pass; axiom audit `[propext, Classical.choice, Quot.sound]` only

Module `GaloisForLFunctions.HTGeometry.GammaSixSaddleDoubleLogClock` (107 constants), axiom-audit clean. `J_λ = thetaCuspGaussianApertureExactTailSaddleDegree λ`, `J'_λ = …Slope`, `J''_λ = …Curvature` (corpus `PrimeArchThetaGaussianApertureCurvatureFlow`), `x_j = saddleHeight hλ j` (corpus `thetaCuspGaussianApertureResponseCenteredSaddleHeight`), `Δ_j = saddleIncrement`, `α_j^{(c)} = saddleClock hλ c j`, `A_λ^{(c)} = saddleClockOperator`, `h_j = elapsedDefect 1 j = 6/(2j+9)`, `D_1 = elapsedHistoryDefect 1` (ULF-PHSR-001), `b_j = relativeClock`, `B_λ = relativeClockOperator`, `B_λ⁺ = relativeClockPosOperator`.

| Claim | Lean declaration |
|-|-|
| (GTSD.1)–(GTSD.2) `J_λ`, unique positive saddle `J_λ(x_j) = j + 1/2`; heights strictly increase to `∞` | corpus `existsUnique_thetaCuspGaussianApertureResponseCenteredSaddle`; `saddleHeight_pos`, `saddleDegree_saddleHeight`, `saddleHeight_strictMono`, `tendsto_saddleHeight` |
| (GTSD.6) `J' > 0`, `J'' > 0` on `x ≥ 0`, `J'` increasing | `saddleSlope_pos`, `saddleCurvature_pos`, `saddleSlope_monotoneOn` |
| (GTSD.9) mean value: `1/J'(x_{j+1}) ≤ Δ_j ≤ 1/J'(x_j)`; increments decrease | `saddleIncrement_bounds`, `saddleIncrement_antitone`, `saddleIncrement_pos` |
| (GTSD.7) first-atom asymptotics: `J = πxe^{2x}(1-δ)`, `J' = πe^{2x}(1+2x)(1-δ')`, `δ, xδ, δ', xδ' → 0` | `saddleDegree_sub_half_eq`, `saddleSlope_eq`, `saddleDegreeDefect`, `saddleSlopeDefect`, `saddleShiftRatio`, `tendsto_saddleDegreeDefect`, `tendsto_mul_saddleDegreeDefect`, `tendsto_saddleSlopeDefect`, `tendsto_mul_saddleSlopeDefect`, `tendsto_saddleShiftRatio`, `tendsto_pow_mul_exp_neg_two` |
| (GTSD.8) `2x_j/log j → 1` | `tendsto_saddleLog_div`, `tendsto_two_mul_saddleHeight_div_log`, `saddleLog_saddleHeight` |
| Theorem A, (GTSD.3)–(GTSD.5): `α^{(c)}` positive, decreasing to `0`, `j α_j^{(c)} → c/2`; `A_λ^{(c)}` positive compact, weak `S_1`, residue `c/2`, not `S_1`, in every `S_p`, `p > 1`; `c = 6` unique calibration with residue `3` | `saddleClock_pos`, `saddleClock_antitone`, `tendsto_saddleClock`, `tendsto_mul_saddleClock`, `tendsto_six_mul_saddleIncrement`, `saddleClockOperator_isPositive`, `isCompactOperator_saddleClockOperator`, `approxNumber_saddleClockOperator`, `saddleClockOperator_residue`, `saddleClock_calibration` |
| Theorem B, (GTSD.10)–(GTSD.14): `j log j (h_j - α_j) → 3`; diagonal eventually positive; `B_λ` compact, not trace class | `tendsto_relativeClock_doubleLog`, `tendsto_saddleLog_mul_three_sub`, `tendsto_mul_three_sub_saddleClockRatio`, `eventually_relativeClock_pos`, `isCompactOperator_relativeClockOperator`, `not_memSchattenClass_relativeClockOperator` |
| Corollary C, (GTSD.15)–(GTSD.16): `B_λ - B_λ⁺` finite rank; `(1/log log N)∑ s_j(B_λ⁺) → 3`; `(1/log N)∑ s_j(B_λ⁺) → 0` | `exists_hasRankLE_relativeClockOperator_sub`, `tendsto_sum_approxNumber_relativeClockPos_div_log_log`, `hasSchattenLogResidue_relativeClockPosOperator`, `approxNumber_ellTwoDiagonal_le_of_tail`, `sum_le_sum_approxNumber_ellTwoDiagonal` (Ky Fan), `eventually_sum_div_log_log_lt`, `eventually_lt_sum_div_log_log`, `sum_inv_mul_log_ge`, `sum_inv_mul_log_le` |
| Theorem D, (GTSD.17)–(GTSD.20): `∑_{j<N}(h_j - α_j) - 3 log log N → 3 log(π/2) - 3ψ(9/2) + 6x_0` | `tendsto_relativeClock_finitePart`, `tendsto_saddleLog_finitePart` (with PHSR `tendsto_sum_elapsedDefect_sub_log`, `elapsedFinitePart_one`) |
| (GTSD.21) `A_λ + B_λ = D_1` (second line is PHSR-E) | `saddleClockOperator_add_relativeClockOperator`; PHSR `tendsto_formed_add_smul_sub_log` |
| Summary | `gamma_six_theta_saddle_double_log_clock` |

§1, §2, §6 (filtration interpretation), §7 (RH edge, explicitly open) and §8 are interpretation and audit.

## Log

- 2026-09-29 — Lean certificate audited; every numbered claim mapped to a declaration; moved to 3-formalized.
