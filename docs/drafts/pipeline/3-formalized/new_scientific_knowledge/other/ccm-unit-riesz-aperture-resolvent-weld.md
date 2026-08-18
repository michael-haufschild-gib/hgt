# CCM unit-Riesz / aperture-resolvent source weld

- **ID:** `ccm-unit-riesz-aperture-resolvent-weld`
- **Stage:** `3-formalized/new_scientific_knowledge`
- **Type:** EXACT LITERAL-SOURCE COMPOSITION / ROUTE COLLAPSE
- **Status:** `[PAPER-PROVED] [LEAN-PROVED, UNCONDITIONAL] [NOVELTY UNVERIFIED] [NO RH CLAIM]`
- **Routes:** `CCM-UR`, `CCM-FU`, `Route O`, `Route G`, `CCM-HG`, `CCM-GS`, `CCM-EP`
- **Parents:** `ccm-unit-riesz-completed-source-stieltjes-weld`,
  `ccm-critical-mellin-aperture-resolvent-law`

## Public claim

The literal finite-aperture CCM unit-Riesz response is not a new arithmetic producer. After
substituting the completed-error Volterra law, its fast exponential channel cancels exactly and
the whole source dependence becomes the corpus's positive unit-rate critical-Mellin aperture
resolvent. For every `t >= 0`,

```text
U(t) = 3(t-3)exp(-t) + 8exp(-3t/2)
       -(3/2)exp(-t/2) R_1(t),                                    (1)

R_1(t) = exp(-t) integral_0^(exp t) (psi(y)-y)y^(-1/2)dy.          (2)
```

Therefore every lower bound on `U` is exactly an upper bound on `R_1`, pointwise and with no
loss of exponent. CCM-UR's remaining arithmetic lower law and the aperture-resolvent Riesz-sector
upper law are one theorem, not two pieces of evidence.

This identity does not prove that theorem or RH.

## 1. Literal completed source

Put

```text
g(h) = (psi(exp h)-exp h)exp(-h/2),
E(h) = 4sinh(h/2)-sum_(n<=exp h) Lambda(n)/sqrt(n).
```

The already formalized completed-error Volterra law is

```text
E(h)=1-2exp(-h/2)-g(h)-(1/2)integral_0^h g(v)dv.                    (3)
```

The finite unit-Riesz Stieltjes test has real kernel

```text
F_t(h)=3[exp(-t+h/2)-exp(-3t/2+h)],
U(t)=-integral_0^t E(h)F_t'(h)dh.                                 (4)
```

No differentiability of the prime staircase is used in `(3)--(4)`.

## 2. Volterra cancellation

Substitute `(3)` into `(4)` and integrate the primitive of `g` once against `F_t'`. The
`exp(-t+h/2)` source channel cancels. The exact result is

```text
U(t)=3(t-3)exp(-t)+9exp(-3t/2)
     -(3/2)exp(-3t/2) I(t),                                      (5)

I(t)=integral_0^t exp(h)g(h)dh.                                  (6)
```

This cancellation is forced by coefficient `1/2` in the completed-source Volterra memory; it is
not a fitted kernel or an asymptotic approximation.

## 3. Ray/full-resolvent normalization

The logarithmic substitution `y=exp h` gives

```text
I(t)=integral_1^(exp t) (psi(y)-y)y^(-1/2)dy.                      (7)
```

On `0<y<=1`, `psi(y)=0`, so

```text
integral_0^1 (psi(y)-y)y^(-1/2)dy = -2/3.                         (8)
```

Consequently

```text
I(t)=exp(t)R_1(t)+2/3.                                            (9)
```

Substitution of `(9)` into `(5)` gives `(1)`; coefficient `9` changes to `8` exactly.

## 4. Pointwise orientation law

Let

```text
q(t)=3(t-3)exp(-t)+8exp(-3t/2).
```

Because `(3/2)exp(-t/2)>0`, for every real `B` and `t>=0`,

```text
B <= U(t)
iff
R_1(t) <= (2/3)exp(t/2)[q(t)-B].                                  (10)
```

In particular, a lower law

```text
U(t) >= -C_epsilon exp(-(1/2-epsilon)t)
```

is equivalent, after absorbing explicit exponentially decaying `q`, to

```text
R_1(t) <= C'_epsilon exp(epsilon t),
```

or, with `X=exp t`,

```text
X^(-1) integral_0^X (psi(y)-y)y^(-1/2)dy <= C'_epsilon X^epsilon.
```

Conversion is pointwise; Laplace uniqueness is unnecessary for source identification.

## 5. Cross-route consequences

- **CCM-UR:** remaining signed lower estimate is precisely unit aperture-resolvent upper
  Riesz-sector estimate. It is no longer legitimate to count these as distinct gates.
- **CCM-FU:** its absolute Cesaro bound still implies UR through separately proved curvature
  transport, but UR forgets affine drift and has no reporter-only converse. New identity does not
  collapse FU's stronger reporter to `R_1`.
- **Route O / Route G / CCM-GS:** scalar ground positivity cannot replace missing arithmetic
  estimate. Unit-Riesz test is an oriented subtraction of positive resolvent from a polar level,
  while its canonical fast-minus-slow covariance is indefinite.
- **CCM-HG / CCM-EP:** prior two-channel boundary pulse remains a signed/Krein carrier, not a
  positive covariance. Equation `(1)` identifies scalar source it would have to control.

## 6. Theatre and novelty audit

Weighted Chebyshev mean `(2)` and classical Riesz-type RH criteria are not claimed as new.
Candidate new result is exact finite-aperture composition `(1)` connecting that mean to corpus
unit-Riesz completed-current response, including forced cancellation, `2/3` tail, coefficient `8`,
and order equivalence `(10)`. Corpus and targeted primary-literature searches found no prior
statement of this composition. External novelty remains unverified.

This is significant route progress because it deletes a false degree of freedom: no alternate
UR-specific source estimate remains to discover. It is not an RH proof because `(2)` still lacks
the all-epsilon upper bound.

## Lean status

Unconditional proofs are in
`formal/GaloisForLFunctions/RHTower/CCMUnitRieszApertureResolventWeld.lean`:

- `unitRieszCompletedSourceResponse_eq_chebyshevRayIntegral`;
- `unitRieszChebyshevRayIntegral_eq_primeIntegral`;
- `integral_chebyshevHalfWeight_zero_one`;
- `unitRieszChebyshevRayIntegral_eq_fullResolvent`;
- `unitRieszCompletedSourceResponse_eq_apertureResolvent`;
- `unitRieszCompletedSourceResponse_re_ge_iff_apertureResolvent_le`.

Module is wired into `GaloisForLFunctions.RHTower`.

## Gates

- [x] exact paper derivation
- [x] unconditional Lean proof
- [x] umbrella wiring
- [ ] external novelty verification
- [ ] prove common source-sector estimate
- [ ] compose estimate with existing RH endpoint

## Log

- 2026-08-16 — derived exact Volterra cancellation and ray/full-resolvent normalization; proved
  literal source weld and pointwise orientation in Lean.

## Index of the formalization

Modules: `RHTower/CCMUnitRieszApertureResolventWeld.lean`,
`RHTower/CCMUnitRieszApertureResolventEpsilonTransfer.lean`.  All declarations are unconditional;
`#print axioms` returns only `propext, Classical.choice, Quot.sound`.

| Card item | Lean declaration |
|---|---|
| `(3)` completed-error Volterra law | `criticalMellinNormalizedChebyshevError_eq_apertureError` |
| `(4)` finite unit-Riesz Stieltjes test | `unitRieszCompletedSourceResponse_eq_errorIntegral` |
| `(5)`, `(6)` Volterra cancellation | `unitRieszCompletedSourceResponse_eq_chebyshevRayIntegral` |
| `(7)` logarithmic substitution | `unitRieszChebyshevRayIntegral_eq_primeIntegral` |
| `(8)` elementary `0 < y ≤ 1` tail | `integral_chebyshevHalfWeight_zero_one` |
| `(9)` ray/full-resolvent normalization | `unitRieszChebyshevRayIntegral_eq_fullResolvent` |
| `(1)` exact composition | `unitRieszCompletedSourceResponse_eq_apertureResolvent`, `unitRieszCompletedSourceResponse_re_eq_apertureResolvent` |
| `(10)` pointwise orientation law | `unitRieszCompletedSourceResponse_re_ge_iff_apertureResolvent_le` |
| §4 all-`epsilon` order equivalence | `unitRiesz_lowerLaw_iff_apertureResolvent_subpower` |
| §4 uniform normalized remainder | `unitRieszApertureResolventRemainder_normalized_eq`, `abs_unitRieszApertureResolventRemainder_normalized_le` |

The two remaining gates (`prove common source-sector estimate`, `compose estimate with existing RH
endpoint`) are the open arithmetic frontier the card explicitly does **not** claim; every statement
the card proves is formalized.
