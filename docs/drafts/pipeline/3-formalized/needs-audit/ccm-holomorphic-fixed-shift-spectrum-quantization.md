# CCM holomorphic fixed-shift aperture-spectrum quantization

- **ID:** CCM-C33
- **Stage:** 3-formalized/needs-audit
- **Type:** THEOREM (Lean)
- **Status:** `[LEAN-FORMALIZED] [UNCONDITIONAL] [NOVELTY-AUDIT-OPEN] [NOT RH] [NOT WHOLE-CCM DEATH]`
- **Source:** `docs/handover/connes.md` §§71--74; C30--C33
- **Statement:** Every norm-holomorphic germ in one fixed positive CCM shift, with values in any
  complex normed space, either vanishes locally and eventually annihilates every aperture carrier,
  or translates its complete aperture exponential spectrum by exactly shift length times finite
  vanishing order.

## Goal

Classify the full norm-holomorphic functional calculus of a fixed CCM spectral shift at the
infinite-aperture augmentation point, for scalar, vector, bounded-operator, and Schatten-valued
filters. Determine whether an infinite Taylor series or a regular operator-valued family can cross
the completed-critical-Mellin exponent frontier after finite polynomial filters were shown unable
to do so stably.

## Exact theorem

Fix `q>0`, put `z_q(h)=exp(-q h)`, and let `F` be complex analytic at `0`. Define

```text
M_(q,F)(h)=|F(z_q(h))|.
```

For a nonnegative carrier `eta`, write `U(eta,epsilon)` for

```text
eta(h) <= C exp(epsilon h) eventually
```

for some `C>=0`. Then exactly one of the following analytic-germ branches occurs.

1. If `ord_0(F)=infinity`, then `F` is zero near `0`, `M_(q,F)` is eventually zero, and
   `U(M_(q,F) eta,epsilon)` holds for every `eta` and every real `epsilon`.
2. If `ord_0(F)=m<infinity`, then, for every eventually nonnegative `eta` and every real
   `epsilon`,

```text
U(M_(q,F) eta,epsilon) <-> U(eta,epsilon+q m).             (C33.1)
```

Consequently

```text
M_(q,F) eta has zero exponential type
  <-> eta has every upper rate q m + epsilon, epsilon>0.   (C33.2)
```

If `F(0) != 0`, then `m=0`; the filter preserves zero exponential type exactly. No Taylor
coefficient after the first nonzero one changes any aperture exponent.

The direct published-source connector is

```text
U(M_(q,F)|E_crit|,epsilon)
  <-> U(|E_crit|,epsilon+q ord_0(F)),                      (C33.3)
```

where `E_crit` is the completed critical-Mellin error from C30 and `F` is any nonzero analytic
germ.

## Paper proof `[PROVED HERE]`

Assume first that `ord_0(F)=m<infinity`. Analytic vanishing-order factorization gives an analytic
germ `G`, with `G(0)!=0`, and a neighborhood of zero on which

```text
F(z)=z^m G(z).
```

Since `q>0`, `z_q(h)->0` as `h->infinity`. Therefore the factorization holds eventually on the
physical arc and

```text
M_(q,F)(h)=exp(-q m h) M_(q,G)(h).                        (C33.4)
```

Continuity gives `M_(q,G)(h)->|G(0)|>0`. Hence C32's complete positive bounded-multiplier law
says multiplication by `M_(q,G)` preserves every exponential upper-rate budget. Multiplication
by `exp(-q m h)` translates the rate exactly from `epsilon` to `epsilon+q m`. Combining those two
equivalences proves `(C33.1)`. Quantifying over every positive `epsilon` proves `(C33.2)`, and
specializing `eta=|E_crit|` proves `(C33.3)`.

If `ord_0(F)=infinity`, analytic-order characterization says `F=0` on a neighborhood of zero.
The physical arc eventually lies in that neighborhood, so the multiplier is eventually zero and
the first branch follows with bound constant `C=0`.

The same proof is formalized for `F : C -> E` in every complex normed space `E`, with absolute
value replaced by norm. Thus `(C33.1)`--`(C33.2)` apply without a dimension, rank, compactness, or
scalar-valued premise. Every step is formalized. There is no RH premise, estimate, numerical
computation, finite-rank premise, polynomial truncation, or unresolved mathematical hypothesis.

## Scientific consequence

C32 closed finite polynomials in a fixed shift. C33 closes every norm-analytic germ in that same
shift coordinate, including infinite convergent Taylor series and operator-valued analytic
families. Analytic completion adds no new aperture-rate behavior: the entire norm spectrum is
quantized by one integer, the augmentation vanishing order.

This is not RH and not death of the whole CCM lane. It rules out norm-holomorphic fixed-shift
calculus as an RH-closing mechanism, even before scalarization. A surviving transform must use at
least one feature absent from the theorem:

- a singular/nonanalytic boundary germ at `z=0`;
- a cofinal family whose order is not fixed before the aperture limit;
- several orbit coordinates with nontrivial joint limiting geometry; or
- genuinely singular/non-norm-holomorphic operator graph information before scalarization.

Exact active endpoint remains source-normalized Evans nonvanishing / four-unit Xi graph
relative-trace contraction. C33 sharpens it: retrying a convergent scalar power series in one
fixed shift cannot reach that endpoint.

## Formal declarations

- `analyticShiftMultiplier`
- `apertureExponentialUpperBound_congr`
- `tendsto_analyticShiftMultiplier`
- `analyticShiftMultiplier_eventually_factor`
- `apertureExponentialUpperBound_analyticShift_complete_iff`
- `SubexponentialAboveApertureRate`
- `subexponentialAtApertureInfinity_analyticShift_complete_iff`
- `subexponentialAtApertureInfinity_analyticShift_unit_iff`
- `analyticShiftMultiplier_eventually_eq_zero_of_order_eq_top`
- `apertureExponentialUpperBound_analyticShift_of_order_eq_top`
- `criticalMellinCompletedError_analyticShift_upperBound_iff`
- `normedAnalyticShiftMultiplier`
- `tendsto_normedAnalyticShiftMultiplier`
- `normedAnalyticShiftMultiplier_eventually_factor`
- `apertureExponentialUpperBound_normedAnalyticShift_complete_iff`
- `subexponentialAtApertureInfinity_normedAnalyticShift_complete_iff`
- `subexponentialAtApertureInfinity_normedAnalyticShift_unit_iff`
- `normedAnalyticShiftMultiplier_eventually_eq_zero_of_order_eq_top`

Formal source:
`formal/GaloisForLFunctions/RHTower/CCMAnalyticShiftSpectrumRigidity.lean`.

## Gates

- [x] 0 → 1: corpus and failed-route audit; exact one-coordinate scalar scope
- [x] 1 → 2: dependency-closed paper proof `[PROVED HERE]`
- [x] direct Lean check
- [x] axiom audit: only `propext`, `Classical.choice`, and `Quot.sound`
- [x] formal lint attribution audit: no finding in this module; repository-wide lint fails only on
  pre-existing umbrella-reachability findings outside this card
- [x] targeted module build through
  `GaloisForLFunctions.RHTower.CCMBoundaryTraceRamification`
- [ ] external novelty audit
- [ ] RH or whole-lane no-go

## Log

- 2026-07-23 — Proved complete analytic-germ dichotomy, exact quantized spectrum translation,
  shifted zero-type equivalence, holomorphic-unit invariance, locally-zero annihilation, and
  direct completed-critical-Mellin-error connector. Extended the law from scalars to every
  complex normed target, including operator-norm and Schatten-norm families. Direct Lean check
  passed.
