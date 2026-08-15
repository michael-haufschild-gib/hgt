# Route P primitive Burnol / Deninger four-leg Hodge completion

- **ID:** `route-p-primitive-burnol-deninger-four-leg-hodge-completion`
- **Stage:** 3-formalized
- **Type:** SHARP TWO-LEG NO-GO plus POSITIVE MATRIX-COMPLETE FOUR-LEG REPLACEMENT
- **Label:** `P-G202`
- **Source:** P-G200 squared-Cauchy incidence, P-G201 upper secant graph completion, Deninger
  lower/upper prime--Gamma Hilbert realizations, unconditional critical-line reindexing
- **Statement:** The natural lower/upper two-leg graph diagonal is phase-unstable and cannot be a
  nonzero complex Hodge metric. Pullback through source conjugation constructs explicit lower
  secants; coefficient conjugation of their strong limit is exactly the critical-line-reflected
  upper graph jet. This four-leg completion has ordinary Hilbert energy and reproduces the full
  upper squared-Cauchy graph Gram entrywise for every finite matrix amplification.

## Conjecture loop

`C202-A` proposed using the canonical conjugate lower coalescent jet directly as the Hodge mate.
This fails for a structural reason stronger than the earlier pole mismatch. On any completed jet
vector `x`, the resulting two-leg diagonal is

```text
D_2(x) = inner(conj x, x).
```

Lean proves

```text
D_2(i x) = -D_2(x).
```

Therefore nonnegativity for both phases `x` and `i x` forces `D_2(x)=0`. A nonzero complex graph
domain cannot acquire a phase-independent positive metric from this two-leg bilinear diagonal.
This kills every attempted repair that merely changes canonical lower packet coefficients while
retaining the same two-leg cup.

`C202-B` proposed functional-equation reflection and ordinate reversal. Primitive poles obey the
exact quartet laws

```text
-upper(pe,kappa) = lower(pe,-kappa),
conj(upper(pe,kappa)) = lower(pe,kappa).
```

Thus reflection and conjugation are distinct source legs except on the collapsed ordinate. The
same phase obstruction survives; two symmetries cannot be silently identified.

`C202-C` keeps all four legs. Pull an arbitrary finite upper packet back through the conjugation
equivalence without changing coefficients. Its lower Hilbert realization satisfies

```text
Lower(conjPull y) = pointwiseConj(LineConj(Upper(y))).
```

Applying this to P-G201 secants constructs explicit lower absolute-Euler secants and proves their
strong `ell^2` convergence to

```text
x_lower(q) = A C_z(xiSpectralPoint(q))^2.
```

The conjugate-lower fourth leg is then exactly

```text
H_4(A,w) = pointwiseConj(x_lower(conj A, conj w))
         = LineConj(x_upper(A,w)).
```

Hence the four-leg pairing is an ordinary Hilbert square:

```text
Re inner(LineConj(x_upper), H_4) = ||x_upper||^2.
```

For every finite family, its four-leg Gram is PSD and Lean proves entrywise equality with the
original upper squared-Cauchy graph Gram. No scalarization or diagonal-only argument occurs.

## Higher principle

The persistent Hodge obstruction was shadow of a variance mismatch, not a missing estimate.
Deninger's source cup is complex bilinear on lower/upper packet coefficients; positive Hilbert
energy is sesquilinear. Critical-line reindexing and coefficient conjugation are two independent
operations. Collapsing them into one lower packet produces phase reversal. The minimal positive
completion must retain both operations, hence four legs.

This reinterprets P-G198 and P-G201 together. Cross-mode polarization failed because it attempted
to manufacture a Hermitian matrix inside a bilinear two-leg object. P-G201's divergent graph
secants were not missing positivity; they were missing the conjugate-lower Real-structure leg.
P-G202 supplies that leg exactly and at matrix level.

## What remains

P-G202 closes Hodge sign classification and source completion. It does **not** prove W-H184's
budget contraction. Because the four-leg Gram equals the full upper graph Gram, no energy has been
discarded or bounded by notation. Remaining theorem must construct a coefficient-faithful
contraction/shorting from P-G194's primitive source colligation into this four-leg graph carrier,
while paying P-G199's unbounded `1/(2a^2)` generator cost and preserving P-G196's commutator
anomaly. Any scalar or two-leg positivity argument is now formally excluded.

## Hostile novelty audit

Target Hilbert positivity and abstract Deninger Hodge operators existed. They are not used as the
new input. New content is:

- packet-level conjugation pullback from every finite upper packet to an actual lower
  absolute-Euler packet;
- exact lower/upper Hilbert realization identity under line reindexing and coefficient
  conjugation;
- strong lower squared-Cauchy graph completion inherited from explicit source secants;
- universal quarter-turn phase reversal and zero classification for the natural two-leg diagonal;
- explicit four-leg Hodge mate with strong source-secant approximation;
- matrix-entry equality between four-leg source graph Gram and upper squared-Cauchy graph Gram;
- primitive quartet law separating functional-equation reflection from conjugation.

The construction assumes no Hodge compatibility, source domination, RH, zero location, or
simplicity. It does not claim the still-open contraction.

## Lean certificate

Module:

```text
formal/GaloisForLFunctions/RHTower/RoutePPrimitiveBurnolDeningerFourLegHodgeCompletion.lean
```

Capstones:

- `deningerPrimeGammaLowerToJetHilbert_upperPacketConjToLower`;
- `tendsto_routePDeningerLowerSecantPacket_to_squaredCauchyJet`;
- `routePDeningerTwoLegCupDiagonal_I_mul`;
- `routePDeningerTwoLegCupDiagonal_eq_zero_of_phase_nonneg`;
- `routePDeningerUpperFourLegHodgeMate_eq_lineConj`;
- `tendsto_routePDeningerConjugateLowerSecantPacket_to_fourLegHodgeMate`;
- `re_inner_lineConj_upperSquaredCauchyJet_fourLegHodgeMate`;
- `routePDeningerFourLegHodgeGram_posSemidef`;
- `routePDeningerFourLegHodgeGram_apply`;
- `neg_routePPrimitiveDeningerUpperPoint_coe`;
- `conj_routePPrimitiveDeningerUpperPoint_coe`.

Verification:

- `/tmp/pg202.lean`: `lake env lean /tmp/pg202.lean` passed;
- exact leaf target
  `GaloisForLFunctions.RHTower.RoutePPrimitiveBurnolDeningerFourLegHodgeCompletion` built;
- `/tmp/pg202_audit.lean`: capstones depend only on `propext`, `Classical.choice`, `Quot.sound`;
- forbidden-declaration scan clean;
- umbrella import wired without building umbrella.

## Gates

- [x] classify canonical two-leg graph diagonal under complex phase
- [x] prove two-leg phase-independent nonnegativity forces zero
- [x] construct finite upper-to-lower source packet pullback
- [x] identify lower realization with conjugated line-reflected upper realization
- [x] construct explicit lower source secants and prove strong graph convergence
- [x] construct conjugate-lower four-leg Hodge mate
- [x] prove exact ordinary Hilbert energy identity
- [x] prove full finite-matrix Gram equality and PSD
- [x] identify primitive reflection/conjugation quartet
- [x] scratch verification and exact leaf build only
- [x] axiom and forbidden-declaration audit
- [x] umbrella wired without umbrella build
- [ ] construct coefficient-faithful P-G194-to-four-leg graph contraction/shorting
- [ ] instantiate W-H184 and prove unconditional RH
