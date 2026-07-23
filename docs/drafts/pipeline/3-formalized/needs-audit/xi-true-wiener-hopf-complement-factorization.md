# True infinite Wiener–Hopf complement factorization

## Status

Formalized unconditionally in Lean 4. Internal corpus novelty established;
external priority requires specialist audit.

## Frontier

Suzuki’s strongest unresolved step is global Pick/Loewner positivity of the
compound Xi Bezoutian. Recent Hardy transport code tries to expose its
anti-causal factor by splitting the full Xi canonical product into strict-right
and complementary factors.

Current complementary factor is defined by totalized pointwise division

`xiCanonicalProduct z / xiRightCanonicalProduct z`.

At every strict-right Xi zero both numerator and denominator vanish, so Lean
sets the quotient to zero. This gives a pointwise identity `0 = 0 * 0`, but not
the removable analytic quotient. Consequently current “Wiener–Hopf
factorization” cannot be differentiated across its own divisor and cannot
support a global Schur, Pick, or Julia argument.

## Theorem WH-COMPLEMENT

For every genus-one indexed canonical product with reciprocal-square summable,
nonzero spectral points, and every predicate on its multiplicity index:

1. canonical products on predicate and complementary subtypes are entire;
2. full product equals predicate product times complementary product at every
   complex point;
3. each factor is nonzero away from its selected divisor.

For the Xi strict-right predicate this produces a genuine entire complement
factor. Multiplying it by the nowhere-zero Hadamard quotient gives an entire
source factor whose product with the strict-right factor is exactly `XiC`.
At a strict-right zero, genuine source factor is nonzero while current
totalized-division source factor is zero.

## Hostile falsifiers

- Infinite-product splitting may fail if subtype products are not independently
  multipliable.
- `Equiv.sumCompl` may reverse factor order or lose multiplicity copies.
- Complement may share a spectral value with strict-right subtype despite
  distinct multiplicity indices.
- Hadamard quotient may fail to be globally nonzero after removable filling.
- Old totalized quotient might accidentally agree with true complement at the
  divisor.

Lean discharges every falsifier without axioms, finite exhaustions, or numerical
evaluation.

## Scientific value if proved

This does not assert RH. It removes a genuine analytic defect exactly at the
infinite continuation wall and supplies the first valid global factor on which
the unresolved compound-Bezoutian positivity question can be posed. The
predicate-splitting theorem is universal and prevents the same totalized
division error for arbitrary canonical-product Wiener–Hopf decompositions.

## Sharp Xi removability law

Lean proves both equivalences

```text
RiemannHypothesis
  ↔ AnalyticOnNhd ℂ xiNonrightCanonicalProduct univ

RiemannHypothesis
  ↔ AnalyticOnNhd ℂ xiNonrightSourceFactor univ.
```

Reason: old quotient and genuine complement agree near zero. If old quotient
were entire, identity continuation would force global equality. At every
strict-right zero old totalized quotient is zero while genuine complement is
nonzero, contradiction. Under RH strict-right divisor is empty, right factor
is identically one, and old source equals `XiC`.

Thus prior claim that old pointwise factorization is a global analytic
Wiener–Hopf split is false unless RH has already been proved. Replacement
factor is entire unconditionally and preserves full Xi analytic multiplicity
in strict-right factor.

## Formal artifacts

- `formal/GaloisForLFunctions/RHTower/CanonicalProductPredicateSplit.lean`
- `formal/GaloisForLFunctions/RHTower/GammaSewnMobiusXiTrueWienerHopfFactorization.lean`

Direct `lake env lean` checks pass. Targeted cached build
`lake build GaloisForLFunctions.RHTower.GammaSewnMobiusXiTrueWienerHopfFactorization`
passes `8850/8850`, building only two new leaves after cached replay. Six
capstone axiom surfaces use only `propext`, `Classical.choice`, and
`Quot.sound`; forbidden-declaration scan is clean. Global lint reaches an
unrelated concurrent umbrella error:
`HTGeometry.LagrangeRemainder` is not imported by `HTGeometry`.
