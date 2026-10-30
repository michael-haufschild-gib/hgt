# Two-prime homogeneous logarithmic rigidity

- **ID:** AHA-LOG2
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Statement:** For distinct primes `p,q` and every fixed degree `T`, the `T+1` numbers `(log p)^j (log q)^(T−j)`, `0≤j≤T`, are linearly independent over the algebraic numbers; in particular their real values are linearly independent over `ℚ`.

## Proof and scope

Factoring out `(log q)^T` turns a homogeneous relation into a polynomial
relation in `log p / log q`. Gelfond–Schneider supplies transcendence of
this ratio. This is qualitative nonvanishing at every fixed homogeneous
degree; it does not establish algebraic independence of `log p, log q`,
which permits relations mixing degrees.

The complex log ratio remains transcendental over `ℚ̄`: algebraicity over
an algebraic extension of `ℚ` would imply algebraicity over `ℚ` by
transitivity. Therefore the same power-basis argument admits arbitrary
algebraic coefficients. The common factor `(log q)^T` is nonzero.

The [friable auxiliary reduction](not_new_scientific_knowledge/friable-dirichlet-auxiliary.md)
concerns homogeneous forms, not arbitrary polynomial relations. Its
coefficient-surjectivity theorems remain valid. Uniform inverse-power
height bounds are separate from qualitative nonvanishing and are not
claimed here.

## Scope of the arithmetic application

The first-order analytic identification for any finite prime family is
proved in `AlgebraicVerticalFirstJets.lean`: at an algebraic torus point,
the logarithmic derivative vanishes exactly when every coordinate partial
derivative vanishes. Extending this identification to every finite jet
order for two prime coordinates remains a separate analytic application.

## Lean closure

`ArithmeticHarmonicAnalysis/TwoPrimeHomogeneousLogRigidity.lean`, namespace
`GaloisForLFunctions.ArithmeticHarmonicAnalysis`:

- `homogeneousPower_linearIndependent`: the ratio argument over fields;
- `twoPrimeLog_homogeneous_linearIndependent`: the real rational form;
- `twoPrimeLog_homogeneous_algClosure_linearIndependent`: the complex
  algebraic-coefficient form.

The actual source passed `lake --old env lean`. These declarations and
the imported `RHTower.log_ratio_transcendental` have only `propext`,
`Classical.choice`, `Quot.sound` as transitive axioms. No new transcendence
theorem is claimed; this is a classical consequence of Gelfond–Schneider.
