# Vertical jets do not control full torus order

- **ID:** AHA-VERTICAL
- **Stage:** 5-failed
- **Type:** FALSIFIED
- **Source:** ../3-formalized/aha-adams-multiplicity-cost.md
- **Statement:** For arbitrary complex coefficients, vanishing of vertical jets cannot replace vanishing of all coordinate jets in the arithmetic torsion length bound.

## Exact obstruction

`F(z,w)=log(3)(z−1)−log(2)(w−1)` is supported on the integers `1,2,3`.
For `V(s)=F(exp(s log 2),exp(s log 3))`,

`V(0)=V′(0)=0`, but `∂F/∂z(1,1)=log 3≠0`.

The derivative along the logarithmic line cancels two distinct prime
directions. Thus vertical order at least two does not force full order
two, and support ends below `2²`. This obstruction uses real logarithmic
coefficients. At algebraic torus points, algebraic coefficients instead
make the first logarithmic derivative faithful to every coordinate
partial derivative, as proved in `AlgebraicVerticalFirstJets.lean`.

## Positive survivor and new insight

Full residue Newton sampling retains the lost directions. For support below
`2^(dr)`, the explicit weighted torsion samples of all Newton orders below
`r` recover each residue coefficient and determine the entire arithmetic
array. This is the unconditional replacement data theorem
[AHA-NEWTON](../3-formalized/aha-residue-newton-resolution.md).
The Euler–Fourier extraction and analytic mixed-jet bridge are now proved
in [AHA-JETS](../3-formalized/aha-adams-multiplicity-cost.md).
They give the sharp full-multiplicity support law with an integral boundary
example. The real-coefficient vertical obstruction remains distinct from
the algebraic-coefficient case.

## Lean closure

Module `ArithmeticHarmonicAnalysis/VerticalJetsMissTransverseDirections.lean`;
namespace `GaloisForLFunctions.ArithmeticHarmonicAnalysis`:
`verticalFlatTrace_at_zero`, `verticalFlatTrace_derivative`, and
`verticalFlatAuxiliary_transverse_jet`.

Positive survivor: `arithmeticNewton_sample_recovery` and
`arithmeticNewton_samples_eq_iff` in `ArithmeticNewtonResolution.lean`.
Both modules passed `lake --old env lean`; transitive axiom checks contain
only `propext`, `Classical.choice`, `Quot.sound`.
The stronger survivor `short_adams_mixedJets_vanishes_iff` in
`AdamsMultiplicityResolution.lean` has the same final and axiom audits.
The algebraic-coefficient boundary is closed by
`algebraic_primeLogTrace_firstJets_vanish_iff` in
`AlgebraicVerticalFirstJets.lean`, with the same audits; see
[AHA-VERTICAL-ALG](../3-formalized/aha-algebraic-vertical-first-jets.md).
