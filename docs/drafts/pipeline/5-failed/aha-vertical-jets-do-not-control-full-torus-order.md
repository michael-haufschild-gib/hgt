# Vertical jets do not control full torus order

- **ID:** AHA-VERTICAL
- **Stage:** 5-failed
- **Type:** FALSIFIED
- **Source:** ../1-in-progress/aha-adams-multiplicity-cost.md
- **Statement:** Vanishing of vertical jets cannot replace vanishing of all coordinate jets in the arithmetic torsion length bound.

## Exact obstruction

`F(z,w)=log(3)(z−1)−log(2)(w−1)` is supported on the integers `1,2,3`.
For `V(s)=F(exp(s log 2),exp(s log 3))`,

`V(0)=V′(0)=0`, but `∂F/∂z(1,1)=log 3≠0`.

The derivative along the logarithmic line cancels two distinct prime
directions. Thus vertical order at least two does not force full order
two, and support ends below `2²`. This obstruction uses real logarithmic
coefficients; the integer-coefficient question remains open.

## Positive survivor and new insight

Full residue Newton sampling retains the lost directions. For support below
`2^(dr)`, the explicit weighted torsion samples of all Newton orders below
`r` recover each residue coefficient and determine the entire arithmetic
array. This is the unconditional replacement data theorem
[AHA-NEWTON](../3-formalized/aha-residue-newton-resolution.md).
Identifying those data with ordinary mixed torus jets remains a separate
bridge; vertical jets do not supply it.

## Lean closure

Module `ArithmeticHarmonicAnalysis/VerticalJetsMissTransverseDirections.lean`;
namespace `GaloisForLFunctions.ArithmeticHarmonicAnalysis`:
`verticalFlatTrace_at_zero`, `verticalFlatTrace_derivative`, and
`verticalFlatAuxiliary_transverse_jet`.

Positive survivor: `arithmeticNewton_sample_recovery` and
`arithmeticNewton_samples_eq_iff` in `ArithmeticNewtonResolution.lean`.
Both modules passed `lake --old env lean`; transitive axiom checks contain
only `propext`, `Classical.choice`, `Quot.sound`.
