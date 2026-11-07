# Incoming cubic spectral residue

- **ID:** cubic-incoming-spectral-residue
- **Stage:** 2-fully-proven
- **Type:** THEOREM
- **Parent:** [cubic theta residue](../1-in-progress/cubic-theta-residue-and-gauss-coefficients.md)
- **Statement:** The actual incoming resolvent correction is meromorphic at `s=4/3`, with residue `(17/6) M P M* F(4/3)` in the `8/9` eigenspace. Adding the incoming seed gives the same residue on every compact quotient set.

Here `F(s)` is the entire quotient `L²` defect, `M` is the energy mass
inclusion, and `P` projects onto the nullspace of `T(8/9)`. The established
resolvent decomposition is
`R(z)=(17/9)(8/9−z)⁻¹ MPM*+R_reg(z)`, with `R_reg` analytic near `8/9`.
Since `8/9−s(2−s)=(s−4/3)(s−2/3)`, multiplication of
`R(s(2−s))F(s)` by `s−4/3` gives an analytic numerator whose central
value is `(17/6)MPM*F(4/3)`. The finite-dimensionality of `P` gives
finite rank. The variational graph identity on `ker T(8/9)` gives the
eigenvalue equation for this residue, including the possibility that it vanishes.

The invariant cusp barrier bounds every principal cusp height on each
compact quotient set. On that set, the seed is therefore the image of
`χ(v)exp(s log v)` in a fixed compact-height Banach algebra under the
bounded profile map followed by compact restriction. This family is entire;
its product with `s−4/3` tends to zero. Thus the local corrected seed is
meromorphic with residue equal to the restricted vector above.

`TheCubicIncomingResidue.lean` is checked: `kernelEisensteinResidueVector_limit`
and `kernelEisensteinResidueVector_graph` use only `propext`, `Classical.choice`,
and `Quot.sound`. The compact-local assertions await
`LocalCubicCorrectedSeeds.lean`, namespace `CubicEisenstein`.

Adapted from OpenAI's meromorphic-resolvent and seed-height arguments.
Source matching and residue nonvanishing remain open on the parent card.
