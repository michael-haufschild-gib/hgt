# Uncorrected Gauss–Mayer branch cutoffs at zeta scattering parameters

- **Stage:** 5-failed
- **Type:** No-go with positive survivor
- **Parent:** [three approaches, A](../1-in-progress/argon-three-orthogonal-rh-approaches.md).

## Exact obstruction

On the disc algebra `|z−1|≤3/2`, let
`L_{s,N}f(z)=Σ_{n=1}^N(n+z)^(−2s)f(1/(n+z))`.
For every nontrivial zeta zero `ρ`, with `s=ρ/2`,

`‖L_{s,N}‖/N^(1−Re ρ) → 1/|1−ρ| > 0`.

Thus these raw finite-alphabet cutoffs diverge in operator norm at every
actual zeta scattering target, including critical zeros. Ordinary branch
convergence cannot distinguish critical from off-critical resonances there.

This obstruction concerns these uncorrected cutoffs only. It does not exclude
Padé approximants, corrected cutoffs, the continued Mayer operator, nuclearity,
Fredholm comparisons, or the full scattering route.

## Positive survivor

For `Re s>0`, `s≠1/2`, subtracting the explicit constant-mode operator
`N^(1−2s)/(1−2s) · [f↦f(0)·1]` gives operator-norm convergence with error
`O(N^(−2 Re s))`. On `0<Re s<1/2`, this leading coefficient is forced among
all bounded-operator subtractions of the same power scale. The corrected
operator equals the usual absolutely convergent branch sum for `Re s>1/2`.

[Exact theorem, constants, paper proof, and Lean certificate](../3-formalized/gauss-mayer-renormalized-cutoff-operator.md).
Both obstruction and positive survivor are formalized in
`RenormalizedIntersectionTheory/GaussMayerCutoffRenormalization.lean`;
the final direct check and transitive axiom audits passed with only
`propext`, `Classical.choice`, and `Quot.sound`.

The corrected operator also has a certified order-zero nuclear expansion and
geometric finite-rank error bound: [paper proof and Lean certificate](../3-formalized/gauss-mayer-renormalized-nuclear-expansion.md). This strengthens the positive
survivor without supplying a scattering determinant identity.

Its [global determinant](../3-formalized/gauss-mayer-source-fredholm-determinant.md)
is now certified as the entire limit of actual coefficient determinants, with
an explicit error and zeros exactly at failure of invertibility of the
original Banach operator. Selberg/scattering comparison remains open.

The [actual fixed-point trace](../3-formalized/gauss-mayer-fixed-point-trace.md)
is also certified, including the countable branch/diagonal interchange.
Its corrected scalar series continues normally to `Re w>−1`, with explicit
summand bound `(|w|+1)n^(−Re w−2)`. [Every power trace](../3-formalized/gauss-mayer-countable-word-traces.md)
is now identified with its absolutely convergent countable word sum on
`Re w>1`, including integral multipliers and the parity-sensitive shift law.
Primitive geodesic coding and the scattering identity remain open.

[Source-parameter holomorphy](../3-formalized/gauss-mayer-source-parameter-holomorphy.md)
is also certified for the actual operator and determinant, together with the
operator's nonzero rank-one residue at `w=1`. The
[exact determinant pole theorem](../3-formalized/gauss-mayer-rank-one-determinant-pole.md)
now gives `D=A+ζB`, residue `B(1,λ)`, and removability exactly at its closed
discrete countable zero set. Its derivative at `λ=0` is `−1`.

[Successor cancellation](../3-formalized/gauss-mayer-negative-unit-pole-cancellation.md)
now proves `det(I+R(w)+tP)=det(I+R(w))` throughout `Re w>0` for every `t`.
Thus the actual negative-unit source determinant is holomorphic through one,
despite the operator pole. Its paper proof and all thirteen production axiom
audits are complete. The raw finite-branch determinants themselves now
[converge at `λ=−1`](../3-formalized/gauss-mayer-raw-negative-unit-determinants.md),
including at every actual zeta parameter where the raw operator norms diverge.
The exact finite shear, uniform nuclear control, and operator/matrix transport
are Lean-certified with thirteen clean production axiom audits. The obstruction
therefore concerns operator convergence, not this negative-unit determinant limit.
