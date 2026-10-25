# Hilbert–Schmidt reserves measure the arithmetic adjoint defect

- **ID:** hilbert-schmidt-reserves-measure-the-arithmetic-adjoint-defect
- **Stage:** 2-fully-proven
- **Type:** CONJECTURE (Lean verification pending)
- **Source:** Q-II; actual full-Hasse Meyer convolution representation.
- **Statement:** A faithful quadratic reserve on genuine Meyer cohomology supplies Bézout unconditionally; its exact excess over the ordinary Weil form is half the squared Hilbert–Schmidt adjoint defect. Its RR axiom is equivalent to simple critical Xi zeros.
- **Status:** UNVERIFIED. Actual Lean candidate present; direct check and transitive axiom audit pending. External novelty unverified.

## Genuine source and exact reserve

Let `T(g)` be the existing full-Hasse convolution operator of an actual strong
logarithmic Meyer source `g`, and let `g#` denote arithmetic sharp. Define

`P(g) = (||T(g)||_HS² + ||T(g#)||_HS²)/2`.

Every operator in this formula is genuinely Hilbert–Schmidt. Indeed, the
corpus factors `T(g)` as `R ∘ (R ∘ T(E²g))`, with the actual Hasse resolvent
`R` Hilbert–Schmidt. A bounded composition of a Hilbert–Schmidt operator is
Hilbert–Schmidt. This proves admission directly, without assigning a value
to a divergent operator norm or adding an admission hypothesis.

Both operators descend through the genuine Poisson boundary. The existing
representation is faithful, and sharp preserves the boundary ideal.
Consequently `P(g)=0` exactly when `g` is a genuine Poisson boundary.
The two nonnegative squared norms make this equivalence immediate in the
forward direction; faithfulness and sharp stability give the reverse direction.

Write `A=T(g)`, `B=T(g#)`, and
`delta(g,g)=Re tr(A B)`, the actual source intersection defect. Hilbert–Schmidt
polarization, adjoint invariance of the norm, and trace cyclicity give

`P(g)-delta(g,g) = ||A-B*||_HS²/2`,

`P(g)+delta(g,g) = ||A+B*||_HS²/2`.

For example the first right-hand side expands as
`(||A||²+||B*||²-2 Re <A,B*>_HS)/2`; the real cross term is
`Re tr(A B)`. The second identity uses the plus sign. All sums are admitted
Hilbert–Schmidt sums, and both products are trace class.

## Cone consequences on the original Meyer pairing

For a cycle `x=(a,b,g)`, use the existing two fibre degrees and declare

`x effective iff deg_H(x)>=0, deg_V(x)>=0, P(g)<=2 deg_H(x) deg_V(x)`.

The reserve is fibre invariant, nonnegative, and quadratic on the real
source space. The two exact identities prove `-P<=delta<=P` on diagonals.
Polarizing these two inequalities gives
`delta(g,h)²<=P(g)P(h)` by the already proved quadratic-majorant lemma.
Thus this source-defined cone has Bézout and ampleness without RH or
simplicity. It is additive, closed under nonnegative scalars, convex, and
generates the full cycle space by adding sufficiently large fibres.

An effective cycle of ample degree zero has both fibre degrees zero and
`P(g)=0`. It is therefore a genuine principal cycle, by the exact principal
criterion on the Meyer surface. Conversely a genuine principal cycle has
these three zero readings. The cone is consequently pointed after quotienting
by principal cycles. This retains higher jets, unlike ordinary numerical
equivalence, which only sees values at Xi zeros.

## Exact RR criterion

The sharp source-cone RR criterion is `P(g)<=delta(g,g)` for every source.
The first norm identity shows that this holds exactly when

`T(g#)=T(g)*` for every actual source `g`.

The dependency-closed adjoint classification in
`../3-formalized/arithmetic-sharp-is-the-hilbert-adjoint-exactly-for-simple-critical-zeros.md`
identifies this with RH together with simplicity of every Xi zero.
Thus the new cone has unconditional Bézout and genuine-class faithfulness,
while RR detects the complete adjoint defect, including nilpotent jets.
This statement is an unconditional equivalence; neither RH nor simplicity
is assumed or claimed proved.

## Exact linear-degree representation target

Unverified corollary, now included in the actual Lean candidate: a complex-linear
cohomological degree `d` represents the faithful reserve on every arithmetic sharp
square, `P(g)=Re d([g*g#])`, if and only if RH and Xi simplicity hold. Equivalently,
such a representation exists exactly when this reserve cone satisfies RR.

The forward argument uses the reserve's exact zero set: any representing degree
is strictly positive on every nonprincipal source square. The certified theorem
`exists_faithful_positive_meyer_degree_iff` then forces both conditions. Conversely,
the candidate RR criterion and its independent Bézout theorem force `P=delta`
by source-boundary rigidity, so the actual ordinary trace degree represents it.
Thus no continuity, square-root factorization, or new analytic input is needed.

Corpus search for a faithful Hilbert–Schmidt reserve represented by a linear
sharp-square degree found the existing adjoint/faithful-degree equivalence and
the reserve's RR/adjoint candidate, but no exact reserve-representation theorem.
External novelty remains unverified. Lean targets:
`exists_meyerHilbertReserve_linear_degree_iff` and
`meyerHilbertSourceCone_riemannRoch_iff_linear_degree`.

## What this changes

The positive origin degree is faithful on literal sources but fails to descend;
ordinary trace descends but loses higher jets. The reserve above is both
cohomological and faithful, and its price is an explicit adjoint-defect square.
It is quadratic rather than a degree of the arithmetic sharp-square product.
The underlying Hilbert representation uses Xi jets, so this construction is
not an independent arithmetic proof of RR or a replacement for the remaining
source positivity problem.

## Exact corpus dependencies and formalization status

- `DeningerMeyerConvolutionTraceClass`: actual resolvent factorization and trace admission.
- `DeningerMeyerFaithfulConvolution`: exact boundary kernel and faithful quotient representation.
- `HilbertSchmidtOperator`, `HilbertSchmidtTrace`: polarization, adjoint isometry, trace pairing.
- `MeyerSourceIntersectionSurface`: actual surface and ordinary trace defect; actual-file certified with standard axiom audits.
- `ArithmeticMajorantsSupplyBezout`, `PositiveQuadraticSourceCones`: mixed bound and cone geometry.
- Actual arithmetic-sharp adjoint classification: Lean certified with standard transitive axiom audits.

No infinite coordinate expansion of the Hilbert–Schmidt norm is needed or claimed.

Internal novelty audit also found
`xiReciprocalKernel_normTraceGap_eq_half_adjointDefect` in
`XiThermalQuadraticReflectionDefectSpectrum`: the same operator mechanism is
already certified for a special diagonal Xi kernel. The new assertion concerns
the whole genuine source algebra, faithful full Hasse blocks, and the exact RR
criterion; the elementary Hilbert–Schmidt polarization identity is not claimed new.

Actual candidate file exists with endpoint axiom prints; its actual-file
verification is pending. It is not wired into the umbrella.
