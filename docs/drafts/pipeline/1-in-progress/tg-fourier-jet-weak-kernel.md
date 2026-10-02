# TG-C9.2: exclude the weak Fourier–jet collision

- **ID:** TG-C9.2-20261001-01a0
- **Stage:** complete research record; canonical stage-3 card is `../3-formalized/tg-fourier-jet-closed-graph.md`
- **Type:** PROVED; production Lean checked, separate axiom audit recorded on the formalized card
- **Parent:** `tg-fourier-radial-jet-completion.md`

## Exact hard target

C9.1 excludes a collision when both position-square jets individually belong to L2.
Closing the two-output source graph could allow cancellation of jets outside that domain.
The next target is the stronger weak equation: no nonzero physical L2 vector annihilates
the Schwartz range of `Q² + (4π²)^-1 D²`, where Q is actual position multiplication
and D is the actual derivative. Prove the closed Fourier–jet source graph reduces to
this weak equation, without silently asserting either separate jet is in L2.

This attacks the same collision through completion. It does not assert a Gamma–Xi identity,
Hardy-index transfer, or sub-unit source action.

## Corpus basis

Documented searches this turn:

- `oscillator virial weak kernel --mode lexical --any --module Oscillator`;
- `hermiteSchwartz annihilation creation --mode lexical --any --module Hermite`;
- deep `dilation generator dense range Schwartz chirp` (partial reranking deadline).

Read the actual `SchwartzOscillatorAlgebra`, `HermiteFourierEigen`,
`HermiteOrthogonality`, and the completeness endpoint of `HermiteL2Completeness`.
They provide creation C=2πQ-D, annihilation B=2πQ+D, Fourier eigenphases,
`C h_n=2π h_(n+1)`, `B h_(n+1)=2(n+1)h_n`, nonzero orthogonal Hermite vectors,
normalized orthonormality, and L2 completeness. The physical dilation generator's
no-point-spectrum theorem also exists, but using it here would require a new exact
metaplectic/domain conjugacy. The Hermite route uses the actual available test vectors.

## Paper mechanism to formalize

Let `b_n=<h_n,u>`, `d_n=||h_n||²`, and `a_n=|b_n|²/d_n`.
The corpus norm recurrence is `d_(n+1)=(n+1)d_n/π`, with d_n>0.

Since `C²+B²=8π² Q²+2D²`, testing the weak equation at h_0 and h_1 gives
b_2=b_3=0. Testing at h_(n+2) gives the exact relation

`π² b_(n+4)+(n+1)(n+2)b_n=0`.

Consequently

`a_(n+4)=[(n+1)(n+2)/((n+3)(n+4))] a_n`.

On each of the surviving residue classes r=0,1, put A_k=a_(4k+r).
For every k≥1 the exact rational factor is at least k/(k+1): after clearing
positive denominators, the difference is 2(k+1) for r=0 and 6(k+1) for r=1.
Thus `A_k≥A_1/k`. Bessel summability and divergence of the harmonic series force
A_1=0, hence A_0=0 and the entire two classes vanish. The other two classes
already vanish by their initial conditions. Hermite completeness then gives u=0.

This is an exact structural exclusion, not a numerical experiment or optimized bound.
All normalization, Fourier signs, weak pairing, summability, and graph-passage steps
are now discharged by the production Lean audit below.

### Stronger recurrence simplification

The initial h_0/h_1 tests and residue-case split are unnecessary. Fix any r≥0 and set
A_k=a_(4k+r). The numerator in the comparison of its recurrence factor with k/(k+1) is

`(k+1)(4k+r+1)(4k+r+2)-k(4k+r+3)(4k+r+4)
 = (4r+2)k+(r+1)(r+2) > 0`.

Thus summability forces A_1=0 for every r. Positivity of the original recurrence factor
then forces a_r=0. The shift-by-four recurrence alone has no nonzero nonnegative summable
solution. In particular, testing against h_(n+2) for every n already suffices for weak-kernel
exclusion. This sharper paper statement should replace the four-case proof in Lean.

## Passage from the actual source graph

For a graph-convergent source sequence, test its second output against a Schwartz vector h.
Maximal multiplication symmetry gives the exact identity

`<h,M f_j+F M g_j> = <M h,f_j> + <M F^-1 h,g_j>`.

Both right-hand entries are continuous in the physical input variables. This proves
closability: zero input limit forces both output limits to vanish, using Schwartz density.
For a zero-output limit (f,g), the first output gives f=-F g. Substituting h=F φ gives

`<M φ-F^-1 M F φ,g>=0`.

The actual Schwartz Fourier derivative identities identify the test vector with
`Q² φ+(4π²)^-1 D² φ`. Thus the weak-kernel theorem would prove injectivity of the
closed graph itself. Closing the graph of the literal finite source core is also covered
by inclusion in this graph; equality with the entire maximal graph domain is a separate
core-density claim, not needed for that inclusion argument. Bounded neutral transport
does not follow from this injectivity and must still be proved or falsified on the retained
source domain.

For Lean, no inverse-Fourier domain construction or sequence extraction is necessary.
Test directly at F φ and use `F(D² φ)=-4π² M(F φ)`. Each test gives a continuous
linear equation in the physical input/output graph coordinates, so its closed kernel
contains the topological closure of the source graph. The Hermite coefficient argument
can then be applied directly to a zero-output point of that closure.

## Completed proof and next arithmetic-domain obligation

1. Completed: square creation/annihilation identity and literal Hermite recurrence.
2. Completed: exclusion of nonzero summable normalized coefficient energies.
3. Completed: weak L2 kernel exclusion, already from the Hermite tail.
4. Completed: actual closed source graph and both projection injectivity theorems.
5. Open: prime-depth graph-core density and the Gamma–Xi/Hardy/sub-unit gaps.

## Formalization checkpoint

The complete proof now passes scratch and production `lake --old env lean` checks without
warnings in `PrimeBurnolFourierJetClosure.lean`. The actual Hermite norm recurrence, ladder
action, Bessel summability, weak coefficient equation, normalization, and full graph
theorem are all checked together. Exact record: `../3-formalized/tg-fourier-jet-closed-graph.md`.
The source graph is represented literally as the topological closure of the range of
`z ↦ (z,E z)`. Separate input/output projection injectivity will certify closability
and absence of new collisions, without assuming separate limiting jet integrability.

Current search `Hermite orthonormal summable inner recurrence` had a partial reranking
deadline. Its returned norm/orthogonality source arguments were inspected alongside
the actual Hermite modules and mathlib Bessel/p-series declarations. Applicability is
established by the scratch Lean checks, not by search ranking.
