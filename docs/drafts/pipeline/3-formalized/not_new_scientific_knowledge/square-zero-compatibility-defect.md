# Square-zero compatibility is exactly the polarized cross defect

- **ID:** `square-zero-compatibility-defect`
- **Stage:** 3-formalized
- **Type:** THEOREM (paper) / STANDARD ALGEBRA / NOT NEW SCIENTIFIC KNOWLEDGE
- **Formalized companion:** `square-zero-compatibility-defect-formalized.md`
- **Lean:** `formal/GaloisForLFunctions/HTGeometry/SquareZeroCompatibilityDefect.lean`
- **Parent:** `../../5-failed/pure-spinor-square-actuality-route.md`
- **Statement:** For any bilinear square, two square-zero directions have square-zero sum exactly
  when their polarized cross defect vanishes.

## Setup

Let \(R\) be a commutative ring, let \(S,V\) be \(R\)-modules, and let
\[
B:S\times S\longrightarrow V
\]
be \(R\)-bilinear. Define
\[
\operatorname{sq}_B(q)=B(q,q),\qquad
\delta_B(q,r)=B(q,r)+B(r,q).
\]

No nondegeneracy, finite dimension, characteristic-zero hypothesis, inner product, topology, or
physical interpretation is assumed.

## Theorem A: exact polarization

For every \(q,r\in S\),
\[
\operatorname{sq}_B(q+r)
=\operatorname{sq}_B(q)+\delta_B(q,r)+\operatorname{sq}_B(r).
\]

### Proof `[PROVED HERE]`

Bilinearity gives
\[
\begin{aligned}
B(q+r,q+r)
 &=B(q,q)+B(q,r)+B(r,q)+B(r,r)\\
 &=\operatorname{sq}_B(q)+\delta_B(q,r)+\operatorname{sq}_B(r).
\end{aligned}
\]
\(\square\)

## Theorem B: complete square-zero compatibility criterion

If
\[
\operatorname{sq}_B(q)=\operatorname{sq}_B(r)=0,
\]
then
\[
\operatorname{sq}_B(q+r)=\delta_B(q,r).
\]
Consequently,
\[
\operatorname{sq}_B(q+r)=0
\quad\Longleftrightarrow\quad
\delta_B(q,r)=0.
\]

### Proof `[PROVED HERE]`

Substitute the two square-zero hypotheses into Theorem A. The equality and equivalence follow
immediately. \(\square\)

## Theorem C: symmetric bracket form

If \(B(q,r)=B(r,q)\) for all \(q,r\), then
\[
\delta_B(q,r)=2B(q,r).
\]
For square-zero \(q,r\),
\[
\operatorname{sq}_B(q+r)=2B(q,r).
\]

### Proof `[PROVED HERE]`

Symmetry turns the two terms of \(\delta_B(q,r)\) into equal summands. Combine with Theorem B.
\(\square\)

## Scientific boundary

Theorems A--C are standard polarization identities. In a supertranslation algebra they express
the cross anticommutator of two individually square-zero odd directions. They do not establish
that:

1. either direction is a quantum possibility or physical state;
2. their sum is an actual event;
3. the cross bracket creates rather than acts within a supplied translation module;
4. the target has Lorentzian signature or time orientation; or
5. the defect produces gravity or any Standard Model force.

The result closes an algebraic no-go survivor. It is not a physics discovery and cannot support a
Nature claim.

## Lean certificate

The following declarations are unconditional:

- `bilinearSquare_add`;
- `bilinearSquare_add_of_square_zero`;
- `bilinearSquare_add_eq_zero_iff_compatibilityDefect_eq_zero`;
- `squareCompatibilityDefect_eq_two_smul_of_symmetric`; and
- `bilinearSquare_add_of_square_zero_symmetric`.

The implementation uses a bilinear map represented as
`S →ₗ[R] S →ₗ[R] V` over an arbitrary commutative ring. Direct
`lake env lean` verification passes with no warnings.

## Gates

- [x] exact statement and dependency-closed paper proof
- [x] characteristic-two behavior retained rather than silently divided by two
- [x] unconditional Lean implementation
- [x] final module build, axiom audit, lint, and generated-index audit
- [x] stage-3 formal certificate

## Log

- 2026-07-29 — extracted as strongest exact survivor after rejecting the category error
  “nonzero pure-spinor square is physical actualization.”

- 2026-08-15 — re-audited direct source and targeted leaf build after consolidating the paper
  card into Stage 3. All five exact statements remain closed with axioms only `propext` and
  `Quot.sound`.
