# Uniform finite Gram certificates for finite Weil packets

Status: FORMALIZED — dependency-closed paper proof and Lean verification complete.

Only local Lean corpus and installed Lean dependencies are mathematical
evidence. No web, external papers, or numerics.

## Frontier audit

The proposed finite-support positivity rigidity is already subsumed by
`WeilAbsoluteConvergenceRigidity.eq_zero_of_positiveDefinite_neg_nullPotential_of_sqrt_summable`
and by the finitely generated multiplicative-support result in
`WeilFiniteSupportRigidity`. Do not present that specialization as new.

The new target is a uniform finite quantitative certificate: for every
fixed finite arithmetic coefficient space, finitely many actual real
Gram tests detect every nonzero vector with margin proportional to its
norm. Approximate nonnegativity of those tests bounds coefficient norm.

Local lexical search for `finite Gram certificate` returned 15 hits, none
matching this finite Weil-packet certificate. Source checks found the
real-even positive-definite bridge in `WeilWorkExposingRayPolarKernel`
and the existing sharp reconstruction in `WeilLogShiftFiniteReconstruction`.

## Paper proof

Let P_c(y) be the finite paired-log potential on indices n+2. Finite
support gives zero head, a uniform coefficient bound, and the weighted
absolute summability required by the existing positive-definite rigidity
theorem. Thus -P_c positive definite forces c=0. Real evenness identifies
positive definiteness with nonnegativity of every real Gram quadratic
form. Hence every nonzero c has a strictly negative real Gram witness.

Include an explicit nonnegative scale in each Gram test. Positive scaling
preserves its positivity meaning. Scale a negative witness so its value
at c is -2. Each scaled test is a continuous linear functional of c.
The open sets where its value is less than -1 cover the compact unit
sphere of the finite coefficient space. A finite subcover gives a fixed
finite family of tests, independent of c.

For c nonzero, normalize c by its norm, select a covering test, and rescale:
that test has value strictly less than -norm(c). Consequently if every
selected test is at least -epsilon, with epsilon nonnegative, then
norm(c) is at most epsilon. At epsilon=0 this gives an exact finite
positivity certificate. The zero-dimensional coefficient space is
covered without an artificial nonemptiness assumption.

## Positive survivor and scope

The obstruction to nonzero positive-definite finite packets yields an
actual finite, quantitative certificate, not just a negative statement.
Tests concern the Gram kernel -P_c; they are not claimed to be a fixed
finite family of the original affine Weil test energies. Existing literal
arithmetic HasSum identities identify P_c with the native deviation
potential. No infinite-family rigidity or RH conclusion is claimed.

## Verification — 2026-10-09

Leaf: `formal/GaloisForLFunctions/RHTower/WeilLogShiftFiniteGramCertificate.lean`.

- Final direct `lake --old env lean` leaf check with output olean exited 0,
  without warnings. Both direct dependency oleans and the new olean are
  current relative to their source files.
- All ten public declarations, including definitions and the test-type
  abbreviation, passed `#print axioms`: only `propext`, `Classical.choice`,
  and `Quot.sound` occur. Mathlib API scratch verification passed.
- Exactly one import in the RHTower umbrella. No full or umbrella build.
- Index refresh exited 0. Module-filtered local lexical search recovered
  all ten public declarations, with no missing names.
- Formal lint exited 1 solely on two unrelated HTGeometry modules missing
  umbrella imports: PaperSymmetricSquareNormalRelations and
  QKrawtchoukCompanionTriangular. No lint error names the new leaf.
  Those unrelated files were not changed.

The native identity `finiteWeilGramForm_native` identifies each form with
the literal arithmetic deviation potential using the preceding finite
packet `HasSum` theorem. The two main public results are
`exists_finiteWeilGram_norm_certificate` and
`exists_finiteWeilGram_stability_certificate`.

## Follow-up formalized

`WeilLogShiftFiniteTailCompensation.lean` now derives a native weighted
tail-compensation bound: for every finite support s there is C_s>0,
independent of the Weil-positive sequence, with head norm at most C_s
times the inverse-square weighted absolute mass outside the head.
Literal tail HasSum, a universal remainder envelope, and explicit Gram
translation/amplitude costs are proved. See
[finite Weil tail compensation](finite-weil-tail-compensation.md).
Do not treat C_s or support-dependent tests as uniform in support.
The full corpus-research goal remains active.
