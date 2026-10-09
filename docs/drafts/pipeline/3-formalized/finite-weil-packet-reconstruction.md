# Finite Weil packet reconstruction

Status: FORMALIZED — paper proof and Lean verification complete.

Mission: discharge finite-packet observability using the exact paired-log
kernel classification. Only local Lean sources and installed dependencies
are mathematical evidence; no external papers, web searches, or numerics.

## Corpus evidence

- `RHTower/WeilLogShiftFiniteKernelClassification.lean` classifies the exact
  finite kernel: the sole alias is between coefficient coordinates 0 and 1.
- `RHTower/WeilFullConeNearNullPositiveDefinite.lean` defines normalized
  deviations with both coordinates 0 and 1 identically zero.
- `RHTower/WeilLogShiftArithmeticDomain.lean` supplies `weilCoefficientLift`
  and its exact normalized deviation identity.
- `HTGeometry/WignerSmithFiniteResolutionLawEscape.lean` proves
  `exists_fullRank_real_evaluation_packet` for any finite linearly
  independent family of real-valued functions.
- Local lexical search for `pairedLogKernel` returned 12 declarations,
  including the preceding classification, but no finite reconstruction.

## Dependency-closed paper proof

Index the actual paired kernels by natural numbers shifted by two:
f_n(y) = pairedLogKernel(y,n+2). Push a finite coefficient relation forward
along n ↦ n+2. The classification forces each pushed coefficient at n+2
to vanish. Injectivity of the shift identifies it with the original
coefficient. Thus the entire tail family is linearly independent.

Restrict to any finite set s of tail indices. Existing finite evaluation
packet theorem supplies exactly |s| real shifts whose evaluation matrix
is invertible. Its multiplication map is a real linear equivalence;
finite-dimensionality upgrades it to a continuous linear equivalence.
Its inverse reconstructs every coefficient vector from those samples,
and its operator norm bounds coefficient error by sampled response error.
This removes an analytic observability premise rather than assuming it.

For arithmetic realization, embed each finite coefficient vector as the
sum of singletons at n+2 and apply `weilCoefficientLift`. Both head
coordinates vanish. Its literal deviation series is finitely supported,
so a `HasSum` identity identifies it with the finite paired-kernel sum.
Therefore the same finite sampling equivalence recovers native arithmetic
deviation packets, with genuine convergence recorded.

## Scope

No injectivity claim for infinite summable families. No numerical shift
selection or determinant computation. All finite sets, including empty
set, are covered. Full corpus-research goal remains active.

## Verification — 2026-10-09

Lean leaf:
`formal/GaloisForLFunctions/RHTower/WeilLogShiftFiniteReconstruction.lean`.

- Final direct `lake --old env lean` leaf check with output olean exited 0,
  without warnings. Olean is newer than source.
- All eight public declarations audited through `#print axioms`: only
  `propext`, `Classical.choice`, and `Quot.sound` occur.
- Exactly one import in the RHTower umbrella. No umbrella or full build.
- Index refresh exited 0; module-filtered local lexical search returns all
  eight public declarations.
- Formal lint exited 1 solely on three unrelated HTGeometry modules missing
  umbrella imports: AffineDomainRationalPointCut,
  QKrawtchoukCompanionTriangular, ReciprocalSourceAffineChart.
  No error names the new leaf. Those unrelated files were not changed.

Public results: tail linear independence; attained finite sampling
equivalence with inverse-norm stability; minimum sample-count bound;
finite arithmetic packet definition and head/synthesis identities; literal
arithmetic `HasSum`; unique native reconstruction for every sample vector.

The dimension obstruction has its positive survivor formalized in the
same leaf: exactly the coefficient count of samples suffices.

Follow-up corpus audit: existing absolute-convergence rigidity already
settles the qualitative finite-packet positivity conjecture. The new
`WeilLogShiftFiniteGramCertificate.lean` combines that result with compactness
to obtain a fixed finite family of normalized Gram tests, a norm margin,
and stability under approximate nonnegativity. See
[finite Weil Gram certificate](finite-weil-gram-certificate.md).
Infinite-family injectivity and any RH conclusion remain outside these results.

## Sharp sample-count extension — paper proof

Any sampling map into m real coordinates is linear. If injective, the
finite-dimensional rank inequality forces the coefficient dimension |s|
to be at most m. Thus the constructed |s|-sample receiver attains the
minimum sample count. This obstruction is algebraic and independent of
shift selection; its positive survivor is the existing attained exact
reconstruction map. No new analytic premise is introduced.
