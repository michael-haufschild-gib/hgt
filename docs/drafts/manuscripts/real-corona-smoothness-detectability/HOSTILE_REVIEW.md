# Hostile review ledger

Paper: *Smoothness--detectability conservation for Real-corona orientations*

Target standard: a broad, renowned research journal such as *Advances in Mathematics*.  A pass
requires correct theorem typing, self-contained human proofs of central claims, credible novelty,
and an unconditional Lean dependency cone.  Formal elaboration of a surrogate object does not
repair a mismatch with the object named in the paper.

## Review 1 — 2026-08-03

Verdict: **REJECT / MAJOR MATHEMATICAL REVISION**.

### Fatal issue H1: P2 has not reached the CCM relative cyclic object

`CCMRationalStrongCyclicLefschetz` acts on `CCMRationalStrongCyclicTarget`, the unquotiented cyclic
submodule cut out by the main-diagonal strong trace condition.  Its own module documentation says
that it is the action required *before* descent along the closed restriction range.

The actual closed relative object currently formalized is
`CCMRationalAdelicClosedRelativeCyclicModule`, the degreewise quotient of the full class-space
cyclic module by the closure of the range of
`ccmRationalAdelicReducedClassSpaceCyclicHom`.  No declaration yet descends class-space translation
to this object, constructs its Real structure and Lefschetz endomorphism, or proves that the
resulting endomorphism is nonzero.

The matrix-unit theorem does not fill this gap.  It proves that
`CCMRationalStrongDegreeZeroFieldSubmodule` is not two-sided.  The CCM cokernel quotients by the
closed reduced-source range, not by the entire strong-condition submodule.  Non-two-sidedness of a
larger containing submodule says nothing about two-sidedness of the smaller closed range.  The
paper's inference from the matrix units to an obstruction in the closed CCM cokernel is therefore
invalid as written.

Required repair:

1. Construct the source class-space action and prove equivariance of the genuine Morita
   restriction.
2. Prove continuity for the exact target topology and stability of the closed source range.
3. Descend translation and the even Real structure to the closed CCM relative cyclic module.
4. Prove nontriviality/nonvanishing there; an invertible endomorphism is not nonzero on a possibly
   zero quotient.
5. Only then state the parity obstruction and scalar-shift classification as a CCM Lefschetz
   theorem.

### Fatal issue H2: P2 does not construct the requested bivariant Chern character

The constructed object is a cyclic-module morphism.  It is not yet a class in a specified entire
or periodic bivariant theory, and the manuscript's limitations section admits that the relevant
bornological completion and homotopy theory are missing.  A negative theorem may solve the direct
lift request, but it must be proved on the actual CCM recipient.  The prequotient morphism cannot be
advertised as the requested bivariant Chern comparison.

Required repair: after H1, either construct the chosen bivariant class and comparison, or state and
prove on the exact object that no requested lift exists.  Any positive survivor must be named at
its real type.

### Major issue H3: human proof of strong landing was initially too compressed

The first draft replaced roughly twenty thousand lines of finite-adic, Schatten, and Poisson Lean
infrastructure by a dependency sketch.  This is below general-journal proof standards.  Revision
now includes periodic strong decay, common-period adelic packets, exact Haar quadrature,
Schatten-1 transport, and all-degree total-product reduction.  This issue is improved but remains
open until every notation and topology used in the landing proposition is defined independently of
the code.

### Major issue H4: “one law, four shadows” is not yet a dependency theorem

The operator parity law directly proves the P1 smoothness/detectability split.  P2 uses Real
parity, P3 uses the identity theorem, and P4 uses orbit multiplicity.  The synthesis identities are
real and formalized, but the paper currently presents a conceptual analogy as if all four results
were corollaries of one theorem.  A pass requires either a precise master theorem with the four
specializations, or language that distinguishes a shared involutive mechanism from logical
dependence.  Because the research goal explicitly requests a universal law, preferred repair is a
genuine theorem, not rhetorical weakening.

### Major issue H5: P1 bridge to a local index formula needs exact scope

The Lean theorem annihilates arbitrary series of positive commutator-jet words plus a summable
reflection-invariant degree-zero term.  The paper must prove that the stated JLO/residue character
evaluated on the reduced orientation has exactly this form for the specified complete-divisor
spectral triple.  Without regularity/dimension-spectrum and factorization statements, the result is
a local-series no-go, not yet a theorem about every standard local index formula compatible with
the divisor.

### Major issue H6: P3 automorphic scope

The universal divisor theorem and positive-degree analytic interface are correct conditional
classification results, with actual Riemann and primitive self-dual Dirichlet instances.  The
paper does not yet formalize higher-rank automorphic completions or prove that their standard
analytic properties instantiate the interface.  It must not claim an unconditional all-automorphic
classification until that bridge exists.

### Major issue H7: P4 recipient

The support/multiplicity theorem uses a genuine Grothendieck group of finite coordinate rank
vectors, but the paper has not identified this group with the K-theory of the same full-adeles
crossed-product recipient used in P2/P3.  The computed comparison is valid for the coordinate
fixed-divisor algebra.  A broader Real-corona K-class claim needs an explicit functorial map.

## Repairs already accepted during Review 1

- Removed false uniqueness wording for the scalar Clifford shift.
- Added and elaborated the exact theorem
  `KRealHom.smul_isAnti_iff_star_eq_neg`; for every nonzero Real-even morphism, `zT` is anti-Real
  exactly when `conj z = -z`.
- Added the CCM prequotient specialization and facade theorem for this classification.
- Added `DeningerMeyerStrongLogDecay.weighted_iteratedDeriv_isBounded`, formally justifying the
  manuscript's global exponential-weight supremum form.
- Expanded the human proof of all-degree strong landing and corrected the finite-rank Fourier-mode
  decomposition by choosing the base residue so that the physical zero mode remains zero.

## Gate state

- Mathematical hostile review: **FAIL** (H1 and H2 fatal).
- Claim-to-Lean symbol audit: in progress.
- Lean lint: not yet run after revision.
- Axiom audit: not yet run after revision.
- Targeted final build: not yet run.
- PDF: compiles, but final visual audit waits for mathematical closure.

No publication-ready promotion is authorized by this review.
