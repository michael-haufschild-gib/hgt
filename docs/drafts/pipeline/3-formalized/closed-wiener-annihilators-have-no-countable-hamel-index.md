# Closed Wiener annihilators have no countably infinite Hamel index

- **ID:** closed-wiener-annihilators-have-no-countable-hamel-index
- **Stage:** 3-formalized
- **Type:** THEOREM (formalized)
- **Source:** Q-III; `TheCriticalWienerAlgebraIsABanachAlgebra.lean`; the actual cofactor representation and its closed annihilator.
- **Statement:** Every actual cofactor-annihilator quotient has either finite algebraic dimension equal to its cyclic Hilbert dimension, or exactly continuum Hamel dimension. Countably infinite algebraic index is impossible.

## Paper proof

Let `B` be a complex Banach space algebraically spanned by a countable family.
Its finite subsets give a countable family of finite-dimensional subspaces
covering `B`. Each is closed. Baire's theorem gives one with nonempty interior.
A linear subspace with nonempty interior is the whole space: translating an
interior ball gives a ball about zero in the subspace, and scaling puts every
vector in that ball. Thus `B` is finite-dimensional.

If `dim_C B=aleph0`, choose a countable Hamel basis. The preceding argument
would make `B` finite-dimensional, a contradiction. More generally,
`dim_C B<=aleph0` implies finite dimension.

The critical Wiener algebra is Banach. Its actual cofactor representation is
bounded, so its kernel is closed. The quotient by this kernel is therefore a
Banach space, and the preceding conclusion applies at every subcritical damping.
No energy-admission or zero-location premise is needed.

## Consequence for Q-III

The algebraic codimension of a closed module annihilator and the Hilbert
dimension of the completed cyclic module are different invariants. A formula
equating this algebraic codimension with a countably infinite zero count cannot
hold. A finite-dimensional formula still requires its own multiplicity proof.
This does not show that the actual infinite-dimensional branch occurs, nor does
it show that the original repairing ideal is closed. The latter ideal must not
be substituted for the closed module annihilator in this argument.

The positive replacement is exact: a countably generated algebraic Banach
quotient is finite-dimensional; an infinite-dimensional Banach quotient has
uncountable Hamel dimension. This leaves open whether a Hilbert or filtered
index can recover the relevant zero count.

## Exact finite-index replacement

There is a sharper positive comparison for a cyclic Banach-algebra action.
Let `q(a)=pi(a)v` be its continuous cyclic map. Its kernel equals `ker(pi)`
by commutativity and cyclicity, and its image is dense in the Hilbert module.
The algebraic first-isomorphism theorem identifies `W/ker(pi)` with this
image. If either this quotient or the Hilbert module is finite-dimensional,
the image is finite-dimensional and therefore closed. Density then makes it
the whole Hilbert module. Thus finite-dimensionality is equivalent on both
sides, and their finite dimensions agree exactly.

Applied to the actual cofactor module, this gives the appropriate finite
index: its closed annihilator quotient has finite dimension exactly when
the cyclic Hilbert module does, with the same dimension. In the infinite
case the quotient instead has uncountable Hamel dimension. This still does
not turn a hull set into an index: multiplicity and the module action remain
necessary. The source representation and cyclicity discharge all premises
of this application. The comparison's Lean proof and final source check passed.

## Lean status

### Exact continuum refinement

For every actual module, the infinite Hamel index is exactly continuum.
The following constructive argument and its actual application passed Lean
with standard axioms; both new continuum source checks passed.

Let `q:W->H` be the continuous cyclic map with dense infinite-dimensional
image. Recursively choose `b_n` in `W` so that `q(b_n)` are orthonormal:
density supplies a vector outside each preceding finite-dimensional span,
and finite Gram--Schmidt corrections lift through `q`. Set
`c_n=2^(-n)/(1+||b_n||)>0`. For each real `t` in `(0,1)`, the series
`a_t=sum_n c_n t^n b_n` converges absolutely in the Banach algebra `W`.
Continuity and orthonormality give
`<q(b_n),q(a_t)>=c_n t^n`. Any finite relation among distinct `q(a_t)`
therefore gives a Vandermonde system in the distinct parameters `t`, forcing
all its coefficients to vanish. Thus the quotient has a linearly independent
family of cardinality continuum.

The draft `/tmp/qiii_continuum_rank_check.lean` constructs this family using
Gram--Schmidt in the image and a summable family of source preimages. It uses
Dedekind independence of the monoid characters `n -> t^n` for the final
independence step. This is the same mechanism already used by the corpus's
Selberg recurrence and Deninger finite-character proofs. The draft passed.
The actual quotient comparison quantifies over every
`ActualCofactorLimit`, with the chosen limit retained as a specialization.

Conversely, `W` injects into the set of complex sequences, whose cardinality
is continuum. A quotient has no larger cardinality, and its algebraic rank
is at most its cardinality. These two bounds give rank exactly continuum.
Combined with the checked finite-dimensional equivalence, the checked exact
dichotomy is: finite index equal to the Hilbert dimension, or continuum Hamel
index. This argument is a functional-analytic cardinality refinement; no
claim of a new general Banach-space theorem is made. It still does not compute
an arithmetic zero count or show which branch the actual escape occupies.

### Existing checked statements

- Generic proof transferred to `HTGeometry/CountableAlgebraicDimensionForcesFiniteDimension.lean`:
  `exists_eq_top_of_countable_finiteDimensional_cover`,
  `finiteDimensional_of_countable_algebraic_span`, `banach_rank_ne_aleph0`.
- The actual annihilator is defined in `TheCofactorLimitIsAWienerModule.lean`;
  its corrected olean check passed.
- Quotient application is transferred to
  `ArithmeticDefectRigidity/TheClosedCofactorAnnihilatorHasNoCountableIndex.lean`.
  Both proofs passed scratch checks and standard-axiom audits. The universal
  finite-dimensional comparison also passed a source-only check. Its new
  continuum extension is in the same actual-index module, using
  `HTGeometry/InfiniteHilbertImagesHaveContinuumRank.lean`. The full extension
  passed scratch checking and standard axioms. Imports are wired; final source
  checks of the new generic module and extended actual module passed. The older
  generic Baire module and the actual Wiener module also passed final source-only
  checks in the sequential core audit. Every verification gate is complete.

## Gates

- [x] Complete paper proof and precise index distinction.
- [x] Generic Lean proof checked in scratch, standard axioms only.
- [x] Actual closed-quotient application checked in scratch, standard axioms only.
- [x] Axiom audit, final checks, and umbrella imports.
