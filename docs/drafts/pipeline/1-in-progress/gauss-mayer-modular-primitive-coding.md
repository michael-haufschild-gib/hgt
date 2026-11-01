# Primitive modular coding of the actual Gauss words

- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Parent:** [actual countable word traces](../3-formalized/gauss-mayer-countable-word-traces.md).

## Target

Classify the actual even Gauss words under `SL₂(ℤ)` conjugacy and proper
powers, and prove that they represent every positive-trace hyperbolic class.
The literal Gauss matrices have determinant `(-1)^k`; one-digit cyclic
rotation uses a determinant-minus-one conjugator. Ordinary digit necklaces
therefore require an orientation audit.

## Certified matrix classification

Let `L=(1,1;0,1)` and `R=(1,0;1,1)`. Every nonnegative determinant-one
integer matrix has a unique word in `L,R`. For strictly positive words:

1. Integral determinant-one conjugacy is exactly cyclic word splitting.
2. An integral determinant-one `k`th root exists exactly when the word is a
   repetition of one whole word `k` times.
3. Every integral determinant-one matrix with trace greater than two is
   conjugate to a strictly positive word, with explicit inverse integral
   determinant-one change-of-basis matrices.

Euclidean row subtraction proves unique generation. Mediant subdivision
gives arbitrarily narrow adjacent unimodular rational brackets around every
irrational slope, with width at most `1/(n+1)`. For the expanding slope `x`,
`λ=cx+d>1`, `μ=λ⁻¹`, the exact identity
`f(y)−x=μ(y−x)/(cy+d)` maps a small bracket strictly inside itself.
Its boundary basis gives a strictly positive conjugate.

For positive `A,B` and an arbitrary integral unimodular intertwiner `CA=BC`,
normalized powers converge to the positive rank-one expanding projection.
Its image under `C` has one strict sign, so one of `CA^n` and `-CA^n` is
strictly positive for all sufficiently large `n`. Free-word cancellation
then gives cyclic splitting. For a root `B^k=A`, a signed positive shift
`D=±BA^n` satisfies `D^(2k)=A^(2(nk+1))`. The common-word-root theorem and
word lengths force the source word to be a `k`fold repetition.

## Lean certificates

Modules in `RenormalizedIntersectionTheory`:

- `GaussMayerPositiveMatrixCoding.lean`: unique nonnegative words, cyclic
  splitting for nonnegative intertwiners, common roots of commuting words.
- `GaussMayerUnimodularRationalCones.lean`:
  `exists_unimodular_rational_cone`, quantitative bracket bounds.
- `GaussMayerHyperbolicReduction.lean`:
  `exists_positive_integral_conjugate`, expanding-slope identities.
- `GaussMayerPositiveConjugators.lean`:
  `eventually_intertwiner_one_sign`, `exists_positive_intertwiner`.
- `GaussMayerIntegralWordConjugacy.lean`:
  `integral_intertwiner_iff_cyclic_split`, `integral_root_iff_word_power`,
  `exists_integral_word_conjugate`.

All five direct production checks pass without diagnostics. Their
6+3+9+11+4 transitive axiom audits use only standard axioms. Umbrella imports
wired. These certify the matrix classification, not the full Gauss target.

## Remaining bridge

Two positive Gauss digits satisfy `M_a M_b=R^a L^b`; the actual `wordMatrix`
uses reversed digit order. Translate alternating positive runs into that
literal source, prove cyclic classification with even digit rotations, and
retain even-word primitivity: the square of an odd primitive Gauss word can
be primitive in `SL₂(ℤ)`.

Matrix/inverse conjugacy and oriented versus unoriented multiplicities must
also be audited before a geodesic or Selberg-product identity. No such
identity, scattering normalization, or resonance exclusion is assumed.
