# Primitive modular coding of the actual Gauss words

- **Stage:** 3-formalized
- **Type:** Theorem
- **Parent:** [actual countable word traces](gauss-mayer-countable-word-traces.md).

## Target

Classify the actual even Gauss words under `SL₂(ℤ)` conjugacy and proper
powers, and prove that they represent every positive-trace hyperbolic class.
The literal Gauss matrices have determinant `(-1)^k`; one-digit cyclic
rotation uses a determinant-minus-one conjugator. The classification retains
this parity and identifies the inverse-class involution explicitly.

## Certified actual Gauss classification

The literal `Word (2*k)` matrices now satisfy the target: integral conjugacy
is cyclic splitting of consecutive digit pairs; an integral `r`th root
exists exactly when the pair sequence is an `r`fold repetition. Pair
extraction recovers every original digit, and every positive-trace
hyperbolic integral class has a nonempty even Gauss representative.

Every one-digit Gauss matrix squared is primitive in `SL₂(ℤ)`, despite its
two identical digits. Thus ordinary digit-word primitivity is insufficient.

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

- `GaussMayerPrimitiveWordCoding.lean`, namespace `MayerGaussCoding`:
  `evenWordPairs_digits`, `evenWordMatrix_conjugacy_iff`,
  `evenWordMatrix_root_iff`, `exists_evenWordMatrix_intertwiner`,
  `single_digit_square_primitive`.

- `GaussMayerPrimitiveOrientation.lean`, namespace `MayerOrientation`:
  `integralInverse_spec`, `adjugate_intertwiner_iff_transpose`,
  `actualPairedMatrix_reversedPairs`, `actualPairedMatrix_inverse_spec`,
  `actualPairedMatrix_inverse_conjugacy_iff`.

All seven direct production checks pass without diagnostics. Their
56 transitive axiom audits use only `propext`, `Classical.choice`, and
`Quot.sound`. Umbrella imports wired.

## Actual digit bridge and inverse classes

The source uses reversed digit order; `M_a M_b=R^(a+1) L^(b+1)` and uniqueness of
positive alternating runs now connect it exactly to the matrix classification.
A conjugacy cut producing another aligned word must cut at a whole run-pair
boundary. Repeated words inherit the same first and last generator, giving
the exact whole-pair root classification.

For `J=(0,−1;1,0)`, exact multiplication gives
`J A⁻¹ J⁻¹=Aᵀ`. Gauss digit matrices are symmetric, so transpose reverses
digit order. On pair sequences this is `ps.reverse.map (a,b ↦ (b,a))`.
The inverse of the actual matrix of `ps` is integrally conjugate to the
actual matrix of `qs` exactly when `qs` is a cyclic rotation of that reversed
pair sequence. The explicit adjugate is proved to be the two-sided inverse.
No oriented/unoriented geodesic identification, Selberg-product identity,
scattering normalization, or resonance exclusion is assumed.
