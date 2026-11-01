# Primitive modular coding of the actual Gauss words

- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Parent:** [actual countable word traces](../3-formalized/gauss-mayer-countable-word-traces.md).

## Target

Classify the actual even Gauss words under conjugacy in `SL₂(ℤ)`, including
proper powers, and prove that they represent every positive-trace hyperbolic
conjugacy class. The existing word matrices have determinant `(-1)^k`;
cyclic rotation through one digit uses a determinant-minus-one conjugator.
Thus ordinary digit necklaces cannot be identified with modular classes
without an orientation and primitivity audit.

## Proposed proof

Let `L=(1,1;0,1)` and `R=(1,0;1,1)`. Two consecutive positive Gauss digits
satisfy `M_a M_b=R^a L^b`. Euclidean subtraction now gives a certified unique expression of every
nonnegative determinant-one integer matrix as a word in `L,R`.

For strictly positive matrices `A,B` and an integral determinant-one
intertwiner `CA=BC`, the expanding eigendirections suggest that one of
`CA^n` and `-CA^n` is eventually strictly positive. For nonnegative determinant-one intertwiners, the exact cyclic word
classification is certified. Euclidean prefix cancellation also proves that
commuting nonnegative unimodular matrices are powers of one word. Extending
these results to arbitrary integral conjugators and roots remains open.

For a general integral matrix with trace greater than two, choose an
oriented unimodular rational cone around its attracting irrational ray.
Certified mediant subdivision preserves the determinant and gives adjacent slopes
with interval width at most `1/(n+1)`: adjacent denominators stay positive,
their sum grows by at least one, and their product is at least their sum
minus one. For the expanding fixed slope `x`, write `λ=cx+d>1`, `μ=λ⁻¹`.
The exact identity
`f(y)−x = μ(y−x)/(cy+d)` sends any sufficiently small bracket strictly
inside itself, since `cy+d>μ>0`. Conjugation by its two primitive
boundary vectors therefore gives a strictly positive integer matrix; this
hyperbolic reduction is now certified.

Finally translate cyclic runs back to the actual Gauss digits, retaining
even rotation and the possible square of an odd primitive Gauss word.
Conjugacy classes of a matrix and its inverse must also be counted explicitly
before passing to any convention for oriented or unoriented geodesics.

## Audit and gaps

The corpus supplies the literal word matrices, fractional-linear action,
real periodic points, expanding quadratic multipliers, and absolutely
convergent power traces. Local searches did not surface a primitive modular
coding theorem. Mathlib supplies continued-fraction determinant and error
formulas; these alone do not prove this classification.

Classification under arbitrary integral conjugacy and the primitive modular
bridge remain unproved here. In particular, no full conjugacy classification, root,
geodesic, Selberg-product, or scattering identity is assumed. The target is
an exact matrix coding bridge for the existing source, not a definition of
Selberg zeta by the desired Fredholm determinant.

## Certified building blocks

Modules in `RenormalizedIntersectionTheory`, namespace `MayerCoding`:

- `GaussMayerPositiveMatrixCoding.lean`: `exists_matrixWord`,
  `matrixWord_injective`, `cyclic_split_of_intertwiner`,
  `positive_intertwiner_iff_cyclic_split`, `commuting_words_common_root`,
  `commuting_matrices_common_root`.
- `GaussMayerUnimodularRationalCones.lean`: `rationalBracket_spec`,
  `rationalBracket_width`, `exists_unimodular_rational_cone`.

The cone theorem gives, for every irrational `x` and every `ε>0`, integers
`p,q,r,s` with positive `q,s`, `ps−rq=1`, and
`r/s<x<p/q`, `p/q−r/s<ε`. The constructive unit-interval brackets have width
at most `1/(n+1)`.

`GaussMayerHyperbolicReduction.lean`, namespace `MayerHyperbolic`, proves
`exists_positive_integral_conjugate`: every integral determinant-one matrix
with trace greater than two has a strictly positive integral conjugate,
with explicit determinant-one inverse change-of-basis matrices. Its proof
also certifies irrationality of the expanding multiplier and slope, and
the exact projective displacement identity above.

All three direct production checks pass without diagnostics. Six word,
three cone, and nine hyperbolic transitive axiom audits use only standard axioms.
Umbrella imports wired. These are foundations for the target classification;
the full conjecture above is not certified.
