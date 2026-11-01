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
satisfy `M_a M_b=R^a L^b`. Euclidean subtraction should uniquely express every
nonnegative determinant-one integer matrix as a word in `L,R`.

For strictly positive matrices `A,B` and an integral determinant-one
intertwiner `CA=BC`, the expanding eigendirections suggest that one of
`CA^n` and `-CA^n` is eventually strictly positive. A positive intertwiner
then becomes a free-word equation. This should classify conjugacy by cyclic
rotation of the `L,R` words and classify roots by their primitive cyclic word.

For a general integral matrix with trace greater than two, choose an
oriented unimodular rational cone around its attracting irrational ray.
Mediant subdivision preserves determinant one and gives adjacent slopes
with interval width at most `1/(n+1)`: adjacent denominators stay positive,
their sum grows by at least one, and their product is at least their sum
minus one. For the expanding fixed slope `x`, write `λ=cx+d>1`, `μ=λ⁻¹`.
The exact identity
`f(y)−x = μ(y−x)/(cy+d)` sends any sufficiently small bracket strictly
inside itself, since `cy+d>μ>0`. Conjugation by its two primitive
boundary vectors should therefore give a strictly positive integer matrix.

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

The positive-word classification, arbitrary integral conjugacy, and primitive
modular bridge remain uncertified here. In particular, no conjugacy, root,
geodesic, Selberg-product, or scattering identity is assumed. The target is
an exact matrix coding bridge for the existing source, not a definition of
Selberg zeta by the desired Fredholm determinant.
