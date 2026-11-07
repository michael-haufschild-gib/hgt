# Sharp even-degree hyperelliptic calibration

- **ID:** SPL-even-hyperelliptic-calibration
- **Stage:** 0-backlog
- **Type:** CANDIDATE

For squarefree even-degree `f∈F[X]`, `deg f=m≥2`, over every finite field
of odd characteristic, prove over every finite extension `E`:

`|#{(x,y)∈E²:y²=f(x)}−#E+χ_E(lc f)|≤(m−2)√#E`.

This includes the exact contribution of the two geometric points at
infinity and removes the odd-degree restriction in the current sharp
hyperelliptic calibration. General curves remain a separate target.

## Existing inputs

`RHTower/HyperellipticDescent.lean` proves the sharp bound and reciprocal-root
purity for every squarefree odd-degree polynomial. For split even-degree
polynomials, `HyperellipticCharacterSums.sum_quadraticChar_prod_eq_of_even`
already gives an exact inversion at a root. It currently yields the weaker
uncorrected bound `(m−1)√q`; its omitted term should give the exact infinity
correction instead.

`HyperellipticLFunction.quadraticChar_norm` identifies the quadratic character
of a finite extension with that of its norm. A nonsquare in an irreducible
quotient field therefore has nonsquare norm, without an additional norm
surjectivity theorem.

## Missing argument

For a monic squarefree modulus, prove that its quadratic resultant character
on residue polynomials is nontrivial. Choose a nonsquare in one irreducible
factor field and residue one on the complementary factor; Chinese remainder
and resultant multiplicativity should provide a unit with character `−1`.
Multiplication by that unit cancels the complete residue-character sum.

This single cancellation should prove degree-sum vanishing in every degree
at least `m`, and, for even `m`, the exact trivial reciprocal root `1`.
The latter is essential: descent from a splitting field identifies powers
of roots and alone does not identify which root of unity occurs at infinity.
For nonmonic `f`, scaling to monic introduces the explicit character `χ(lc f)`.

Only after those inputs are proved can the Newton trace identity, split
inversion and power-sum descent give the sharp bound. No missing polynomial
character cancellation or unit-root identification may be assumed.
