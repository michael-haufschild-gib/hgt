# Triangular root coefficients unfold arithmetic cells

- **Stage:** 1-in-progress
- **Parent:** [Arithmetic unfolding](finite-field-eisenstein-unfolding.md).
- **Target:** Derive each actual arithmetic Bruhat-cell integral by iterated
  scalar periodization in the audited product domain.

## Candidate mechanism

For a positive unipotent matrix `u=(a,b;c,d)` and an upper polynomial `p`,
the upper Gauss coordinate of `u U(p)` is `(ap+b)/(cp+d)`. Its coefficient
of degree `n` is `b_n+p_n` plus terms involving earlier free coordinates
and earlier coefficients of `p`. Here `a₀=d₀=1`, `c₀=0`, and the determinant
recursion makes `d_n` independent of `b_n`.

For a lower polynomial with `p₀=0`, the lower Gauss coordinate of `u L(p)`
is `(c+dp)/(a+bp)`. Its degree-`n` coefficient is `c_n+p_n` plus earlier
terms. The zero constant coefficient prevents dependence on `a_n`.

Thus summation over rational polynomial coefficients and integration over
the selected domain coordinates should unfold successively by the audited
scalar additive formula. All unused domain coordinates have total mass one.
This does not assert a Gauss-coordinate map from the nonnormal quotient.

## Required proofs

- Compatibility of polynomial/Weyl representatives with diagonal field maps
  and exhaustive parametrization of actual arithmetic cells.
- The residual Borel factor after Weyl conjugation has trivial character,
  including its central coordinate. The expected tame correction is one
  because the relevant power-series diagonal has constant coefficient one.
- Finite-coordinate measurability, Tonelli and resulting actual cell integral.

The listed obligations remain unproved. No relative quotient or Jacobian is assumed.

The [Gauss coefficient laws](../3-formalized/unipotent-gauss-defects-use-only-earlier-free-coefficients.md)
are formalized: for an actual product, each upper or lower Gauss coordinate
is the sum of the current free coefficients plus a correction depending
only on strict input prefixes. Direct Lean and transitive axiom audits passed.

[Polynomial-head uniqueness and lifting modulo Borel](../3-formalized/affine-polynomial-cell-heads-are-unique.md)
passed direct Lean and axiom audits. This does not establish triviality of
the residual Borel character.
