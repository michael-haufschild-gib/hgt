# Overlap Gram smoothing needs a prime-defect corrector

- **ID:** overlap-gram-defect-corrector
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Statement:** For every fixed overlap `c>1`, eventually in the horizon, the symmetrized Gram smoothing of the actual prime defect is indefinite. Adding `τ D_N((I-G)x)` makes it nonnegative for every vector exactly when `τ≥1/4`.

## Objects and purpose

`G` is the normalized atom Gram matrix of the tilted unit spline at width `c/N`. Write `D_N(x,y)` for the polarization of the actual prime defect and `b_n=1/sqrt(n)` for its ground vector. The candidate reserve is `F_N(x)=D_N(x,Gx)`.

This tests a proposed way to retain the physical Gram inside the arithmetic reserve. It is not the complete Weil form and does not obstruct the whole conductor-confinement route.

## Candidate mechanism

The expected exact positive replacement is

`F_N(x)+(1/4)D_N(x-Gx)=(1/4)D_N(x+Gx)`.

The matrix `I+G` is positive definite. If `(I+G)u=b`, then the right side vanishes. When `Gb` is not proportional to `b`, the vector `u` has positive prime defect, and every smaller correction coefficient fails on this same vector.

For fixed `c>1` and large `N`, the first atom is separated while the final two atoms overlap. Nonnegative autocorrelation then makes `(Gb)_1=b_1` and `(Gb)_N>b_N`, which prevents preservation of the arithmetic ground line.

## Proof obligations

- Verify the exact kernel of the finite prime defect.
- Prove positivity and the stated ground-line failure for the literal normalized atom Gram.
- Prove the sharp correction threshold and its transformed ground line in Lean.

The actual signed Weil reserve, growing-family residual bound, and physical synthesis estimate remain open.
