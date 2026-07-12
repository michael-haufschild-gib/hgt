# Joint Hurwitz analytic-continuation removal

- **ID:** `joint-hurwitz-analytic-continuation-removal`
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Scientific status:** `[CONJECTURE] [OPEN CORE: CONCRETE CONTINUATION IN THE SHIFT VARIABLE]`
- **Statement:** The joint differential-algebraic-independence theorem for
  $a\mapsto\zeta(s_j,a)$ holds for every finite family for which
  $1,(s_j)_j$ is linearly independent over $\mathbb Q$, with no half-plane restriction on the
  exponents.

## Goal

Replace the convergence-half-plane model by a concrete analytically continued Hurwitz function in
the complex shift variable and prove the same monodromy-grid and Vandermonde conclusion without
additional hypotheses or a property interface.

## Gates

- [x] 0 → 1 in-progress: well-posed, exact continuation construction selected, local monodromy
  target identified
- [ ] 1 → 2 fully-proven: complete continuation construction and unrestricted paper proof
- [ ] 2 → 3 formalized: unrestricted Lean capstone, target build green, formal lint green, axioms
  audited
- [ ] 3 → 4 publication-ready: unrestricted theorem and proof incorporated in the standalone paper

## Approach

Use a finite Taylor-subtracted Hurwitz series at the reference shift $a=1$.  For a sufficiently
large subtraction order $K$, subtract the first $K+1$ Taylor terms of
$(m+a)^{-s}$ at $a=1$ termwise and restore them with mathlib's meromorphically continued real-shift
Hurwitz values.  Rational independence excludes every pole $s+r=1$ that can occur in the finite
restoration.  The resulting concrete function must be proved to:

1. agree with the normally convergent series when $\operatorname{Re}s>1$;
2. be holomorphic in $a$ on the upper half-plane;
3. satisfy the shift-derivative ladder;
4. have, near every $a=-n$, the exact decomposition $(a+n)^{-s}$ plus a single-valued holomorphic
   tail.

These four facts let the existing monodromy-grid-density and block-Vandermonde proof run unchanged.

## Positive boundary statement

The existing theorem is the zero-subtraction chamber of this construction.  Completing the finite
regularization promotes the same value-relation law from the convergence chamber to every
nonresonant exponent family.
