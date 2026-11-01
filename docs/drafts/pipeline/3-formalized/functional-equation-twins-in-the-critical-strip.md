# Functional-equation twins in a prescribed critical-strip disk

- **ID:** functional-equation-twins-in-the-critical-strip
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Wall:** Γ15.
- **Statement:** For every `N`, `k` and real `T`, a normalized Dirichlet series matching `ζ³`
  below `N` has a completion with `k` distinct zeros in `|s−(3/4+iT)|<1/8`, the same
  functional equation and principal parts, and absolute convergence on `Re s>3`.

## Proof

Dirichlet uniqueness makes the theta perturbations independent on a real right
ray, hence on the whole plane. The identity theorem preserves independence on
the disk, by `HTGeometry.linearIndependent_restrict_of_entire` and
`HTGeometry.frequently_mem_of_isOpen`. Choose distinct points with invertible
evaluation matrix and solve for a finite combination cancelling completed `ζ³`
at those points. Each perturbation is entire and reflection-even, with coefficients
vanishing below `max(N,2)`, so the principal parts, functional equation, normalization
and coefficient prefix survive. Finite sums preserve convergence on `Re s>3`.

The disk lies strictly between the critical line and `Re s=1`; reflection supplies
the other half. The twin depends on `N`, `k` and `T`; points are chosen within the
disk, not prescribed individually.

Complex coefficients are allowed. No finite-order or `Re s>1` convergence claim
is included.

## Verification

`GaloisForLFunctions.SelbergClass.exists_cubic_twin_with_many_critical_strip_zeros`,
in `formal/GaloisForLFunctions/SelbergClass/FunctionalEquationTwinsWithRightHandZeros.lean`,
passed the leaf check and transitive axiom audit. Only `propext`, `Classical.choice`,
and `Quot.sound` occur. The module is imported by the SelbergClass umbrella.
