# Finite-index Mautner rigidity for the Haar successor

- **ID:** HAAR-FINITE-INDEX-MAUTNER
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Parent:** [O5](weil-positivity-five-structural-mechanisms.md)
- **Statement:** A Hermitian kernel on `Aff(ℚ)` with nonzero Haar successor `c·1_ℤ` and dilation correlation continuous at the identity has infinite negative index.

## Mathematical issue

The proved obstruction `negIndex_eq_top_of_weil_haarSuccessor` assumes Hecke support. Removing that support assumption would also obstruct every adelic carrier whose restriction has these two readings. Weil's scalar dilation correlation already has the required continuity.

For a Haar successor, all vectors `v_{b+n}−v_b`, with `b∈ℚ` and `n∈ℤ`, span a totally isotropic translation-invariant space. Finite negative index bounds its dimension in the nondegenerate kernel quotient. The analogous radical of the dilation-cyclic space is also finite-dimensional. These are the only directions invisible to the positive-kernel Mautner argument.

The unresolved step is controlling those isotropic directions from scalar dilation continuity. Continuity of mixed coefficients must be proved; it cannot be added as a premise. A counterexample with finite isotropic transport would instead identify a possible carrier beyond Hecke support.

No paper proof or Lean theorem is claimed. The Hecke-supported no-go does not settle this conjecture or O5.
