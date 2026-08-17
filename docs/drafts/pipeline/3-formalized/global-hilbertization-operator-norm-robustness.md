# Dimension-independent robust Hilbertization firewall

Stage: 3-formalized

Status: `[LITERATURE] [PAPER-PROVED] [LEAN PROVED] [STRENGTHENED]`

Source: Corollary 4.3 of *Locally Quantum, Globally Non-Hilbertizable* (Zenodo 21982163).

## Exact claim

Every normalized positive-semidefinite block kernel is exactly the Gram kernel of common
orthonormal frames.  For the balanced context anomaly of order `r+3`, every positive-semidefinite
matrix `P` satisfies the dimension-independent operator-norm separation

```text
balancedContextMargin r <= ||C_r - P||op.
```

The lower bound is read by one normalized constant-section reporter and is independent of any
ambient Hilbert-space realization dimension.

## Lean status

`formal/GaloisForLFunctions/HTGeometry/ContextOrderRobustHilbertization.lean`, declarations
`normalizedBlockKernel_posSemidef_iff_exists_orthonormal_frames`,
`balancedContext_psd_separation`, and `balancedContext_operatorNorm_psd_separation`.  Closed without
added axioms.
