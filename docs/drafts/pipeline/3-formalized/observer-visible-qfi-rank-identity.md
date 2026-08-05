# Observer-visible QFI rank identity

- **ID:** observer-visible-qfi-rank-identity
- **Stage:** 3-formalized
- **Type:** THEOREM / exact finite-dimensional projective-action rank
- **Status:** `[LEAN-PROVED] [BRIDGE]`
- **Parent:** `../2-fully-proven/observer-visible-local-time-dimension-obstruction.md`

## Exact theorem

For a normalized pure state `psi` and a finite Hermitian generator family
`h_a`, form the real matrix whose `a`th column is the realification of

[
 (h_a-langle h_aangle_psi)psi .
]

Then the pure-state multiparameter quantum Fisher matrix is four times its
real Gram matrix, and therefore

[
 operatorname{rank}_{mathbb R}operatorname{QFIM}_psi(h)
 =
 operatorname{rank}_{mathbb R}
 igl[(h_a-langle h_aangle_psi)psiigr]_a .
]

For every real coefficient vector `x`, the corresponding realified action
vanishes exactly when the assembled Hamiltonian
`H(x)=sum_a x_a h_a` has `psi` as an eigenvector:

[
 T_psi x=0
 iff
 H(x)psi=langle H(x)angle_psipsi .
]

## Lean surface

File:
`formal/GaloisForLFunctions/HTGeometry/ObserverVisibleLocalTimeDimension.lean`

Declarations:

- `QuantumAlg.centeredRealification_gram_apply`
- `QuantumAlg.qfim_eq_four_smul_realification_gram`
- `QuantumAlg.qfim_rank_eq_centeredRealification_rank`
- `QuantumAlg.centeredRealification_mulVec_eq_zero_iff`
- `QuantumAlg.centeredRealification_mulVec_eq_zero_iff_eigenvector`
- `QuantumAlg.observerChannel_subspace_finrank_le`
- `QuantumAlg.observerChannel_subspace_finrank_add_rank_le`
- `QuantumAlg.observerChannel_preimage_finrank_eq`

The module is imported by `GaloisForLFunctions.HTGeometry`.

## Verification

- `lake env lean GaloisForLFunctions/HTGeometry/ObserverVisibleLocalTimeDimension.lean` — passes.
- `lake build GaloisForLFunctions.HTGeometry.ObserverVisibleLocalTimeDimension` — passes.
- Axiom audit reports only `propext`, `Classical.choice`, and `Quot.sound`.

Repository-wide `scripts/formal_tools.py lint` passes.  The earlier transient
umbrella failure for `KleinGordonSwitchedClock` was repaired by the task that
owned that module before the final lint audit.

## Scope

This exact Gram/rank/kernel identity is established QFI linear algebra and is
classified as a `[BRIDGE]`, not new scientific knowledge.  It formalizes the
algebraic spine of the observer obstruction.  The Gaussian tube bound,
fixed-`q` product-state count, and selector-aware no-shortcut upper law are
not claimed here.
