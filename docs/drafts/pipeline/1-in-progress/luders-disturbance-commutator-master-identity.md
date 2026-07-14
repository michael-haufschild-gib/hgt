# Lueders disturbance and cutoff-commutator master identity

- **ID:** `luders-disturbance-commutator-master-identity`
- **Stage:** 1-in-progress
- **Type:** PHYSICS VALUE RELATION / FORMAL BRIDGE
- **Scientific status:** `[BRIDGE] [CORPUS-USEFUL] [NOT AN RH PROOF]`
- **Physics source:** Y. Liu and J. B. DeBrota, *Relating measurement disturbance, information
  and orthogonality*, arXiv:2105.02074 (Lueders-rule disturbance); Z. Zhu, S. Karnik,
  M. A. Davenport, J. Romberg, and M. B. Wakin, *The Eigenvalue Distribution of Discrete
  Periodic Time-Frequency Limiting Operators*, arXiv:1707.05344 (time/frequency projection
  products and prolate transition spectrum).
- **Lean target:** `formal/GaloisForLFunctions/RHTower/SoninLudersPinching.lean`

## Claim

Let `e` be a self-adjoint idempotent and `X` a self-adjoint bounded operator.  Write

```text
D_e(X) = e X e + (1-e) X (1-e),
delta_e(X) = X - D_e(X),
C_e(X) = X e - e X.
```

Then the positive master operators agree exactly:

```text
delta_e(X)^* delta_e(X) = C_e(X)^* C_e(X).
```

Consequently every state `psi` has the exact value identity

```text
||delta_e(X) psi||^2 = ||C_e(X) psi||^2.
```

## Paper proof

Put `A=(1-e)Xe` and `B=eX(1-e)`.  Idempotence gives `A^2=B^2=0`, while direct expansion gives

```text
delta_e(X)=A+B,
C_e(X)=A-B.
```

Hence `delta_e(X)^2=AB+BA=-C_e(X)^2`.  Self-adjointness of `e,X` gives
`delta_e(X)^*=delta_e(X)` and `C_e(X)^*=-C_e(X)`, proving the master-operator identity.  The
state value follows from the standard master-constraint expectation formula.

## Corpus value

1. Strengthens the existing compactness equivalence between Lueders disturbance and essential
   cutoff commutation to literal equality of their positive master constraints.
2. Eliminates any comparison constant in statewise energy, Ward-value, trace, or singular-value
   consumers of the master operator.
3. Applies directly to the physical/Fourier orthogonal projections defining the Sonin prolate
   geometry.
4. Applies directly to `archimedeanPrimeEulerGram` and
   `archimedeanBoundaryCarrierProjection`, with no positivity of aperture or lower bound on the
   prime parameter.
5. Is purely static constraint mathematics; it introduces no carrier flow.

## Lean surface

- `ccmCommutator_eq_crossBoundary_sub_upperBoundary`
- existing `crossBoundary_mul_crossBoundary`
- `upperBoundary_mul_upperBoundary`
- `ludersDisturbance_sq_eq_neg_ccmCommutator_sq`
- `star_mul_self_ludersDisturbance_eq_cutoffCommutator`
- `quantumMasterConstraint_ludersDisturbance_eq_cutoffCommutator`
- `norm_ludersDisturbance_apply_sq_eq_norm_cutoffCommutator_apply_sq`
- `quantumMasterConstraint_starProjection_ludersDisturbance_eq_cutoffCommutator`
- `quantumMasterConstraint_archimedeanPrimeEuler_ludersDisturbance_eq_commutator`
- `norm_archimedeanPrimeEuler_ludersDisturbance_apply_sq_eq_commutator`

## Verification boundary

The proof is exact noncommutative algebra.  Under the current no-computation instruction the Lean
source has been manually reviewed but not built, linted, or axiom-audited.  Promotion to stage 3
requires one later targeted file check.

## Gates

- [x] primary quantum-measurement source identified
- [x] primary signal-processing/time-frequency source identified
- [x] exact relation proved on paper
- [x] direct RHTower consumers identified
- [x] Lean source added and manually reviewed
- [ ] targeted Lean verification when computation is permitted
