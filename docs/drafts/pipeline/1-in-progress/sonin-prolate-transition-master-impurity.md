# Sonin prolate transition master impurity

- **ID:** `sonin-prolate-transition-master-impurity`
- **Stage:** 1-in-progress
- **Type:** AUDIO/QUANTUM VALUE RELATION / FORMAL BRIDGE
- **Scientific status:** `[BRIDGE] [CORPUS-USEFUL] [NOT AN RH PROOF]`
- **Physics/audio source:** A. Israel and A. Mayeli, *On the Eigenvalue Distribution of
  Spatio-Spectral Limiting Operators in Higher Dimensions*, arXiv:2301.09616; A. Bonami and
  A. Karoui, *Spectral Decay of Time and Frequency Limiting Operator*, arXiv:1509.02646.
- **Lean target:** `formal/GaloisForLFunctions/RHTower/SoninLudersPinching.lean`

## Claim

For orthogonal projections `P,R`, put

```text
T = R P R,
A = (1-R) P R.
```

Then

```text
T - T^2 = A^* A.
```

In the Sonin corpus, `T` is exactly `soninAlternatingBlock` and `A` is the existing
`crossBoundary R P`.

## Paper proof

Self-adjointness and idempotence of `P,R` give

```text
A^*A = R P (1-R) (1-R) P R
      = R P (1-R) P R
      = R P R - R P R P R
      = T - T^2.
```

Thus every state `psi` satisfies

```text
Re <psi,(T-T^2)psi> = ||A psi||^2.
```

## Corpus value

1. Identifies the prolate/time-frequency transition region as an existing positive
   `quantumMasterConstraint`, not merely as the norm gap of an alternating block.
2. Removes any separate positivity premise for the operator `T-T^2` and gives its exact kernel
   meaning: zero value is precisely zero physical/Fourier transition residual on that state.
3. Supplies a source-native positive defect for the strict-contraction and Sonin resolvent layer.
4. Does not prove the live per-polynomial aperture Rayleigh comparison.  Writing that quotient as
   a Born expectation only repackages the missing spectral-measure comparison, so no such wrapper
   was added.

## Lean surface

- `star_mul_self_crossBoundary_eq_compression_sub_sq`
- `quantumMasterConstraint_crossBoundary_eq_compression_sub_sq`
- `soninAlternatingBlock_sub_sq_eq_quantumMasterConstraint_transition`
- `re_inner_soninAlternatingBlock_sub_sq_eq_norm_transition`
- `physicalState_soninAlternatingBlock_sub_sq_iff_transition`

## Verification boundary

The proof is exact projection algebra.  Under the current no-computation instruction the Lean
source has been manually reviewed but not built, linted, or axiom-audited.  Promotion to stage 3
requires one later targeted file check.

## Gates

- [x] primary time-frequency sources identified
- [x] exact relation proved on paper
- [x] direct Sonin alternating-block consumer identified
- [x] Lean source added and manually reviewed
- [ ] targeted Lean verification when computation is permitted
