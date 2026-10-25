# Kernel-checked first-atom quadrature

- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Statement:** Preserve the five rational first-atom bounds and rank-four Milnor-to-Steinberg surjectivity while replacing native decision proofs by kernel-checked arithmetic.

## Approach

The finite-index complement follows from cardinality. The rational quadrature needs separate
certificates for mesh endpoints and local polynomial integrals, followed by finite-sum bounds.
Keep every existing theorem statement and analytic dependency unchanged. No external numerical
calculation, added mathematical premise, or raised elaboration limit is permitted.

## Verification

- [ ] Replace the finite-index proof.
- [ ] Replace the five rational quadrature checks.
- [ ] Check each changed module with `lake --old env lean` from `formal/`.
- [ ] Audit transitive axioms for the numeric bounds and exported consequences.
- [ ] Confirm umbrella imports and remove scratch artifacts.
