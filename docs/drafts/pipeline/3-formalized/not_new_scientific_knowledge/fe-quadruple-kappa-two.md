# FE quadruple carrier negative inertia two

- **ID:** fe-quadruple-kappa-two
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean), split from the finite carrier/off-line-zero inertia ledger
- **Priority:** FOUNDATIONAL
- **Source:** `formal/GaloisForLFunctions/FECarrier.lean`; row #32 finite carrier inertia; `../1-in-progress/archimedean-weil-ii-bedrock.md`
- **Statement:** For one off-line zero representative `t0` with `0 < Im(t0)` and `Re(t0) != 0`, the functional-equation closure gives two upper-half-plane conjugate-pair representatives `t0` and `-conj(t0)`. In the finite FE-faithful carrier with those two representatives and no collisions with the sample points, every negative-definite subspace has complex dimension at most `2`, and there exists a negative-definite subspace of dimension `2`. Hence one FE quadruple contributes negative inertia exactly `2`.

## Paper Proof

Let the two upper-half-plane pole representatives be
`t = ![t0, -conj(t0)]`. The hypotheses `0 < Im(t0)` and `Re(t0) != 0` imply:

1. both entries of `t` have positive imaginary part, since `Im(-conj(t0)) = Im(t0)`;
2. the two entries are distinct, because `t0 = -conj(t0)` would force `Re(t0) = 0`.

The finite carrier for two conjugate pairs has the factored Pick form
`sum_i w_i w_i^* - sum_i u_i u_i^*`, where
`w_i(j) = (conj(t_i)-z_j)^(-1) + (t_i-z_j)^(-1)` and
`u_i(j) = (conj(t_i)-z_j)^(-1) - (t_i-z_j)^(-1)`.

The collision hypotheses say neither `t_i` nor `conj(t_i)` equals a sample point `z_j`, and `z` is injective.
Therefore the already-certified finite carrier theorem
`multiPair_carrier_exact_neg_inertia`, applied with `k = 2`, gives exactly:

- any subspace on which this Pick form is negative definite has dimension `<= 2`;
- some subspace of dimension `2` is negative definite.

This is precisely negative inertia `2` for the FE quadruple.

## Lean Certificate

- Lean theorem: `GaloisForLFunctions.fe_quadruple_kappa_two`
- File: `formal/GaloisForLFunctions/FECarrier.lean`
- Axiom audit: standard/mathlib axioms only (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`.

Verification:

```bash
cd formal && lake build GaloisForLFunctions
bash scripts/check_axioms.sh
```

## Gates

- [x] 0 -> 1 in-progress: FE quadruple carrier statement isolated from the finite inertia ledger.
- [x] 1 -> 2 fully-proven: paper proof above, reducing the two-pair FE quadruple to the exact finite carrier inertia theorem.
- [x] 2 -> 3 formalized: `fe_quadruple_kappa_two` imports through `GaloisForLFunctions`; included in `scripts/check_axioms.sh`.
- [ ] 3 -> 4 publication-ready: include as the FE-doubling finite carrier certificate.

## Log

- 2026-06-19 — Leaner added this exact split ticket and axiom-audit coverage for `fe_quadruple_kappa_two`. This does not claim the infinite xi carrier or RH; it is the finite FE quadruple carrier inertia theorem only.
