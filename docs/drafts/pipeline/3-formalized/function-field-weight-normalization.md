# Function-field weight normalization

- **ID:** function-field-weight-normalization
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Priority:** FOUNDATIONAL
- **Source:** split from `../2-fully-proven/g5-over-fq-deligne-unitarity.md` sections 1-2
- **Statement:** For positive `q`, weight `w`, degree `d`, and Frobenius eigenvalue `alpha`, normalizing
  by the weight radius `q^(w*d/2)` has unit norm iff `alpha` lies on the Frobenius weight circle of that
  radius.

## Goal
This banks the scalar modulus algebra behind the function-field G5 recovery: the normalized Frobenius
`u = alpha / q^(w*d/2)` is unitary exactly when `alpha` is on the weight circle. It does not formalize
Poincare duality, sheaves, polarization, Deligne Weil II, `Fix(iota)`, or RH over `F_q`.

## Paper Proof
Let

`R = q^(w*d/2)`.

Since `q > 0`, real powers give `R > 0`. Define the normalized eigenvalue

`u = R^(-1) alpha`.

The norm is homogeneous under positive real scaling:

`|u| = |R^(-1) alpha| = R^(-1) |alpha|`.

Therefore

`|u| = 1  iff  R^(-1) |alpha| = 1  iff  |alpha| = R`.

Thus normalized Frobenius is unitary exactly on the Frobenius weight circle.

## Gates
- [x] 0 -> 1  in-progress: scalar weight-radius normalization extracted from the function-field G5 card.
- [x] 1 -> 2  fully-proven: paper proof above by positivity of `q^(w*d/2)` and norm homogeneity.
- [x] 2 -> 3  formalized: Lean definitions `functionFieldWeightRadius`,
  `functionFieldWeightNormalize`, and theorem `functionFieldWeightNormalize_norm_eq_one_iff` in
  `formal/GaloisForLFunctions/BoundaryModulus.lean`; scratch `#check`/`#print axioms`, `lake build`, and
  `scripts/check_axioms.sh` pass.
- [ ] 3 -> 4  publication-ready: cite as the scalar weight-circle certificate for G5 over function fields.

## Log
- 2026-06-19 - Leaner split this exact scalar normalization theorem from `g5-over-fq-deligne-unitarity`.
  The parent card remains in `2-fully-proven` because the function-field specialization, Poincare duality,
  polarization, Deligne purity import, `Fix(iota)` identification, and RH-over-`F_q` theorem are not fully
  Lean-formalized.
