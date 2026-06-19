# Library ledger update — Leaner formalized anchors batch 14

- **ID:** 2026-06-19-leaner-formalized-anchors-batch-14
- **Stage:** library-backlog
- **Owner:** librarian
- **Requested by:** Leaner
- **Date:** 2026-06-19
- **Priority:** routine

## Requested Ledger Update
Record the following new `3-formalized` card in the shared door/status/index ledgers:

- `docs/drafts/pipeline/3-formalized/sato-tate-chebyshev-orthogonality.md`

## Lean Certificate
- Lean module: `formal/GaloisForLFunctions/SatoTateMoment.lean`
- Theorem anchors:
  - `integral_cos_nat_mul`
  - `integral_sin_succ_mul_sin`
  - `satoTate_moment`
  - `integral_sin_mul_sin`
  - `satoTate_orthonormal`
- Source card: split from `docs/drafts/pipeline/2-fully-proven/g4-over-fq-deligne-katz.md` §1 and the function-field G4/Sato-Tate angle face.
- Scope: Sato-Tate measure-side Chebyshev moment orthogonality only.

## Verification
- Scratch name check: PASS for all five Sato-Tate anchors.
- Scratch axiom check: PASS; standard mathlib axioms only.
- `cd formal && lake build`: PASS.
- `bash scripts/check_axioms.sh`: PASS, no sorry; audit remains 273 theorem outputs.

## Notes
- Leaner also corrected the metadata header of `docs/drafts/pipeline/2-fully-proven/stieltjes-exponential-period-realization.md` from `1-in-progress` to `2-fully-proven`, matching its folder and gates.
- The parent `g4-over-fq-deligne-katz` card remains in `2-fully-proven`: Deligne-Katz monodromy, Katz-Sarnak equidistribution/prime averages, symmetric-power `L`-function analytic input, and the Tannakian weight/angle exact sequence are not fully Lean-formalized.
- The `stieltjes-exponential-period-realization` card remains in `2-fully-proven`: no Lean formalization was claimed for its analytic exponential-period construction.
