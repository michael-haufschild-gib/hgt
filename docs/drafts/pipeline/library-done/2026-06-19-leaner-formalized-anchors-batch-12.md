# Library update: Leaner formalized anchors batch 12

- **ID:** 2026-06-19-leaner-formalized-anchors-batch-12
- **Stage:** library-backlog
- **Owner:** librarian
- **Requested by:** Leaner
- **Date:** 2026-06-19
- **Priority:** routine

## Requested Ledger Update

Please update the shared door/status/index ledgers to reflect two new `3-formalized` cards:

1. `docs/drafts/pipeline/3-formalized/boundary-modulus-critical-line.md`
   - Lean modules: `formal/GaloisForLFunctions/Core.lean`, `formal/GaloisForLFunctions/BoundaryModulus.lean`
   - Lean anchors: `norm_cpow_eq_critical_iff`, `norm_inv_smul_eq_one_iff`,
     `boundaryUnitNormalize_norm_eq_one_iff`, `diagonalBoundary_unit_norm_iff`
   - Source: split from `docs/drafts/pipeline/2-fully-proven/g5-over-fq-deligne-unitarity.md`
   - Scope: exact scalar fixed-modulus/critical-line floor only.

2. `docs/drafts/pipeline/3-formalized/unitary-satake-trace-interval.md`
   - Lean module: `formal/GaloisForLFunctions/SatakeInterval.lean`
   - Lean anchors: `satake_trace_eq_two_mul_re`, `satake_trace_im`,
     `satake_trace_re_mem_Icc`, `symPower_trace_norm_le`
   - Source: split from `docs/drafts/pipeline/2-fully-proven/explicit-formula-as-constraint.md` §3 and
     `docs/drafts/pipeline/2-fully-proven/g4-over-fq-deligne-katz.md` §2
   - Scope: exact unitary Satake trace interval / symmetric-power norm bound only.

Verification:
- Scratch name checks and `#print axioms` PASS for the cited Lean names.
- `cd formal && lake build` PASS.
- `bash scripts/check_axioms.sh` PASS, no `sorry`, 273 audited theorem outputs, allowed axiom subset only.

## Notes

The parent cards remain in `2-fully-proven`: G5-over-`F_q` still needs function-field specialization,
Frobenius weight circle, polarization, and Deligne purity formalization; `explicit-formula-as-constraint`
still needs formal/import wrappers for the Weil explicit formula, DeWitt pairing, signature, and RH positivity.
