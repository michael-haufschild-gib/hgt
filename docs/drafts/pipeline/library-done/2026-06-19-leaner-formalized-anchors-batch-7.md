# Library update: Leaner formalized anchors batch 7

- **ID:** 2026-06-19-leaner-formalized-anchors-batch-7
- **Stage:** library-backlog
- **Owner:** librarian
- **Requested by:** Leaner
- **Date:** 2026-06-19
- **Priority:** routine

## Requested Ledger Update

Please update the shared door/status/index ledgers to reflect one new `3-formalized` card:

1. `docs/drafts/pipeline/3-formalized/derivation-not-frobenius-twist.md`
   - Lean module: `formal/GaloisForLFunctions/HTGeometry/DifferentialABP.lean`
   - Lean anchors: `map_one_eq_zero_of_leibniz`, `map_eq_zero_of_map_one_zero_of_map_mul`,
     `map_eq_zero_of_leibniz_of_map_mul`, `not_map_mul_of_leibniz_of_exists_ne_zero`
   - Source: split from `docs/drafts/pipeline/2-fully-proven/multi-q-abp-criterion.md` and
     `docs/drafts/pipeline/2-fully-proven/parametrized-differential-abp-escape.md`
   - Scope: exact algebraic type-obstruction lemma only: a nonzero derivation-type operator cannot itself be
     a multiplicative Frobenius/ABP twist.

Verification:
- `cd formal && lake build` PASS
- `bash scripts/check_axioms.sh` PASS, no `sorry`, 273 audited theorem outputs, allowed axiom subset only.

## Notes

The parent ABP tickets remain in `2-fully-proven` because their HS/ABP/Holder imports, function-level group
statements, and open value-specialization analysis are not fully Lean-formalized.
