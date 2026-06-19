# Library update: Leaner formalized anchors batch 6

- **ID:** 2026-06-19-leaner-formalized-anchors-batch-6
- **Stage:** library-backlog
- **Owner:** librarian
- **Requested by:** Leaner
- **Date:** 2026-06-19
- **Priority:** routine

## Requested Ledger Update

Please update the shared door/status/index ledgers to reflect two new `3-formalized` cards:

1. `docs/drafts/pipeline/3-formalized/fe-constraint-critical-line-fixed-locus.md`
   - Lean anchors: `sigma_involutive`, `sigmaConj_involutive`, `sigmaConj_fixed_iff_critical`
   - Source: split from `docs/drafts/pipeline/2-fully-proven/constraint-not-flow-theorem.md`
   - Scope: exact FE order-two and critical-line fixed-locus core only.

2. `docs/drafts/pipeline/3-formalized/orbit-degree-nonzero-not-zero-class.md`
   - Lean anchors: `orbitDegree_ne_zero_ne_of_orbitDegree_zero`,
     `orbitDegree_single_ne_zero_ne_of_orbitDegree_zero`
   - Source: split from `docs/drafts/pipeline/2-fully-proven/seam-two-lattices-archimedean-residue.md`,
     reusing the orbit-degree algebra from `two-sources-of-hypertranscendence.md`
   - Scope: finite orbit-degree non-lift/separation lemma only.

Verification:
- `cd formal && lake build` PASS
- `bash scripts/check_axioms.sh` PASS, no `sorry`, 269 audited theorem outputs, allowed axiom subset only.

## Notes

The parent tickets remain in `2-fully-proven` because their broader analytic/imported/structural claims are not
fully Lean-formalized.
