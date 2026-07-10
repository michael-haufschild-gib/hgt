# Sonin--Perron support transfer and coherence obstruction

- **ID:** sonin-perron-support-transfer-formal
- **Stage:** 3-formalized
- **Status:** `[PROVED, Lean]`
- **Date:** 2026-07-10
- **Paper theorem:** `docs/drafts/pipeline/2-fully-proven/new/sonin-perron-support-transfer.md`
- **Lean:** `formal/GaloisForLFunctions/RHTower/SoninPerronSupportTransfer.lean`

## Formal surface

### Logarithmic support and negative source moments

- `HasAELowerSupport`
- `logEvenUnitary_hasAELowerSupport`
- `negativeLogWeight`
- `negativeMellinSourceFun`
- `negativeMellinSource_memLp_and_lpNorm_le`
- `sqrt_integral_norm_sq_eq_lpNorm`

### Normalized Mellin traces

- `logMellinUnitary`
- `negativeMellinSourceLp`
- `negativeMellinSourceLp_ae`
- `negativeMellinL2Trace`
- `negativeMellinL2Trace_norm_le`
- `exp_neg_nat_mul_log_eq_inv_pow`

### Cross-line coherence interface

- `HasCoherentNegativeMellinTraces`
- `HasCoherentNegativeMellinTraces.hasPerronCarrierFlankL2Energy`
- `soninCoherentNegativeMellinTraces_hasPerronCarrierFlankL2Energy`

### Support transfer and obstruction capstones

- `coefficient_index_le_inv_sonin_cutoff`
- `coefficient_support_finite_of_sonin_coherence`
- `not_coherent_of_infinite_coefficient_support`
- `coefficient_eq_zero_of_one_lt_sonin_cutoff`
- `entire_eq_zero_of_one_lt_sonin_cutoff`
- `not_coherent_of_nonzero_one_lt_sonin_cutoff`

The strongest general capstone says that exact cross-line coherence plus finite horizontal carrier
mass forces the coefficient support to be finite at every positive Sonin cutoff.  Infinite support
therefore refutes coherence.  The `q>1` specialization forces the entire carrier itself to vanish.

## Verification

- [x] Target source elaborates directly.
- [x] Targeted Lake build passes (`8499/8499`); no umbrella build was run.
- [x] Principal theorem axiom audit reports only `propext`, `Classical.choice`, and `Quot.sound`.
- [x] Generated API refreshed and `formal_tools.py lint --check-generated` passes.

## Remaining gate

`PerronMellinSeamResidue.lean` now supplies a defect-bearing coherence law and proves that its
knot-normalized Perron coordinates recover the infinite Dirichlet tail. `[OPEN CORE]` Construct the
defect for the target and constrain those coordinates using divisor or cocycle data.
