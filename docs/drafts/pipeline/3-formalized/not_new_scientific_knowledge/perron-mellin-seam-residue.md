# Perron--Mellin seam residues recover the arithmetic tail

- **ID:** perron-mellin-seam-residue-formal
- **Stage:** 3-formalized
- **Status:** `[PROVED, Lean]`
- **Date:** 2026-07-10
- **Paper theorem:** `docs/drafts/pipeline/2-fully-proven/new/perron-mellin-seam-residue.md`
- **Lean:** `formal/GaloisForLFunctions/RHTower/PerronMellinSeamResidue.lean`

## Formal surface

### `L2` Perron probe

- `norm_integral_mul_le_lpNorm_mul_lpNorm`
- `perronEAt_left_flank_memLp_and_lpNorm_le`
- `perron_left_integral_eq_right_integral_of_boundaryEscapeAt`

### Additive seam object

- `HasCrossLineMellinDefect`
- `HasCoherentNegativeMellinTraces.hasCrossLineMellinDefect_zero`
- `negativeMellinSourcePerronCharge`
- `perronMellinSeamResidue`
- `perronMellinSeamCoefficient`

### Source decay

- `negativeMellinSourcePerronCharge_norm_le`
- `soninSourcePerronCharge_norm_le`
- `soninSourcePerronCharge_tendsto_zero`

### Arithmetic recovery capstones

- `coefficient_eq_sourceCharge_add_seamResidue`
- `soninPerronMellinSeamResidue_tendsto_coefficient`
- `soninPerronMellinSeamCoefficient_tendsto_coefficient`
- `soninPerronMellinSeamCoefficient_eventually_ne_zero`
- `soninPerronMellinSeamCoefficient_sub_tendsto_zero`

The strongest capstone says that the knot-normalized Perron coordinate of the cross-line seam defect
converges to `coeff n` whenever `n-delta>q⁻¹`.  Different admissible knot widths give asymptotically
the same coordinate, and a nonzero coefficient gives an eventually nonzero seam witness.

## Verification

- [x] Target source elaborates directly.
- [x] Targeted Lake build passes (`8500/8500`); no umbrella build was run.
- [x] Principal theorem axiom audit reports only `propext`, `Classical.choice`, and `Quot.sound`.
- [x] Generated API refreshed and `formal_tools.py lint --check-generated` passes.

## Remaining gate

`CanonicalPerronMellinSeam.lean` now constructs the unique eventual defect from flank `L2` energy
and proves source-gauge invariance. `[OPEN CORE]` Build an archimedean-completed coefficient
extractor for `xi=archFactor*zeta`, then constrain its coordinates by divisor or cocycle data.
