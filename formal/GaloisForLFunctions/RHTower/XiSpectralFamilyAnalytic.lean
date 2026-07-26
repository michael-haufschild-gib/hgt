import GaloisForLFunctions.RHTower.XiSpectralFamily
import GaloisForLFunctions.RHTower.XiPoissonTraceAnalytic
import GaloisForLFunctions.HTGeometry.AbstractSpectralFamily

/-!
# Analyticity and shell structure of an admissible family

Unified with the index-free layer.  `RHTower.SpectralFamily` is by definition
`HTGeometry.AbstractSpectralFamily XiZeroCopy` (see `RHTower.XiSpectralFamily`), so every statement
this module used to re-prove for the Xi divisor is already available as the corresponding abstract
law in `GaloisForLFunctions.HTGeometry.AbstractSpectralFamily`.  The module survives only as an import node of the RH
tower; it adds no Xi-specific content.

Former Xi-indexed statements and their index-free replacements:

- `differentiable_term`
- `norm_term_le_on_box`
- `differentiableOn_traceC_box`
- `differentiableAt_traceC`
- `analyticOnNhd_traceC`
- `exists_min_re_of_nonempty`
- `cut`
- `mem_cut`
- `cut_lineConj -> cut_inv`
- `finite_cut_shell`
-/
