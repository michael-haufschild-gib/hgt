import GaloisForLFunctions.RHTower.XiSpectralFamilyDecay
import GaloisForLFunctions.RHTower.XiPoissonVerticalSplit
import GaloisForLFunctions.HTGeometry.AbstractSpectralShell

/-!
# The bottom shell of an admissible family

Unified with the index-free layer.  `RHTower.SpectralFamily` is by definition
`HTGeometry.AbstractSpectralFamily XiZeroCopy` (see `RHTower.XiSpectralFamily`), so every statement
this module used to re-prove for the Xi divisor is already available as the corresponding abstract
law in `GaloisForLFunctions.HTGeometry.AbstractSpectralShell`.  The module survives only as an import node of the RH
tower; it adds no Xi-specific content.

Former Xi-indexed statements and their index-free replacements:

- `bottomShell`
- `mem_bottomShell`
- `mem_bottomShell_lineConj -> mem_bottomShell_inv`
- `aboveBottom`
- `mem_aboveBottom`
- `exists_secondHeight`
- `bottomShellSum`
- `aboveBottomSum`
- `bottomShellSum_eq`
- `traceC_vertical_split`
- `exp_bottomHeight_mul_norm_aboveBottomSum_le`
-/
