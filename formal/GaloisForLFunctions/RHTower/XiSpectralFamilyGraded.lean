import GaloisForLFunctions.RHTower.XiSpectralFamilyDecay
import GaloisForLFunctions.HTGeometry.AbstractSpectralGraded

/-!
# The graded envelope of an admissible family

Unified with the index-free layer.  `RHTower.SpectralFamily` is by definition
`HTGeometry.AbstractSpectralFamily XiZeroCopy` (see `RHTower.XiSpectralFamily`), so every statement
this module used to re-prove for the Xi divisor is already available as the corresponding abstract
law in `GaloisForLFunctions.HTGeometry.AbstractSpectralGraded`.  The module survives only as an import node of the RH
tower; it adds no Xi-specific content.

Former Xi-indexed statements and their index-free replacements:

- `gtwist`
- `norm_gtwist`
- `differentiableOn_gtwist`
- `norm_gtwist_le`
- `norm_twist_le_of_line_growth`
- `norm_traceC_le_of_line_growth`
-/
