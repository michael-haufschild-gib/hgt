import GaloisForLFunctions.RHTower.XiSpectralFamilyAnalytic
import GaloisForLFunctions.RHTower.XiHeatShellMinimum
import GaloisForLFunctions.HTGeometry.AbstractSpectralDecay

/-!
# Half-plane decay for an admissible family

Unified with the index-free layer.  `RHTower.SpectralFamily` is by definition
`HTGeometry.AbstractSpectralFamily XiZeroCopy` (see `RHTower.XiSpectralFamily`), so every statement
this module used to re-prove for the Xi divisor is already available as the corresponding abstract
law in `GaloisForLFunctions.HTGeometry.AbstractSpectralDecay`.  The module survives only as an import node of the RH
tower; it adds no Xi-specific content.

Former Xi-indexed statements and their index-free replacements:

- `bottomCopy -> bottomIndex`
- `bottomCopy_min -> bottomIndex_min`
- `bottomHeight`
- `bottomHeight_le`
- `bottomHeight_pos`
- `exp_bottomHeight_mul_traceReal_le`
- `twist`
- `norm_exp_twist`
- `differentiableOn_twist`
- `norm_twist_le`
- `norm_twist_imaginary_ray`
- `norm_twist_real_ray`
- `norm_twist_le_of_line_bound`
- `norm_traceC_le_of_line_bound`
-/
