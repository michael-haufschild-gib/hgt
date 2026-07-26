import GaloisForLFunctions.RHTower.XiSpectralFamilyGraded
import GaloisForLFunctions.RHTower.XiSpectralFamilyOnLine
import GaloisForLFunctions.RHTower.XiSpectralFamilyRH
import GaloisForLFunctions.HTGeometry.AbstractSpectralGraded

/-!
# The graded criterion on a vertical line

Unified with the index-free layer.  `RHTower.SpectralFamily` is by definition
`HTGeometry.AbstractSpectralFamily XiZeroCopy` (see `RHTower.XiSpectralFamily`), so every statement
this module used to re-prove for the Xi divisor is already available as the corresponding abstract
law in `GaloisForLFunctions.HTGeometry.AbstractSpectralGraded`.  The module survives only as an import node of the RH
tower; it adds no Xi-specific content.

Former Xi-indexed statements and their index-free replacements:

- `im_le_of_line_growth`
- `abs_im_le_of_line_growth`
- `abs_im_le_of_line_growth_all`
- `norm_traceC_le_of_abs_im_le`
- `abs_im_le_iff_exists_line_growth`
- `im_eq_zero_of_subexponential`
-/
