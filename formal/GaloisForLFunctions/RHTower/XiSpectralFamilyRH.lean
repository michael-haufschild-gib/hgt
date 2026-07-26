import GaloisForLFunctions.RHTower.XiSpectralFamilyLift
import GaloisForLFunctions.HTGeometry.AbstractSpectralRigidity

/-!
# Rigidity at every height

Unified with the index-free layer.  `RHTower.SpectralFamily` is by definition
`HTGeometry.AbstractSpectralFamily XiZeroCopy` (see `RHTower.XiSpectralFamily`), so every statement
this module used to re-prove for the Xi divisor is already available as the corresponding abstract
law in `GaloisForLFunctions.HTGeometry.AbstractSpectralRigidity`.  The module survives only as an import node of the RH
tower; it adds no Xi-specific content.

Former Xi-indexed statements and their index-free replacements:

- `lift_pt_of_le`
- `lift_pt_of_lt`
- `im_eq_zero_of_line_bound_all`
- `im_eq_zero_iff_exists_line_bound`
-/
