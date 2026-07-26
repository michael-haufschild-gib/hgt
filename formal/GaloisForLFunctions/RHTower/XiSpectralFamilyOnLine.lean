import GaloisForLFunctions.RHTower.XiSpectralFamilyShell
import GaloisForLFunctions.RHTower.XiPoissonBottomOnLine
import GaloisForLFunctions.HTGeometry.AbstractSpectralRigidity

/-!
# Vertical-line rigidity for an admissible family

Unified with the index-free layer.  `RHTower.SpectralFamily` is by definition
`HTGeometry.AbstractSpectralFamily XiZeroCopy` (see `RHTower.XiSpectralFamily`), so every statement
this module used to re-prove for the Xi divisor is already available as the corresponding abstract
law in `GaloisForLFunctions.HTGeometry.AbstractSpectralRigidity`.  The module survives only as an import node of the RH
tower; it adds no Xi-specific content.

Former Xi-indexed statements and their index-free replacements:

- `bottomShell_regroup`
- `im_nonpos_of_line_bound`
- `im_eq_zero_of_line_bound`
-/
