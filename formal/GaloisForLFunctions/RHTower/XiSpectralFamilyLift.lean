import GaloisForLFunctions.RHTower.XiSpectralFamilyOnLine
import GaloisForLFunctions.HTGeometry.AbstractSpectralRigidity

/-!
# Lifting the points below a cut

Unified with the index-free layer.  `RHTower.SpectralFamily` is by definition
`HTGeometry.AbstractSpectralFamily XiZeroCopy` (see `RHTower.XiSpectralFamily`), so every statement
this module used to re-prove for the Xi divisor is already available as the corresponding abstract
law in `GaloisForLFunctions.HTGeometry.AbstractSpectralRigidity`.  The module survives only as an import node of the RH
tower; it adds no Xi-specific content.

Former Xi-indexed statements and their index-free replacements:

- `below`
- `finite_below`
- `below_lineConj -> below is stable under `inv` by `conj_stable``
- `lift`
-/
