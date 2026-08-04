import GaloisForLFunctions.QECLean.Stabilizer.Codes.RotatedSurface.Three
import GaloisForLFunctions.QECLean.Stabilizer.Codes.RotatedSurface.N
import GaloisForLFunctions.QECLean.Stabilizer.Codes.RotatedSurface.CellComplex
import GaloisForLFunctions.QECLean.Stabilizer.Codes.RotatedSurface.BoundaryMaps
import GaloisForLFunctions.QECLean.Stabilizer.Codes.RotatedSurface.ChainComplex
import GaloisForLFunctions.QECLean.Stabilizer.Codes.RotatedSurface.H1Dimension
import GaloisForLFunctions.QECLean.Stabilizer.Codes.RotatedSurface.Distance
import GaloisForLFunctions.QECLean.Stabilizer.Codes.RotatedSurface.DistanceX
import GaloisForLFunctions.QECLean.Stabilizer.Codes.RotatedSurface.DistanceZ
import GaloisForLFunctions.QECLean.Stabilizer.Codes.RotatedSurface.StabilizerCode

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

/-!
# Rotated surface code family

Distance-3 specialization plus the parametric `L × L` rotated-surface code,
with lattice geometry + chain complex + distance.
-/
