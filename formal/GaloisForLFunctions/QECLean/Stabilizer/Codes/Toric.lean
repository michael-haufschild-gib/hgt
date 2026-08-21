import GaloisForLFunctions.QECLean.Stabilizer.Codes.Toric.CodeN
import GaloisForLFunctions.QECLean.Stabilizer.Codes.Toric.Chains
import GaloisForLFunctions.QECLean.Stabilizer.Codes.Toric.BoundaryMaps
import GaloisForLFunctions.QECLean.Stabilizer.Codes.Toric.Homology
import GaloisForLFunctions.QECLean.Stabilizer.Codes.Toric.H1Dimension
import GaloisForLFunctions.QECLean.Stabilizer.Codes.Toric.WrappingInvariants
import GaloisForLFunctions.QECLean.Stabilizer.Codes.Toric.AbelianChernSimons
import GaloisForLFunctions.QECLean.Stabilizer.Codes.Toric.KnotChernSimonsBridge
import GaloisForLFunctions.QECLean.Stabilizer.Codes.Toric.OperatorChains
import GaloisForLFunctions.QECLean.Stabilizer.Codes.Toric.ChainOps
import GaloisForLFunctions.QECLean.Stabilizer.Codes.Toric.LogicalCorrespondenceX
import GaloisForLFunctions.QECLean.Stabilizer.Codes.Toric.LogicalCorrespondenceZ
import GaloisForLFunctions.QECLean.Stabilizer.Codes.Toric.DualWrappingInvariants
import GaloisForLFunctions.QECLean.Stabilizer.Codes.Toric.ChainComplex
import GaloisForLFunctions.QECLean.Stabilizer.Codes.Toric.Distance
import GaloisForLFunctions.QECLean.Stabilizer.Codes.Toric.DistanceX
import GaloisForLFunctions.QECLean.Stabilizer.Codes.Toric.DistanceZ
import GaloisForLFunctions.QECLean.Stabilizer.Codes.Toric.StabilizerCode
import GaloisForLFunctions.QECLean.Stabilizer.Codes.Toric.LoopGaugeApplications

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

/-!
# Toric code family
Parametric `L × L` toric code: code + lattice geometry + chain complex +
homology + distance.
-/
