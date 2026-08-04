import GaloisForLFunctions.QECLean.Stabilizer.Codes.Small.Shor9
import GaloisForLFunctions.QECLean.Stabilizer.Codes.Small.Steane7
import GaloisForLFunctions.QECLean.Stabilizer.Codes.Small.Steane7Distance
import GaloisForLFunctions.QECLean.Stabilizer.Codes.Small.Steane7TransversalGates
import GaloisForLFunctions.QECLean.Stabilizer.Codes.Small.FourQubit_4_2_2
import GaloisForLFunctions.QECLean.Stabilizer.Codes.Small.QuantumHamming
import GaloisForLFunctions.QECLean.Stabilizer.Codes.Small.FiveQubit_5_1_3
import GaloisForLFunctions.QECLean.Stabilizer.Codes.Small.CSS_4_1_2
import GaloisForLFunctions.QECLean.Stabilizer.Codes.Small.SixQubit_6_2_2

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

/-!
# Small concrete codes

Single-instance stabilizer codes: Shor's [[9,1,3]], Steane [[7,1,3]] (with
transversal gates), the [[4,2,2]] code, quantum Hamming, the [[5,1,3]]
perfect code (the first non-CSS code in the repo), the [[4,1,2]]
LNCY CSS detection code, and Knill's C_6 [[6,2,2]] CSS detection code.
-/
