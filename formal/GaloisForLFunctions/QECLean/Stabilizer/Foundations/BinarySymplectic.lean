import GaloisForLFunctions.QECLean.Stabilizer.Foundations.BinarySymplectic.Core
import GaloisForLFunctions.QECLean.Stabilizer.Foundations.BinarySymplectic.SymplecticInner
import GaloisForLFunctions.QECLean.Stabilizer.Foundations.BinarySymplectic.CheckMatrix
import GaloisForLFunctions.QECLean.Stabilizer.Foundations.BinarySymplectic.CheckMatrixDecidable

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

/-!
# Binary symplectic representation and check matrix (Foundations)

Pure binary-symplectic algebra. Re-exports:

- **Core**: `PauliOperator.toSymplecticSingle`, `NQubitPauliOperator.toSymplectic`
- **SymplecticInner**: `symplecticInner`, `commutes_iff_symplectic_inner_zero`, `toSymplectic_add`
- **CheckMatrix**: `NQubitPauliGroupElement.checkMatrix`, `rowsLinearIndependent`
- **CheckMatrixDecidable**: `Decidable (rowsLinearIndependent L)` and `rowsLinearIndependent_iff_forall`

For the stabilizer-aware bridge content (`IndependentEquiv`,
`SymplecticOrthogonal`, `SymplecticSpan`, `WeightTwoInSpan`, `SupportLemmas`),
see `QEC.Stabilizer.Framework.Symplectic`.
-/
