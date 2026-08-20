import GaloisForLFunctions.HTGeometry.SourceOrderedPairComplexStructure
import GaloisForLFunctions.HTGeometry.SuperPoincareAlgebra

/-!
# Super-Poincare certificates for source-pair polarity

The corpus source-polarity and record-pairing matrices are two unit-momentum supercharges.  Their
ordered product is another odd generator in the negative-momentum real form.  Thus the existing
`Cl(2,0)` source geometry already contains both the `N = 2` generators and their complex-structure
product.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- Source polarity and paired composition form unit-momentum `N = 2`. -/
def sourcePairD1N2 (K : Type*) [Field K] :
    SuperPoincare.D1N2 (Matrix (Fin 2) (Fin 2) K) where
  supercharge0 := recordPolarityMatrix
  supercharge1 := pairRecordMatrix
  momentum := 1
  supercharge0_sq := recordPolarityMatrix_mul_self
  supercharge1_sq := pairRecordMatrix_mul_self
  mixed_anticommutator := by
    rw [recordPolarity_pair_anticommute]
    exact neg_add_cancel _

/-- Their ordered product is an `N = 1` supercharge with momentum `-1`. -/
def sourceOrderedPairD1N1 (K : Type*) [Field K] :
    SuperPoincare.D1N1 (Matrix (Fin 2) (Fin 2) K) where
  supercharge := sourceOrderedPairComplexStructure
  momentum := -1
  supercharge_sq := sourceOrderedPairComplexStructure_sq

end GaloisForLFunctions.HTGeometry
