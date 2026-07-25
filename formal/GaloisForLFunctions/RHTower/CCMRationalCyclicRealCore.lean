import GaloisForLFunctions.RHTower.KRealCyclicWord
import GaloisForLFunctions.RHTower.CCMRationalRealCrossedProduct

/-!
# Cyclic-word Real structure for the algebraic rational CCM source

The finite-support rational CCM crossed-product involution is unital, multiplicative, and
even. Therefore it acts componentwise in every algebraic cyclic degree and commutes with
internal faces, the last face, degeneracies, and cyclic rotation.

This is the pure-tensor algebraic core of the future completed CCM cyclic-module lift. No
Schwartz topology, bornology, trace-class completion, cyclic homology, positivity, zero
spectrum, or Riemann-hypothesis premise occurs.
-/

noncomputable section

namespace GaloisForLFunctions
namespace RHTower

/-- Even Real algebra structure on the finite-support rational CCM crossed product. -/
def ccmRationalCrossedProductKRealAlgebra :
    KRealAlgebraStructure CCMRationalAlgebraicCrossedProduct where
  sigma := ccmRationalCrossedProductRealStructureₛₗ
  sq F := by
    simpa [kRealParityAction] using
      ccmRationalCrossedProductRealStructure_sq F
  map_one := ccmRationalCrossedProductRealStructure_one
  map_mul := ccmRationalCrossedProductRealStructure_mul

/-- The rational CCM cyclic-word Real structure is involutive in every degree. -/
theorem ccmRationalCyclicWordRealStructure_sq
    (w : List CCMRationalAlgebraicCrossedProduct) :
    ccmRationalCrossedProductKRealAlgebra.cyclicWordSigma
      (ccmRationalCrossedProductKRealAlgebra.cyclicWordSigma w) = w :=
  ccmRationalCrossedProductKRealAlgebra.cyclicWordSigma_sq w

/-- Rational CCM componentwise Real action commutes with cyclic rotation. -/
theorem ccmRationalCyclicWordRealStructure_rotate
    (w : List CCMRationalAlgebraicCrossedProduct) :
    ccmRationalCrossedProductKRealAlgebra.cyclicWordSigma
      (KRealAlgebraStructure.cyclicWordRotate w) =
    KRealAlgebraStructure.cyclicWordRotate
      (ccmRationalCrossedProductKRealAlgebra.cyclicWordSigma w) :=
  ccmRationalCrossedProductKRealAlgebra.cyclicWordSigma_rotate w

/-- Rational CCM componentwise Real action commutes with every internal face schema. -/
theorem ccmRationalCyclicWordRealStructure_internalFace
    (pre post : List CCMRationalAlgebraicCrossedProduct)
    (a b : CCMRationalAlgebraicCrossedProduct) :
    ccmRationalCrossedProductKRealAlgebra.cyclicWordSigma
      (pre ++ (a * b) :: post) =
    ccmRationalCrossedProductKRealAlgebra.cyclicWordSigma pre ++
      (ccmRationalCrossedProductKRealAlgebra.sigma a *
        ccmRationalCrossedProductKRealAlgebra.sigma b) ::
      ccmRationalCrossedProductKRealAlgebra.cyclicWordSigma post :=
  ccmRationalCrossedProductKRealAlgebra.cyclicWordSigma_internalFace
    pre post a b

/-- Rational CCM componentwise Real action commutes with every degeneracy schema. -/
theorem ccmRationalCyclicWordRealStructure_degeneracy
    (pre post : List CCMRationalAlgebraicCrossedProduct) :
    ccmRationalCrossedProductKRealAlgebra.cyclicWordSigma
      (pre ++ 1 :: post) =
    ccmRationalCrossedProductKRealAlgebra.cyclicWordSigma pre ++
      1 :: ccmRationalCrossedProductKRealAlgebra.cyclicWordSigma post :=
  ccmRationalCrossedProductKRealAlgebra.cyclicWordSigma_degeneracy
    pre post

end RHTower
end GaloisForLFunctions
