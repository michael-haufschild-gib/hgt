import GaloisForLFunctions.RHTower.FieldOneFiniteStageClassInvariantL2
import GaloisForLFunctions.RHTower.FieldOneFiniteStageConnesMarcolliLemma233

/-!
# Fourier transform on the literal finite-stage class space

The Connes--Consani--Moscovici semilocal Fourier transform is the tensor
product of the normalized local additive Fourier transforms, acting on the
literal quotient `X_S`.  Lemma 2.33 already extends that transform through
the dense Bruhat half-density core on the split idele-class model.  The exact
measure comparison and Haar splitting now transport that extension back to
`L²(X_S)`.

This file does not define Fourier support by transport.  It constructs the
full source operator on the literal quotient and records its action on the
dense, independently defined Bruhat core.  Later support subspaces can
therefore use this operator without replacing source support by an abstract
image condition.
-/

namespace GaloisForLFunctions.RHTower

noncomputable section

open IsDedekindDomain

/-! ### Exact comparison with the split model -/

/-- Restriction to the conull idele locus, source half-density, and Haar
splitting give an exact unitary from the literal additive class space to the
split model used in Connes--Marcolli Lemma 2.33. -/
def fieldOneFiniteStageClassToSplitProductL2Unitary
    (S : Finset (HeightOneSpectrum ℤ)) :
    FieldOneFiniteStageClassL2 S ≃ₗᵢ[ℂ]
      FieldOneFiniteStageSplitProductL2 S :=
  (fieldOneFiniteStageClassToSplitClassL2Unitary S).trans
    (fieldOneFiniteStageSplitL2Unitary S)

/-- The literal class-space realization of the Bruhat half-density core.
It is the inverse image of the independently constructed periodized Bruhat
core, not a support space defined from Fourier transport. -/
def fieldOneFiniteStageClassBruhatHalfDensityLinearMap
    (S : Finset (HeightOneSpectrum ℤ)) :
    FieldOneFiniteStageBruhatSchwartz S →ₗ[ℂ]
      FieldOneFiniteStageClassL2 S where
  toFun x := (fieldOneFiniteStageClassToSplitProductL2Unitary S).symm
    (fieldOneFiniteStageBruhatHalfDensityLinearMap S x)
  map_add' x y := by simp
  map_smul' c x := by simp

@[simp] theorem fieldOneFiniteStageClassToSplitProductL2Unitary_classBruhat
    (S : Finset (HeightOneSpectrum ℤ))
    (x : FieldOneFiniteStageBruhatSchwartz S) :
    fieldOneFiniteStageClassToSplitProductL2Unitary S
        (fieldOneFiniteStageClassBruhatHalfDensityLinearMap S x) =
      fieldOneFiniteStageBruhatHalfDensityLinearMap S x := by
  simp [fieldOneFiniteStageClassBruhatHalfDensityLinearMap]

/-! ### Literal semilocal Fourier operator -/

/-- The normalized semilocal Fourier unitary on literal `L²(X_S)`.
Conjugation is by the proved measure-theoretic comparison with the split
idele-class model; its dense-core formula below identifies it with the
tensor product of the local additive Fourier transforms. -/
def fieldOneFiniteStageClassFourierUnitary
    (S : Finset (HeightOneSpectrum ℤ)) :
    FieldOneFiniteStageClassL2 S ≃ₗᵢ[ℂ]
      FieldOneFiniteStageClassL2 S :=
  (fieldOneFiniteStageClassToSplitProductL2Unitary S).trans
    ((fieldOneFiniteStageConnesMarcolliFourierUnitary S).trans
      (fieldOneFiniteStageClassToSplitProductL2Unitary S).symm)

/-- Exact tensor-product Fourier formula on the literal Bruhat core. -/
@[simp] theorem fieldOneFiniteStageClassFourierUnitary_classBruhat
    (S : Finset (HeightOneSpectrum ℤ))
    (x : FieldOneFiniteStageBruhatSchwartz S) :
    fieldOneFiniteStageClassFourierUnitary S
        (fieldOneFiniteStageClassBruhatHalfDensityLinearMap S x) =
      fieldOneFiniteStageClassBruhatHalfDensityLinearMap S
        (fieldOneFiniteStageBruhatFourierLinearEquiv S x) := by
  apply (fieldOneFiniteStageClassToSplitProductL2Unitary S).injective
  simp [fieldOneFiniteStageClassFourierUnitary]

end

end GaloisForLFunctions.RHTower
