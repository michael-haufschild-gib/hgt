import GaloisForLFunctions.RHTower.FieldOneFiniteStageClassL2Comparison

/-!
# Half-density transport on finite-stage idele classes

The additive quotient measure pulls back from `X_S` to `|c| d*c` on
`C_S`.  Multiplication by `|c|^{1/2}` is therefore the exact unitary from
the weighted idele-class space to split multiplicative Haar `L²(C_S,d*c)`.
This is the half-density normalization in the source map `w_S`.
-/

namespace GaloisForLFunctions.RHTower

noncomputable section

open IsDedekindDomain

/-- Exact half-density unitary
`L²(C_S, |c| d*c) ≃ L²(C_S, d*c)`. -/
def fieldOneFiniteStageIdeleClassHalfDensityUnitary
    (S : Finset (HeightOneSpectrum ℤ)) :
    FieldOneFiniteStageIdeleClassAdditiveL2 S ≃ₗᵢ[ℂ]
      FieldOneFiniteStageSplitClassL2 S :=
  GaloisForLFunctions.HTGeometry.weightedDensityUnitary
    (fieldOneFiniteStageIdeleClassModuleReal S)
    (fieldOneFiniteStageIdeleClassModuleReal_measurable S)
    (fieldOneFiniteStageIdeleClassModuleReal_pos S)

/-- Pointwise-a.e. source formula for the half-density unitary. -/
theorem fieldOneFiniteStageIdeleClassHalfDensityUnitary_ae
    (S : Finset (HeightOneSpectrum ℤ))
    (f : FieldOneFiniteStageIdeleClassAdditiveL2 S) :
    fieldOneFiniteStageIdeleClassHalfDensityUnitary S f =ᵐ[
        fieldOneFiniteStageSplitHaarMeasure S]
      fun c =>
        GaloisForLFunctions.HTGeometry.sqrtWeight
          (fieldOneFiniteStageIdeleClassModuleReal S) c * f c :=
  GaloisForLFunctions.HTGeometry.densityMul_ae
    (fieldOneFiniteStageIdeleClassModuleReal S)
    (fieldOneFiniteStageIdeleClassModuleReal_measurable S)
    (fieldOneFiniteStageIdeleClassModuleReal_pos S) f

/-- Exact unitary from the literal additive class space to multiplicative
Haar `L²(C_S)`: restriction to the conull idele locus followed by the source
half-density. -/
def fieldOneFiniteStageClassToSplitClassL2Unitary
    (S : Finset (HeightOneSpectrum ℤ)) :
    FieldOneFiniteStageClassL2 S ≃ₗᵢ[ℂ]
      FieldOneFiniteStageSplitClassL2 S :=
  (fieldOneFiniteStageClassIdeleClassAdditiveL2Unitary S).trans
    (fieldOneFiniteStageIdeleClassHalfDensityUnitary S)

end

end GaloisForLFunctions.RHTower
