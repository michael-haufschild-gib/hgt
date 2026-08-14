import GaloisForLFunctions.RHTower.FieldOneFiniteStageClassSpaceMeasure

/-!
# The literal class-space `L²` comparison

At a finite semilocal stage the coordinatewise-invertible locus of
`X_S = Q_S^* \\ A_S` is the open image of the idele class group `C_S`.
The source measure on `X_S` is the pushforward of `|c| d*c`, and its
complement is null.  Pullback along `C_S → X_S` is therefore not only an
isometric embedding: it is onto all of `L²(C_S, |c| d*c)`.

The inverse used below extends a representative by zero away from the open
idele locus.  Surjectivity is proved in `L²`, so it is independent of the
chosen representative and of all values on the null complement.
-/

open scoped ENNReal NNReal

namespace GaloisForLFunctions.RHTower

noncomputable section

open IsDedekindDomain MeasureTheory Set

/-- Weighted idele-class Hilbert space `L²(C_S, |c| d*c)`. -/
abbrev FieldOneFiniteStageIdeleClassAdditiveL2
    (S : Finset (HeightOneSpectrum ℤ)) :=
  Lp ℂ 2 (fieldOneFiniteStageIdeleClassAdditiveMeasure S)

/-- Pullback from the literal additive class space to its conull idele-class
locus. -/
def fieldOneFiniteStageClassToIdeleClassAdditiveL2
    (S : Finset (HeightOneSpectrum ℤ)) :
    FieldOneFiniteStageClassL2 S →ₗᵢ[ℂ]
      FieldOneFiniteStageIdeleClassAdditiveL2 S :=
  Lp.compMeasurePreservingₗᵢ ℂ
    (fieldOneFiniteStageIdeleClassToClassSpace S)
    (fieldOneFiniteStageIdeleClassToClassSpace_measurePreserving S)

/-- Every weighted `L²` function on `C_S` is the pullback of an `L²`
function on the literal class space `X_S`. -/
theorem fieldOneFiniteStageClassToIdeleClassAdditiveL2_surjective
    (S : Finset (HeightOneSpectrum ℤ)) :
    Function.Surjective
      (fieldOneFiniteStageClassToIdeleClassAdditiveL2 S) := by
  intro g
  let i := fieldOneFiniteStageIdeleClassToClassSpace S
  let G : FieldOneFiniteStageClassSpace S → ℂ :=
    Function.extend i (fun c => g c) (fun _ => 0)
  have hi : MeasurableEmbedding i :=
    (fieldOneFiniteStageIdeleClassToClassSpace_isOpenEmbedding S).measurableEmbedding
  have hcomp : G ∘ i = fun c => g c := by
    funext c
    exact hi.injective.extend_apply (fun c => g c) (fun _ => 0) c
  have hG : MemLp G 2 (fieldOneFiniteStageClassAdditiveMeasure S) := by
    change MemLp G 2
      (Measure.map i (fieldOneFiniteStageIdeleClassAdditiveMeasure S))
    apply hi.memLp_map_measure_iff.mpr
    rw [hcomp]
    exact Lp.memLp g
  let f : FieldOneFiniteStageClassL2 S := hG.toLp G
  refine ⟨f, ?_⟩
  change Lp.compMeasurePreserving
      (fieldOneFiniteStageIdeleClassToClassSpace S)
      (fieldOneFiniteStageIdeleClassToClassSpace_measurePreserving S) f = g
  apply Lp.ext
  have hpull := Lp.coeFn_compMeasurePreserving f
    (fieldOneFiniteStageIdeleClassToClassSpace_measurePreserving S)
  have hto :
      f =ᵐ[fieldOneFiniteStageClassAdditiveMeasure S] G :=
    MemLp.coeFn_toLp hG
  have htoComp :=
    (fieldOneFiniteStageIdeleClassToClassSpace_measurePreserving S).quasiMeasurePreserving
      |>.ae_eq_comp hto
  filter_upwards [hpull, htoComp] with c hp hc
  rw [hp, hc]
  exact hi.injective.extend_apply (fun c => g c) (fun _ => 0) c

/-- Exact unitary
`L²(X_S, da) ≃ L²(C_S, |c| d*c)` on the literal source class space. -/
def fieldOneFiniteStageClassIdeleClassAdditiveL2Unitary
    (S : Finset (HeightOneSpectrum ℤ)) :
    FieldOneFiniteStageClassL2 S ≃ₗᵢ[ℂ]
      FieldOneFiniteStageIdeleClassAdditiveL2 S :=
  LinearIsometryEquiv.ofSurjective
    (fieldOneFiniteStageClassToIdeleClassAdditiveL2 S)
    (fieldOneFiniteStageClassToIdeleClassAdditiveL2_surjective S)

/-- Pointwise-a.e. restriction formula for the class-space unitary. -/
theorem fieldOneFiniteStageClassIdeleClassAdditiveL2Unitary_ae
    (S : Finset (HeightOneSpectrum ℤ))
    (f : FieldOneFiniteStageClassL2 S) :
    fieldOneFiniteStageClassIdeleClassAdditiveL2Unitary S f =ᵐ[
        fieldOneFiniteStageIdeleClassAdditiveMeasure S]
      fun c => f (fieldOneFiniteStageIdeleClassToClassSpace S c) := by
  exact Lp.coeFn_compMeasurePreserving f
    (fieldOneFiniteStageIdeleClassToClassSpace_measurePreserving S)

end

end GaloisForLFunctions.RHTower
