import GaloisForLFunctions.HTGeometry.FiniteSpecialUnitaryHaarProductAveraging

/-!
# Haar-null transfer for finite special-unitary gate tuples

An exceptional measurable set in a complete finite gate assignment space is
Haar-null once one positive `SFinite` coordinate measure annihilates every
left translate.  This is the architecture-level form of local-coordinate
Haar-null transfer.
-/

open MeasureTheory MeasureTheory.Measure TopologicalSpace
open scoped ENNReal

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- A measurable exceptional set of finite `SU(d)` gate assignments is null
for the independent Haar gate law whenever every left translate is null for a
positive `SFinite` coordinate measure. -/
theorem finiteSpecialUnitaryHaarProduct_eq_zero_of_all_left_translates_null
    {κ ι : Type*} [Fintype κ] [Fintype ι] [DecidableEq ι]
    (ν : Measure (κ → Matrix.specialUnitaryGroup ι ℂ)) [SFinite ν]
    {s : Set (κ → Matrix.specialUnitaryGroup ι ℂ)}
    (hs : MeasurableSet s) (hνpos : 0 < ν Set.univ)
    (htrans : ∀ U : κ → Matrix.specialUnitaryGroup ι ℂ,
      ν ((fun V => U * V) ⁻¹' s) = 0) :
    finiteSpecialUnitaryHaarProduct κ ι s = 0 := by
  have hinner (U : κ → Matrix.specialUnitaryGroup ι ℂ) :
      (∫⁻ V, s.indicator
        (1 : (κ → Matrix.specialUnitaryGroup ι ℂ) → ℝ≥0∞) (U * V) ∂ν) = 0 := by
    have hindicator :
        (fun V : κ → Matrix.specialUnitaryGroup ι ℂ =>
          s.indicator (1 : (κ → Matrix.specialUnitaryGroup ι ℂ) → ℝ≥0∞) (U * V)) =
        ((fun V => U * V) ⁻¹' s).indicator
          (fun _ : κ → Matrix.specialUnitaryGroup ι ℂ => (1 : ℝ≥0∞)) := by
      funext V
      simpa [Function.comp_def] using
        (Set.indicator_comp_right (s := s)
          (g := (1 : (κ → Matrix.specialUnitaryGroup ι ℂ) → ℝ≥0∞))
          (fun V => U * V) (x := V)).symm
    rw [show (fun V : κ → Matrix.specialUnitaryGroup ι ℂ =>
      s.indicator (1 : (κ → Matrix.specialUnitaryGroup ι ℂ) → ℝ≥0∞) (U * V)) = _ from hindicator]
    rw [lintegral_indicator (measurable_const_mul U hs)]
    exact (setLIntegral_one _).trans (htrans U)
  have hconv : (finiteSpecialUnitaryHaarProduct κ ι ∗ₘ ν) s = 0 := by
    calc
      (finiteSpecialUnitaryHaarProduct κ ι ∗ₘ ν) s =
          ∫⁻ a, s.indicator (1 : (κ → Matrix.specialUnitaryGroup ι ℂ) → ℝ≥0∞) a
            ∂(finiteSpecialUnitaryHaarProduct κ ι ∗ₘ ν) :=
        (MeasureTheory.lintegral_indicator_one hs).symm
      _ = ∫⁻ U, ∫⁻ V, s.indicator
          (1 : (κ → Matrix.specialUnitaryGroup ι ℂ) → ℝ≥0∞)
          (U * V) ∂ν ∂finiteSpecialUnitaryHaarProduct κ ι :=
        Measure.lintegral_mconv (measurable_const.indicator hs)
      _ = 0 := by
        simp_rw [hinner]
        exact lintegral_zero
  have hscale := congrArg
    (fun μ : Measure (κ → Matrix.specialUnitaryGroup ι ℂ) => μ s)
    (finiteSpecialUnitaryHaarProduct_right_convolution ν)
  rw [hconv, Measure.smul_apply, smul_eq_mul] at hscale
  exact (mul_eq_zero.mp hscale.symm).resolve_left hνpos.ne'

end

end GaloisForLFunctions.HTGeometry
