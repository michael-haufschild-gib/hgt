import GaloisForLFunctions.HTGeometry.FiniteUnitaryHaarAveraging

/-!
# Haar-null transfer on finite unitary groups

A positive finite local coordinate measure annihilating every left translate
of a measurable exceptional set forces that set to be null for normalized
finite-unitary Haar measure.
-/

open MeasureTheory MeasureTheory.Measure TopologicalSpace
open scoped ENNReal

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- A measurable set is normalized finite-unitary Haar-null whenever a
positive `SFinite` measure annihilates all its left translates. -/
theorem finiteUnitaryHaar_eq_zero_of_all_left_translates_null
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ν : Measure (Matrix.unitaryGroup ι ℂ)) [SFinite ν]
    {s : Set (Matrix.unitaryGroup ι ℂ)}
    (hs : MeasurableSet s) (hνpos : 0 < ν Set.univ)
    (htrans : ∀ U : Matrix.unitaryGroup ι ℂ,
      ν ((fun V => U * V) ⁻¹' s) = 0) :
    finiteUnitaryHaar ι s = 0 := by
  have hinner (U : Matrix.unitaryGroup ι ℂ) :
      (∫⁻ V, s.indicator
        (1 : Matrix.unitaryGroup ι ℂ → ℝ≥0∞) (U * V) ∂ν) = 0 := by
    have hindicator :
        (fun V : Matrix.unitaryGroup ι ℂ =>
          s.indicator (1 : Matrix.unitaryGroup ι ℂ → ℝ≥0∞) (U * V)) =
        ((fun V => U * V) ⁻¹' s).indicator
          (fun _ : Matrix.unitaryGroup ι ℂ => (1 : ℝ≥0∞)) := by
      funext V
      simpa [Function.comp_def] using
        (Set.indicator_comp_right (s := s)
          (g := (1 : Matrix.unitaryGroup ι ℂ → ℝ≥0∞))
          (fun V => U * V) (x := V)).symm
    rw [show (fun V : Matrix.unitaryGroup ι ℂ =>
      s.indicator (1 : Matrix.unitaryGroup ι ℂ → ℝ≥0∞) (U * V)) = _ from hindicator]
    rw [lintegral_indicator (measurable_const_mul U hs)]
    exact (setLIntegral_one _).trans (htrans U)
  have hconv : (finiteUnitaryHaar ι ∗ₘ ν) s = 0 := by
    calc
      (finiteUnitaryHaar ι ∗ₘ ν) s =
          ∫⁻ a, s.indicator (1 : Matrix.unitaryGroup ι ℂ → ℝ≥0∞) a
            ∂(finiteUnitaryHaar ι ∗ₘ ν) :=
        (MeasureTheory.lintegral_indicator_one hs).symm
      _ = ∫⁻ U, ∫⁻ V, s.indicator
          (1 : Matrix.unitaryGroup ι ℂ → ℝ≥0∞)
          (U * V) ∂ν ∂finiteUnitaryHaar ι :=
        Measure.lintegral_mconv (measurable_const.indicator hs)
      _ = 0 := by
        simp_rw [hinner]
        exact lintegral_zero
  have hscale := congrArg
    (fun μ : Measure (Matrix.unitaryGroup ι ℂ) => μ s)
    (finiteUnitaryHaar_right_convolution ν)
  rw [hconv, Measure.smul_apply, smul_eq_mul] at hscale
  exact (mul_eq_zero.mp hscale.symm).resolve_left hνpos.ne'

end

end GaloisForLFunctions.HTGeometry
