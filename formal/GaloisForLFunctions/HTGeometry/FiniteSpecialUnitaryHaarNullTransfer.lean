import GaloisForLFunctions.HTGeometry.FiniteSpecialUnitaryHaarAveraging

/-!
# Haar-null transfer on finite special-unitary groups

If a positive coordinate measure annihilates every left translate of a set,
then Haar averaging forces the set itself to be Haar-null.  A local `SU(n)`
chart need only provide this translation-stable coordinate nullity.
-/

open MeasureTheory MeasureTheory.Measure TopologicalSpace
open scoped ENNReal

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- A measurable set is normalized finite-special-unitary Haar-null whenever
a positive `SFinite` measure annihilates all of its left translates. -/
theorem finiteSpecialUnitaryHaar_eq_zero_of_all_left_translates_null
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ν : Measure (Matrix.specialUnitaryGroup ι ℂ)) [SFinite ν]
    {s : Set (Matrix.specialUnitaryGroup ι ℂ)}
    (hs : MeasurableSet s) (hνpos : 0 < ν Set.univ)
    (htrans : ∀ U : Matrix.specialUnitaryGroup ι ℂ,
      ν ((fun V => U * V) ⁻¹' s) = 0) :
    finiteSpecialUnitaryHaar ι s = 0 := by
  have hinner (U : Matrix.specialUnitaryGroup ι ℂ) :
      (∫⁻ V, s.indicator
        (1 : Matrix.specialUnitaryGroup ι ℂ → ℝ≥0∞) (U * V) ∂ν) = 0 := by
    have hindicator :
        (fun V : Matrix.specialUnitaryGroup ι ℂ =>
          s.indicator (1 : Matrix.specialUnitaryGroup ι ℂ → ℝ≥0∞) (U * V)) =
        ((fun V => U * V) ⁻¹' s).indicator
          (fun _ : Matrix.specialUnitaryGroup ι ℂ => (1 : ℝ≥0∞)) := by
      funext V
      simpa [Function.comp_def] using
        (Set.indicator_comp_right (s := s)
          (g := (1 : Matrix.specialUnitaryGroup ι ℂ → ℝ≥0∞))
          (fun V => U * V) (x := V)).symm
    rw [show (fun V : Matrix.specialUnitaryGroup ι ℂ =>
      s.indicator (1 : Matrix.specialUnitaryGroup ι ℂ → ℝ≥0∞) (U * V)) = _ from hindicator]
    rw [lintegral_indicator (measurable_const_mul U hs)]
    exact (setLIntegral_one _).trans (htrans U)
  have hconv : (finiteSpecialUnitaryHaar ι ∗ₘ ν) s = 0 := by
    calc
      (finiteSpecialUnitaryHaar ι ∗ₘ ν) s =
          ∫⁻ a, s.indicator (1 : Matrix.specialUnitaryGroup ι ℂ → ℝ≥0∞) a
            ∂(finiteSpecialUnitaryHaar ι ∗ₘ ν) :=
        (MeasureTheory.lintegral_indicator_one hs).symm
      _ = ∫⁻ U, ∫⁻ V, s.indicator
          (1 : Matrix.specialUnitaryGroup ι ℂ → ℝ≥0∞)
          (U * V) ∂ν ∂finiteSpecialUnitaryHaar ι :=
        Measure.lintegral_mconv (measurable_const.indicator hs)
      _ = 0 := by
        simp_rw [hinner]
        exact lintegral_zero
  have hscale := congrArg
    (fun μ : Measure (Matrix.specialUnitaryGroup ι ℂ) => μ s)
    (finiteSpecialUnitaryHaar_right_convolution ν)
  rw [hconv, Measure.smul_apply, smul_eq_mul] at hscale
  exact (mul_eq_zero.mp hscale.symm).resolve_left hνpos.ne'

end

end GaloisForLFunctions.HTGeometry
