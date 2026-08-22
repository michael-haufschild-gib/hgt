import GaloisForLFunctions.HTGeometry.FiniteSpecialUnitaryHaarProductAveraging

/-!
# Right-translate Haar-null transfer for finite special-unitary gate tuples

An exceptional measurable set in a complete finite gate-assignment space is
Haar-null once one positive `SFinite` coordinate measure annihilates every
right translate.  This is the orientation required by terminal gate paths
composed on the right of a fixed gate assignment.
-/

open MeasureTheory MeasureTheory.Measure TopologicalSpace
open scoped ENNReal

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- A measurable exceptional set of finite `SU(d)` gate assignments is null
for the independent Haar gate law whenever every right translate is null for a
positive `SFinite` coordinate measure. -/
theorem finiteSpecialUnitaryHaarProduct_eq_zero_of_all_right_translates_null
    {κ ι : Type*} [Fintype κ] [Fintype ι] [DecidableEq ι]
    (ν : Measure (κ → Matrix.specialUnitaryGroup ι ℂ)) [SFinite ν]
    {s : Set (κ → Matrix.specialUnitaryGroup ι ℂ)}
    (hs : MeasurableSet s) (hνpos : 0 < ν Set.univ)
    (htrans : ∀ U : κ → Matrix.specialUnitaryGroup ι ℂ,
      ν ((fun V => V * U) ⁻¹' s) = 0) :
    finiteSpecialUnitaryHaarProduct κ ι s = 0 := by
  have hinner (U : κ → Matrix.specialUnitaryGroup ι ℂ) :
      (∫⁻ V, s.indicator
        (1 : (κ → Matrix.specialUnitaryGroup ι ℂ) → ℝ≥0∞) (V * U) ∂ν) = 0 := by
    have hindicator :
        (fun V : κ → Matrix.specialUnitaryGroup ι ℂ =>
          s.indicator (1 : (κ → Matrix.specialUnitaryGroup ι ℂ) → ℝ≥0∞) (V * U)) =
        ((fun V => V * U) ⁻¹' s).indicator
          (fun _ : κ → Matrix.specialUnitaryGroup ι ℂ => (1 : ℝ≥0∞)) := by
      funext V
      simpa [Function.comp_def] using
        (Set.indicator_comp_right (s := s)
          (g := (1 : (κ → Matrix.specialUnitaryGroup ι ℂ) → ℝ≥0∞))
          (fun V => V * U) (x := V)).symm
    rw [show (fun V : κ → Matrix.specialUnitaryGroup ι ℂ =>
      s.indicator (1 : (κ → Matrix.specialUnitaryGroup ι ℂ) → ℝ≥0∞) (V * U)) = _ from hindicator]
    rw [lintegral_indicator (measurable_mul_const U hs)]
    exact (setLIntegral_one _).trans (htrans U)
  have hconv : (ν ∗ₘ finiteSpecialUnitaryHaarProduct κ ι) s = 0 := by
    calc
      (ν ∗ₘ finiteSpecialUnitaryHaarProduct κ ι) s =
          ∫⁻ a, s.indicator (1 : (κ → Matrix.specialUnitaryGroup ι ℂ) → ℝ≥0∞) a
            ∂(ν ∗ₘ finiteSpecialUnitaryHaarProduct κ ι) :=
        (MeasureTheory.lintegral_indicator_one hs).symm
      _ = ∫⁻ V, ∫⁻ U, s.indicator
          (1 : (κ → Matrix.specialUnitaryGroup ι ℂ) → ℝ≥0∞)
          (V * U) ∂finiteSpecialUnitaryHaarProduct κ ι ∂ν :=
        Measure.lintegral_mconv (measurable_const.indicator hs)
      _ = ∫⁻ U, ∫⁻ V, s.indicator
          (1 : (κ → Matrix.specialUnitaryGroup ι ℂ) → ℝ≥0∞)
          (V * U) ∂ν ∂finiteSpecialUnitaryHaarProduct κ ι := by
        have hmeas : Measurable
            (Function.uncurry fun V U : κ → Matrix.specialUnitaryGroup ι ℂ =>
              s.indicator (1 : (κ → Matrix.specialUnitaryGroup ι ℂ) → ℝ≥0∞) (V * U)) := by
          change Measurable (fun p : (κ → Matrix.specialUnitaryGroup ι ℂ) ×
            (κ → Matrix.specialUnitaryGroup ι ℂ) =>
              s.indicator (1 : (κ → Matrix.specialUnitaryGroup ι ℂ) → ℝ≥0∞) (p.1 * p.2))
          exact (measurable_const.indicator hs).comp measurable_mul
        exact lintegral_lintegral_swap hmeas.aemeasurable
      _ = 0 := by
        simp_rw [hinner]
        exact lintegral_zero
  have hscale := congrArg
    (fun μ : Measure (κ → Matrix.specialUnitaryGroup ι ℂ) => μ s)
    (finiteSpecialUnitaryHaarProduct_left_convolution ν)
  rw [hconv, Measure.smul_apply, smul_eq_mul] at hscale
  exact (mul_eq_zero.mp hscale.symm).resolve_left hνpos.ne'

end

end GaloisForLFunctions.HTGeometry
