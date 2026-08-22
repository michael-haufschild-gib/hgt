import Mathlib.MeasureTheory.Function.L2Space

/-!
# Centered indicators in a finite aperture

This source-independent `L²` package gives the exact Hilbert geometry of measurable subsets of a
finite positive-measure aperture.  It is the reusable core of the physical hard-aperture metric.
-/

open scoped BigOperators symmDiff
open MeasureTheory Set

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Indicator of `E` with its constant component on `Ω` removed. -/
def centeredIndicatorOn {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (Ω E : Set X)
    (hΩ : MeasurableSet Ω) (hΩfin : μ Ω ≠ ⊤)
    (hE : MeasurableSet E) (hEfin : μ E ≠ ⊤) :
    Lp ℝ 2 μ :=
  indicatorConstLp 2 hE hEfin (1 : ℝ) -
    (μ.real E / μ.real Ω) • indicatorConstLp 2 hΩ hΩfin (1 : ℝ)

/-- Exact Gram formula for centered indicators in a finite positive-measure aperture. -/
theorem real_inner_centeredIndicatorOn
    {X : Type*} [MeasurableSpace X] (μ : Measure X) (Ω E F : Set X)
    (hΩ : MeasurableSet Ω) (hΩfin : μ Ω ≠ ⊤)
    (hE : MeasurableSet E) (hEfin : μ E ≠ ⊤)
    (hF : MeasurableSet F) (hFfin : μ F ≠ ⊤)
    (hEΩ : E ⊆ Ω) (hFΩ : F ⊆ Ω) (hΩpos : 0 < μ.real Ω) :
    inner ℝ (centeredIndicatorOn μ Ω E hΩ hΩfin hE hEfin)
        (centeredIndicatorOn μ Ω F hΩ hΩfin hF hFfin) =
      μ.real (E ∩ F) - μ.real E * μ.real F / μ.real Ω := by
  simp only [centeredIndicatorOn, inner_sub_left, inner_sub_right,
    real_inner_smul_left, real_inner_smul_right,
    MeasureTheory.L2.real_inner_indicatorConstLp_one_indicatorConstLp_one,
    Set.inter_eq_left.mpr hEΩ, Set.inter_eq_right.mpr hFΩ, Set.inter_self]
  field_simp [hΩpos.ne']
  ring

/-- Exact squared norm of a centered aperture indicator. -/
theorem norm_sq_centeredIndicatorOn
    {X : Type*} [MeasurableSpace X] (μ : Measure X) (Ω E : Set X)
    (hΩ : MeasurableSet Ω) (hΩfin : μ Ω ≠ ⊤)
    (hE : MeasurableSet E) (hEfin : μ E ≠ ⊤)
    (hEΩ : E ⊆ Ω) (hΩpos : 0 < μ.real Ω) :
    ‖centeredIndicatorOn μ Ω E hΩ hΩfin hE hEfin‖ ^ 2 =
      μ.real E * (μ.real Ω - μ.real E) / μ.real Ω := by
  rw [← real_inner_self_eq_norm_sq,
    real_inner_centeredIndicatorOn μ Ω E E hΩ hΩfin hE hEfin hE hEfin hEΩ hEΩ hΩpos,
    Set.inter_self]
  field_simp [hΩpos.ne']

/-- Relative complements are antipodes in the centered-indicator Hilbert geometry. -/
theorem centeredIndicatorOn_sdiff_eq_neg
    {X : Type*} [MeasurableSpace X] (μ : Measure X) (Ω E : Set X)
    (hΩ : MeasurableSet Ω) (hΩfin : μ Ω ≠ ⊤)
    (hE : MeasurableSet E) (hEfin : μ E ≠ ⊤)
    (hEΩ : E ⊆ Ω) (hΩpos : 0 < μ.real Ω) :
    centeredIndicatorOn μ Ω (Ω \ E) hΩ hΩfin (hΩ.diff hE)
        (measure_ne_top_of_subset Set.sdiff_subset hΩfin) =
      -centeredIndicatorOn μ Ω E hΩ hΩfin hE hEfin := by
  have hcompfin : μ (Ω \ E) ≠ ⊤ := measure_ne_top_of_subset Set.sdiff_subset hΩfin
  have hmeasure : μ.real (Ω \ E) = μ.real Ω - μ.real E :=
    MeasureTheory.measureReal_sdiff hEΩ hE hΩfin
  have hratio : μ.real (Ω \ E) / μ.real Ω = 1 - μ.real E / μ.real Ω := by
    rw [hmeasure]
    field_simp [hΩpos.ne']
  have hindicator :
      indicatorConstLp 2 hΩ hΩfin (1 : ℝ) =
        indicatorConstLp 2 hE hEfin (1 : ℝ) +
          indicatorConstLp 2 (hΩ.diff hE) hcompfin (1 : ℝ) := by
    ext1
    grw [Lp.coeFn_add, indicatorConstLp_coeFn, indicatorConstLp_coeFn,
      indicatorConstLp_coeFn]
    conv_lhs => rw [← Set.union_sdiff_cancel hEΩ]
    rw [Set.indicator_union_of_disjoint Set.disjoint_sdiff_right]
    rfl
  rw [centeredIndicatorOn, centeredIndicatorOn, hratio, hindicator]
  module

/-- Symmetric-difference measure written through individual and intersection measures. -/
theorem measureReal_symmDiff_eq_sub_inter
    {X : Type*} [MeasurableSpace X] (μ : Measure X) (E F : Set X)
    (hE : MeasurableSet E) (hEfin : μ E ≠ ⊤)
    (hF : MeasurableSet F) (hFfin : μ F ≠ ⊤) :
    μ.real (E ∆ F) = μ.real E + μ.real F - 2 * μ.real (E ∩ F) := by
  rw [MeasureTheory.measureReal_symmDiff_eq hE hF hEfin hFfin]
  have hE_diff : E \ F = E \ (E ∩ F) := by ext x; simp
  have hF_diff : F \ E = F \ (F ∩ E) := by ext x; simp
  rw [hE_diff, hF_diff,
    MeasureTheory.measureReal_sdiff Set.inter_subset_left (hE.inter hF) hEfin,
    MeasureTheory.measureReal_sdiff Set.inter_subset_left (hF.inter hE) hFfin,
    Set.inter_comm E F]
  ring

/-- Exact squared distance in the constants quotient, expressed by symmetric difference. -/
theorem norm_sub_sq_centeredIndicatorOn
    {X : Type*} [MeasurableSpace X] (μ : Measure X) (Ω E F : Set X)
    (hΩ : MeasurableSet Ω) (hΩfin : μ Ω ≠ ⊤)
    (hE : MeasurableSet E) (hEfin : μ E ≠ ⊤)
    (hF : MeasurableSet F) (hFfin : μ F ≠ ⊤)
    (hEΩ : E ⊆ Ω) (hFΩ : F ⊆ Ω) (hΩpos : 0 < μ.real Ω) :
    ‖centeredIndicatorOn μ Ω E hΩ hΩfin hE hEfin -
        centeredIndicatorOn μ Ω F hΩ hΩfin hF hFfin‖ ^ 2 =
      μ.real (E ∆ F) - (μ.real E - μ.real F) ^ 2 / μ.real Ω := by
  rw [norm_sub_sq_real, ← real_inner_self_eq_norm_sq,
    ← real_inner_self_eq_norm_sq,
    real_inner_centeredIndicatorOn μ Ω E E hΩ hΩfin hE hEfin hE hEfin hEΩ hEΩ hΩpos,
    real_inner_centeredIndicatorOn μ Ω F F hΩ hΩfin hF hFfin hF hFfin hFΩ hFΩ hΩpos,
    real_inner_centeredIndicatorOn μ Ω E F hΩ hΩfin hE hEfin hF hFfin hEΩ hFΩ hΩpos,
    measureReal_symmDiff_eq_sub_inter μ E F hE hEfin hF hFfin]
  simp only [Set.inter_self]
  field_simp [hΩpos.ne']
  ring

end
end GaloisForLFunctions.HTGeometry
