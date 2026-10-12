import GaloisForLFunctions.RHTower.PaperAbelRoutePSource
import GaloisForLFunctions.HTGeometry.PaperHalfLineCayley
import GaloisForLFunctions.HTGeometry.PaperCompactIdentityDistance

/-!
# Exponentially close, compact-distinct full FU and RP tails

The native positive correction gives a nonzero discrepancy at every finite
tail. Its norm tends to zero exponentially, while the TraceCone compact-ideal
weight remains infinite. Both unitaries retain a common nontrivial spectral
arc, obtained from the full source excursions and continuity.
-/

namespace RHTower
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ENNReal NNReal
open GaloisForLFunctions.HTGeometry

private abbrev PaperAbelTailL2 := Lp ℂ 2 halfLineMeasure

abbrev paperAbelTailOperator (T : ℝ) := paperHalfLineCayley paperCompletedAbelSource T
abbrev paperRoutePTailOperator (T : ℝ) := paperHalfLineCayley paperRoutePSource T

def paperAbelRoutePTailDifference (T : ℝ) : PaperAbelTailL2 →L[ℂ] PaperAbelTailL2 :=
  paperAbelTailOperator T - paperRoutePTailOperator T

theorem paperAbelRoutePTailDifference_coeFn (T : ℝ) (f : PaperAbelTailL2) :
    (paperAbelRoutePTailDifference T f : ℝ → ℂ) =ᵐ[halfLineMeasure]
      fun x => (realCayley (paperCompletedAbelSource (T + x)) -
        realCayley (paperRoutePSource (T + x))) * f x :=
  paperHalfLineCayley_difference_coeFn _ _ T f

/-- Uniform norm control on the entire continuous physical tail. -/
theorem paperAbelRoutePTailDifference_norm_le (T : ℝ≥0) :
    ‖paperAbelRoutePTailDifference T‖ ≤ (40 / 3) * Real.exp (-(T : ℝ) / 2) := by
  apply paperHalfLine_norm_le (paperAbelRoutePTailDifference_coeFn T) (by positivity)
  intro x hx
  have ht : 0 ≤ (T : ℝ) + x := add_nonneg T.2 hx
  have hd : 0 < paperCompletedAbelSource ((T : ℝ) + x) - paperRoutePSource ((T : ℝ) + x) ∧
      paperCompletedAbelSource ((T : ℝ) + x) - paperRoutePSource ((T : ℝ) + x) ≤
        (20 / 3) * Real.exp (-((T : ℝ) + x) / 2) :=
    paperAbelRouteP_source_difference ⟨(T : ℝ) + x, ht⟩
  calc
    _ ≤ 2 * |paperCompletedAbelSource ((T : ℝ) + x) - paperRoutePSource ((T : ℝ) + x)| :=
      paperRealCayley_norm_sub_le _ _
    _ ≤ 2 * ((20 / 3) * Real.exp (-((T : ℝ) + x) / 2)) := by
      rw [abs_of_pos hd.1]
      exact mul_le_mul_of_nonneg_left hd.2 (by norm_num)
    _ ≤ 2 * ((20 / 3) * Real.exp (-(T : ℝ) / 2)) := by
      gcongr
      linarith
    _ = _ := by ring

/-- No finite physical tail identifies the two full sources modulo compact operators. -/
theorem paperAbelRoutePTailDifference_not_compact (T : ℝ≥0) :
    ¬ IsCompactOperator (paperAbelRoutePTailDifference T) := by
  intro h
  have he := (paperHalfLineCayley_compact_difference_iff
    paperCompletedAbelSource paperRoutePSource T).mp h T le_rfl
  have hd := (paperAbelRouteP_source_difference T).1
  rw [he, sub_self] at hd
  exact lt_irrefl _ hd

theorem paperAbelRoutePTailDifference_ne_zero (T : ℝ≥0) :
    paperAbelRoutePTailDifference T ≠ 0 := by
  intro h
  exact paperAbelRoutePTailDifference_not_compact T (h ▸ isCompactOperator_zero)

theorem paperAbelRoutePTailDifference_essentialNorm (T : ℝ) :
    compactIdealDistance (paperAbelRoutePTailDifference T) =
      ‖paperAbelRoutePTailDifference T‖ :=
  paperHalfLineCayley_difference_essentialNorm _ _ T

/-- Exact positive essential discrepancy, with an exponentially vanishing upper bound. -/
theorem paperAbelRoutePTailDifference_essential_bounds (T : ℝ≥0) :
    0 < compactIdealDistance (paperAbelRoutePTailDifference T) ∧
      compactIdealDistance (paperAbelRoutePTailDifference T) ≤
        (40 / 3) * Real.exp (-(T : ℝ) / 2) := by
  rw [paperAbelRoutePTailDifference_essentialNorm]
  exact ⟨norm_pos_iff.mpr (paperAbelRoutePTailDifference_ne_zero T),
    paperAbelRoutePTailDifference_norm_le T⟩

theorem paperAbelRoutePTailDifference_traceCost (T : ℝ≥0) :
    compactOperatorTraceCost PaperAbelTailL2 (paperAbelRoutePTailDifference T) = ∞ := by
  rw [paperHalfLine_traceCost (paperAbelRoutePTailDifference_coeFn T),
    if_neg (paperAbelRoutePTailDifference_ne_zero T)]

/-- Arbitrary compact corrections preserve the exact discrepancy and its infinite ideal weight. -/
theorem paperAbelRoutePTailDifference_compact_correction (T : ℝ≥0)
    (K : compactOperatorStarAlgebra PaperAbelTailL2) :
    compactIdealDistance (paperAbelRoutePTailDifference T + K.1) =
        ‖paperAbelRoutePTailDifference T‖ ∧
      compactOperatorTraceCost PaperAbelTailL2 (paperAbelRoutePTailDifference T + K.1) = ∞ := by
  constructor
  · rw [compactIdealDistance_add_compact _ _ K.2,
      paperAbelRoutePTailDifference_essentialNorm]
  · rw [compactOperatorTraceCost_add_compact, paperAbelRoutePTailDifference_traceCost]

theorem paperAbelRoutePTailDifference_tendsto_zero :
    Tendsto paperAbelRoutePTailDifference atTop (𝓝 0) := by
  have he : Tendsto (fun t : ℝ => Real.exp (-t / 2)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, id_eq, neg_div] using Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (tendsto_id.atTop_div_const (by norm_num : (0 : ℝ) < 2))
  have hb : ∀ᶠ T : ℝ in atTop,
      ‖paperAbelRoutePTailDifference T‖ ≤ (40 / 3) * Real.exp (-T / 2) := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
    exact paperAbelRoutePTailDifference_norm_le ⟨T, hT⟩
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  exact squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) hb
    (by simpa using he.const_mul (40 / 3 : ℝ))

theorem paperAbelRouteP_tail_spectra (T : ℝ) :
    spectrum ℂ (paperAbelTailOperator T) =
        closure (realCayley '' (paperCompletedAbelSource '' Ici T)) ∧
      spectrum ℂ (paperRoutePTailOperator T) =
        closure (realCayley '' (paperRoutePSource '' Ici T)) :=
  ⟨paperHalfLineCayley_spectrum _ T, paperHalfLineCayley_spectrum _ T⟩

/-- A common nontrivial spectral arc persists on every tail of both complete sources. -/
theorem paperAbelRouteP_common_tail_spectral_arc :
    ∃ δ : ℝ, 0 < δ ∧ ∀ T : ℝ,
      realCayley '' Icc (-δ) δ ⊆
        spectrum ℂ (paperAbelTailOperator T) ∩ spectrum ℂ (paperRoutePTailOperator T) := by
  obtain ⟨δ, hδ, h⟩ := paperAbelRouteP_common_tail_interval
  refine ⟨δ, hδ, fun T z hz => ?_⟩
  obtain ⟨x, hx, rfl⟩ := hz
  obtain ⟨a, ha, hax⟩ := (h T).1 hx
  obtain ⟨r, hr, hrx⟩ := (h T).2 hx
  rw [(paperAbelRouteP_tail_spectra T).1, (paperAbelRouteP_tail_spectra T).2]
  exact ⟨subset_closure ⟨x, ⟨a, show T ≤ a from ha.le, hax⟩, rfl⟩,
    subset_closure ⟨x, ⟨r, show T ≤ r from hr.le, hrx⟩, rfl⟩⟩

end
end RHTower
