import GaloisForLFunctions.HTGeometry.FokasLenellsOriginWeightedProfile
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic

/-!
# Sharp local integrability of the actual weighted reflection profile

The reciprocal compatibility pole gives a necessary condition for every
local L^p assertion with p>=1. Its removal gives one interval on which
all L^p bounds, including L^infinity, hold. This audits the positive-z
part of Proposition 3.9 of arXiv:2607.19649 on Schwartz initial data.
-/

open Complex Matrix MeasureTheory Filter Topology Set
open scoped ENNReal NNReal
namespace GaloisForLFunctions.HTGeometry.FokasLenells
noncomputable section

private theorem measurable_finite_limit_window (f : ℝ → ℂ) (hfm : Measurable f)
    (c : ℂ) (hc : Tendsto f (𝓝[>] 0) (𝓝 c)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ p : ℝ≥0∞,
      MemLp f p (volume.restrict (Ioo 0 δ)) := by
  have hb := hc.norm.eventually_le_const (show ‖c‖ < ‖c‖+1 by linarith)
  obtain ⟨δ,hδ,hbound⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hb
  refine ⟨δ,hδ,fun p => MemLp.of_bound
    hfm.aestronglyMeasurable (‖c‖+1) ?_⟩
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with z hz
  exact hbound hz

private theorem integrable_coordinate_limit_zero (f : ℝ → ℂ) (c : ℂ)
    (hl : Tendsto (fun z : ℝ => (z : ℂ)*f z) (𝓝[>] 0) (𝓝 c))
    (r : ℝ) (hr : 0 < r) (hW : IntegrableOn (f) (Ioo 0 r)) :
    c = 0 := by
  by_contra hm
  have hc : 0 < ‖c‖ := norm_pos_iff.mpr hm
  have hb := hl.norm.eventually_const_le
    (show ‖c‖/2 < ‖c‖ by linarith)
  obtain ⟨ε,hε,hbound⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hb
  have hδ : 0 < min r ε := lt_min hr hε
  have hWs : IntegrableOn (f) (Ioo 0 (min r ε)) :=
    hW.mono_set (Ioo_subset_Ioo le_rfl (min_le_left _ _))
  have hdom := hWs.norm.const_mul (2/‖c‖)
  have hinv : IntegrableOn (fun z : ℝ => z⁻¹) (Ioo 0 (min r ε)) := by
    apply hdom.mono' measurable_inv.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with z hz
    have hzε : z ∈ Ioo 0 ε := ⟨hz.1,lt_of_lt_of_le hz.2 (min_le_right _ _)⟩
    have hlow : ‖c‖/2 ≤ ‖(z : ℂ)*f z‖ := hbound hzε
    have hnorm : ‖(z : ℂ)*f z‖ = z*‖f z‖ := by
      rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hz.1]
    rw [hnorm] at hlow
    rw [Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hz.1)]
    apply (inv_le_iff_one_le_mul₀' hz.1).2
    calc
      1 = (2/‖c‖)*(‖c‖/2) := by field_simp
      _ ≤ (2/‖c‖)*(z*‖f z‖) :=
        mul_le_mul_of_nonneg_left hlow (by positivity)
      _ = z*((2/‖c‖)*‖f z‖) := by ring
  have hrpow : IntegrableOn (fun z : ℝ => z^(-1 : ℝ)) (Ioo 0 (min r ε)) := by
    simpa only [Real.rpow_neg_one] using hinv
  have hfalse := (intervalIntegral.integrableOn_Ioo_rpow_iff hδ).1 hrpow
  exact (lt_irrefl (-1 : ℝ)) hfalse

private theorem origin_weighted_bounded_window (q : SchwartzMap ℝ ℂ)
    (hm : compatibilityMoment q = 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ p : ℝ≥0∞,
      MemLp (originWeightedReflection q) p (volume.restrict (Ioo 0 δ)) := by
  obtain ⟨c,hc⟩ := (originWeightedReflection_finite_limit_iff q).2 hm
  exact measurable_finite_limit_window _ (originWeightedReflection_measurable q) c hc

private theorem origin_weighted_integrable_forces_compatibility (q : SchwartzMap ℝ ℂ)
    (r : ℝ) (hr : 0 < r) (hW : IntegrableOn (originWeightedReflection q) (Ioo 0 r)) :
    compatibilityMoment q = 0 := by
  have hz := integrable_coordinate_limit_zero _ _
    (originWeightedReflection_mul_coordinate_tendsto q) r hr hW
  exact (mul_eq_zero.mp hz).resolve_left (by norm_num)

/-- Even local L^1 at the origin forces precisely the cubic compatibility moment to vanish. -/
theorem originWeightedReflection_locally_integrable_iff (q : SchwartzMap ℝ ℂ) :
    (∃ δ : ℝ, 0 < δ ∧ IntegrableOn (originWeightedReflection q) (Ioo 0 δ)) ↔
      compatibilityMoment q = 0 := by
  constructor
  · rintro ⟨δ,hδ,hW⟩
    exact origin_weighted_integrable_forces_compatibility q δ hδ hW
  · intro hm
    obtain ⟨δ,hδ,hW⟩ := origin_weighted_bounded_window q hm
    exact ⟨δ,hδ,MemLp.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2) (hW 2)⟩

/-- Sharp replacement for the positive-axis weighted L^2 conclusion of Proposition 3.9. -/
theorem originWeightedReflection_locally_memLp_two_iff (q : SchwartzMap ℝ ℂ) :
    (∃ δ : ℝ, 0 < δ ∧ MemLp (originWeightedReflection q) 2 (volume.restrict (Ioo 0 δ))) ↔
      compatibilityMoment q = 0 := by
  constructor
  · rintro ⟨δ,hδ,hW⟩
    exact origin_weighted_integrable_forces_compatibility q δ hδ
      (MemLp.integrable (by norm_num) hW)
  · intro hm
    obtain ⟨δ,hδ,hW⟩ := origin_weighted_bounded_window q hm
    exact ⟨δ,hδ,hW 2⟩

/-- Removing the pole provides one common interval for every L^p space, including L^infinity. -/
theorem originWeightedReflection_locally_memLp_all_iff (q : SchwartzMap ℝ ℂ) :
    (∃ δ : ℝ, 0 < δ ∧ ∀ p : ℝ≥0∞,
      MemLp (originWeightedReflection q) p (volume.restrict (Ioo 0 δ))) ↔
      compatibilityMoment q = 0 := by
  constructor
  · rintro ⟨δ,hδ,hW⟩
    exact (originWeightedReflection_locally_memLp_two_iff q).1 ⟨δ,hδ,hW 2⟩
  · exact origin_weighted_bounded_window q

/-- Every exponent at least one has exactly the same compatibility boundary. -/
theorem originWeightedReflection_locally_memLp_one_add_iff (q : SchwartzMap ℝ ℂ) (p : ℝ≥0∞) :
    (∃ δ : ℝ, 0 < δ ∧ MemLp (originWeightedReflection q) (1+p)
      (volume.restrict (Ioo 0 δ))) ↔ compatibilityMoment q = 0 := by
  constructor
  · rintro ⟨δ,hδ,hW⟩
    exact origin_weighted_integrable_forces_compatibility q δ hδ
      (MemLp.integrable (le_self_add) hW)
  · intro hm
    obtain ⟨δ,hδ,hW⟩ := origin_weighted_bounded_window q hm
    exact ⟨δ,hδ,hW (1+p)⟩

/-- Arbitrarily small Gaussian scattering data fail the local weighted L^1 assertion on every window. -/
theorem originWeightedReflection_globalSmallGaussian_not_integrable (a r : ℝ) :
    ¬ IntegrableOn (originWeightedReflection (globalSmallScatteringPotential (compatibilityGaussian a)))
      (Ioo 0 (Real.exp r)) := by
  intro h
  exact compatibilityMoment_globalSmallGaussian_ne_zero a
    ((originWeightedReflection_locally_integrable_iff _).1 ⟨Real.exp r,Real.exp_pos r,h⟩)

/-- An explicit smooth small-data obstruction to the weighted L^2 conclusion as a spatial assertion. -/
theorem originWeightedReflection_globalSmallGaussian_not_memLp_two (a r : ℝ) :
    ¬ MemLp (originWeightedReflection (globalSmallScatteringPotential (compatibilityGaussian a))) 2
      (volume.restrict (Ioo 0 (Real.exp r))) := by
  intro h
  exact originWeightedReflection_globalSmallGaussian_not_integrable a r
    (MemLp.integrable (by norm_num) h)

/-- Subtract a proposed residue from the actual weighted reflection profile. -/
def renormalizedOriginReflection (q : SchwartzMap ℝ ℂ) (c : ℂ) (z : ℝ) : ℂ :=
  originWeightedReflection q z-c/(z : ℂ)

theorem renormalizedOriginReflection_measurable (q : SchwartzMap ℝ ℂ) (c : ℂ) :
    Measurable (renormalizedOriginReflection q c) :=
  (originWeightedReflection_measurable q).sub
    (measurable_const.div Complex.continuous_ofReal.measurable)

/-- A proposed subtraction changes the actual reciprocal residue by exactly that amount. -/
theorem renormalizedOriginReflection_mul_coordinate_tendsto (q : SchwartzMap ℝ ℂ) (c : ℂ) :
    Tendsto (fun z : ℝ => (z : ℂ)*renormalizedOriginReflection q c z)
      (𝓝[>] 0) (𝓝 (2*compatibilityMoment q-c)) := by
  apply ((originWeightedReflection_mul_coordinate_tendsto q).sub_const c).congr'
  filter_upwards [self_mem_nhdsWithin] with z hz
  have hzc : (z : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hz)
  simp only [renormalizedOriginReflection,mul_sub]
  field_simp

/-- The compatibility coefficient is the unique subtraction that leaves a finite right limit. -/
theorem renormalizedOriginReflection_finite_limit_iff (q : SchwartzMap ℝ ℂ) (c : ℂ) :
    (∃ d : ℂ, Tendsto (renormalizedOriginReflection q c) (𝓝[>] 0) (𝓝 d)) ↔
      c = 2*compatibilityMoment q := by
  constructor
  · rintro ⟨d,hd⟩
    have hz : Tendsto (fun z : ℝ => (z : ℂ)) (𝓝[>] 0) (𝓝 0) :=
      (Complex.continuous_ofReal.tendsto 0).mono_left nhdsWithin_le_nhds
    have hh := hz.mul hd
    simp only [zero_mul] at hh
    have he := tendsto_nhds_unique (renormalizedOriginReflection_mul_coordinate_tendsto q c) hh
    exact (sub_eq_zero.mp he).symm
  · rintro rfl
    exact ⟨rawScatteringFifthCoefficient q 1 0,originWeightedReflection_sub_pole_tendsto q⟩

/-- The explicit subtraction is also uniquely characterized by local L^1 integrability. -/
theorem renormalizedOriginReflection_locally_integrable_iff (q : SchwartzMap ℝ ℂ) (c : ℂ) :
    (∃ δ : ℝ, 0 < δ ∧ IntegrableOn (renormalizedOriginReflection q c) (Ioo 0 δ)) ↔
      c = 2*compatibilityMoment q := by
  constructor
  · rintro ⟨δ,hδ,hW⟩
    have hz := integrable_coordinate_limit_zero _ _
      (renormalizedOriginReflection_mul_coordinate_tendsto q c) δ hδ hW
    exact (sub_eq_zero.mp hz).symm
  · intro hc
    obtain ⟨d,hd⟩ := (renormalizedOriginReflection_finite_limit_iff q c).2 hc
    obtain ⟨δ,hδ,hW⟩ := measurable_finite_limit_window _
      (renormalizedOriginReflection_measurable q c) d hd
    exact ⟨δ,hδ,MemLp.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2) (hW 2)⟩

/-- The paper's local L^2 assertion holds after exactly one explicit pole subtraction. -/
theorem renormalizedOriginReflection_locally_memLp_two_iff (q : SchwartzMap ℝ ℂ) (c : ℂ) :
    (∃ δ : ℝ, 0 < δ ∧ MemLp (renormalizedOriginReflection q c) 2
      (volume.restrict (Ioo 0 δ))) ↔ c = 2*compatibilityMoment q := by
  constructor
  · rintro ⟨δ,hδ,hW⟩
    exact (renormalizedOriginReflection_locally_integrable_iff q c).1
      ⟨δ,hδ,MemLp.integrable (by norm_num) hW⟩
  · intro hc
    obtain ⟨d,hd⟩ := (renormalizedOriginReflection_finite_limit_iff q c).2 hc
    obtain ⟨δ,hδ,hW⟩ := measurable_finite_limit_window _
      (renormalizedOriginReflection_measurable q c) d hd
    exact ⟨δ,hδ,hW 2⟩

/-- Correct pole subtraction unconditionally restores all local L^p bounds on one interval. -/
theorem renormalizedOriginReflection_locally_memLp_all (q : SchwartzMap ℝ ℂ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ p : ℝ≥0∞,
      MemLp (renormalizedOriginReflection q (2*compatibilityMoment q)) p
        (volume.restrict (Ioo 0 δ)) :=
  measurable_finite_limit_window _ (renormalizedOriginReflection_measurable q _)
    (rawScatteringFifthCoefficient q 1 0) (originWeightedReflection_sub_pole_tendsto q)

end
end GaloisForLFunctions.HTGeometry.FokasLenells
