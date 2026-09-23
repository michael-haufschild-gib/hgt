import GaloisForLFunctions.HTGeometry.FokasLenellsOriginIntegrability
import GaloisForLFunctions.HTGeometry.FokasLenellsContourFifth

/-!
# The weighted original reflection on the full squared spectral line

Positive z comes from real lambda; negative z comes from imaginary lambda.
The factor I and the reflected source I*q(-x) are forced by the actual
Lax conjugation. Both square-root branches yield this same weighted profile.
-/

open Complex Matrix MeasureTheory Filter Topology Set
open scoped ENNReal NNReal
namespace GaloisForLFunctions.HTGeometry.FokasLenells
noncomputable section

def signedOriginWeightedReflection (q : SchwartzMap ℝ ℂ) (z : ℝ) : ℂ :=
  if 0 ≤ z then originWeightedReflection q z
  else I*originWeightedReflection (twistedPotential q) (-z)

@[simp] theorem signedOriginWeightedReflection_zero (q : SchwartzMap ℝ ℂ) :
    signedOriginWeightedReflection q 0 = 0 := by
  simp [signedOriginWeightedReflection,originWeightedReflection]

theorem signedOriginWeightedReflection_measurable (q : SchwartzMap ℝ ℂ) :
    Measurable (signedOriginWeightedReflection q) := by
  exact Measurable.ite measurableSet_Ici (originWeightedReflection_measurable q)
    (measurable_const.mul ((originWeightedReflection_measurable (twistedPotential q)).comp measurable_neg))

/-- This is the paper's z^-2 lambda^-1 b(lambda) on each of the four actual spectral rays. -/
theorem signedOriginWeightedReflection_eq_contour (q : SchwartzMap ℝ ℂ)
    (vertical negative : Bool) (κ : ℝ) :
    signedOriginWeightedReflection q (contourSquaredParameter vertical κ) =
      contourReflectionAmplitude q vertical negative κ/(contourParameter vertical negative κ)^(5 : ℕ) := by
  have hp : 0 < (Real.exp κ)^(2 : ℕ) := sq_pos_of_pos (Real.exp_pos κ)
  have hi : Complex.I^(5 : ℕ) = Complex.I := by rw [pow_succ,I_pow_four,one_mul]
  have hni : (-I)^(5 : ℕ) = -I := by rw [neg_pow,hi]; norm_num
  cases vertical <;> cases negative <;>
    simp only [contourSquaredParameter,contourReflectionAmplitude_eq,contourSource,contourParameter,
      Bool.false_eq_true,↓reduceIte,one_mul,neg_one_mul,
      signedOriginWeightedReflection,if_pos hp.le,if_neg (not_le.mpr (neg_neg_of_pos hp)),neg_neg,
      originWeightedReflection_exp]
  all_goals ring_nf
  all_goals (simp [hni,inv_I]; ring)

private theorem signed_origin_bounded_window (q : SchwartzMap ℝ ℂ)
    (hm : compatibilityMoment q = 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ p : ℝ≥0∞,
      MemLp (signedOriginWeightedReflection q) p (volume.restrict (Ioo (-δ) δ)) := by
  obtain ⟨c,hc⟩ := (originWeightedReflection_finite_limit_iff q).2 hm
  obtain ⟨d,hd⟩ := (originWeightedReflection_finite_limit_iff (twistedPotential q)).2
    ((compatibilityMoment_twistedPotential_zero_iff q).2 hm)
  obtain ⟨r,hr,hbr⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp
    (hc.norm.eventually_le_const (show ‖c‖ < ‖c‖+1 by linarith))
  obtain ⟨s,hs,hbs⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp
    (hd.norm.eventually_le_const (show ‖d‖ < ‖d‖+1 by linarith))
  refine ⟨min r s,lt_min hr hs,fun p => MemLp.of_bound
    (signedOriginWeightedReflection_measurable q).aestronglyMeasurable
      (max (‖c‖+1) (‖d‖+1)) ?_⟩
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with z hz
  rcases lt_trichotomy z 0 with hneg | rfl | hpos
  · rw [signedOriginWeightedReflection,if_neg (not_le.mpr hneg),norm_mul,norm_I,one_mul]
    exact (hbs ⟨neg_pos.mpr hneg,by have hh := min_le_right r s; linarith [hz.1]⟩).trans (le_max_right _ _)
  · rw [signedOriginWeightedReflection_zero,norm_zero]
    exact (by positivity : (0 : ℝ) ≤ ‖c‖+1).trans (le_max_left _ _)
  · rw [signedOriginWeightedReflection,if_pos hpos.le]
    exact (hbr ⟨hpos,lt_of_lt_of_le hz.2 (min_le_left _ _)⟩).trans (le_max_left _ _)

private theorem signed_origin_integrable_forces_compatibility (q : SchwartzMap ℝ ℂ)
    (δ : ℝ) (hδ : 0 < δ)
    (h : IntegrableOn (signedOriginWeightedReflection q) (Ioo (-δ) δ)) : compatibilityMoment q = 0 := by
  have hs : IntegrableOn (signedOriginWeightedReflection q) (Ioo 0 δ) :=
    h.mono_set (Ioo_subset_Ioo (by linarith) le_rfl)
  have hp : IntegrableOn (originWeightedReflection q) (Ioo 0 δ) := by
    apply hs.congr_fun_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with z hz
    exact if_pos hz.1.le
  exact (originWeightedReflection_locally_integrable_iff q).1 ⟨δ,hδ,hp⟩

/-- The full two-sided local L^(1 : ℕ) assertion has the same exact compatibility boundary. -/
theorem signedOriginWeightedReflection_locally_integrable_iff (q : SchwartzMap ℝ ℂ) :
    (∃ δ : ℝ, 0 < δ ∧ IntegrableOn (signedOriginWeightedReflection q) (Ioo (-δ) δ)) ↔
      compatibilityMoment q = 0 := by
  constructor
  · rintro ⟨δ,hδ,hW⟩
    exact signed_origin_integrable_forces_compatibility q δ hδ hW
  · intro hm
    obtain ⟨δ,hδ,hW⟩ := signed_origin_bounded_window q hm
    exact ⟨δ,hδ,MemLp.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2) (hW 2)⟩

/-- Sharp two-sided replacement of Proposition 3.9 for actual Schwartz scattering data. -/
theorem signedOriginWeightedReflection_locally_memLp_two_iff (q : SchwartzMap ℝ ℂ) :
    (∃ δ : ℝ, 0 < δ ∧ MemLp (signedOriginWeightedReflection q) 2
      (volume.restrict (Ioo (-δ) δ))) ↔ compatibilityMoment q = 0 := by
  constructor
  · rintro ⟨δ,hδ,hW⟩
    exact signed_origin_integrable_forces_compatibility q δ hδ (MemLp.integrable (by norm_num) hW)
  · intro hm
    obtain ⟨δ,hδ,hW⟩ := signed_origin_bounded_window q hm
    exact ⟨δ,hδ,hW 2⟩

/-- One symmetric interval supports every L^p bound precisely when the compatibility pole vanishes. -/
theorem signedOriginWeightedReflection_locally_memLp_all_iff (q : SchwartzMap ℝ ℂ) :
    (∃ δ : ℝ, 0 < δ ∧ ∀ p : ℝ≥0∞,
      MemLp (signedOriginWeightedReflection q) p (volume.restrict (Ioo (-δ) δ))) ↔
      compatibilityMoment q = 0 := by
  constructor
  · rintro ⟨δ,hδ,hW⟩
    exact (signedOriginWeightedReflection_locally_memLp_two_iff q).1 ⟨δ,hδ,hW 2⟩
  · exact signed_origin_bounded_window q

/-- Small Gaussian scattering fails the full signed weighted L^(2 : ℕ) conclusion on every origin window. -/
theorem signedOriginWeightedReflection_globalSmallGaussian_not_memLp_two (a r : ℝ) :
    ¬ MemLp (signedOriginWeightedReflection (globalSmallScatteringPotential (compatibilityGaussian a))) 2
      (volume.restrict (Ioo (-(Real.exp r)) (Real.exp r))) := by
  intro h
  exact compatibilityMoment_globalSmallGaussian_ne_zero a
    ((signedOriginWeightedReflection_locally_memLp_two_iff _).1 ⟨Real.exp r,Real.exp_pos r,h⟩)

end
end GaloisForLFunctions.HTGeometry.FokasLenells
