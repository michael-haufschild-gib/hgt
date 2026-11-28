import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralFilling.UnivariateSublevel
import Mathlib.Probability.Distributions.Gaussian.Multivariate

/-! # Gaussian probability of an affine test of one winding -/

open MeasureTheory ProbabilityTheory Finset Set WithLp
open private standard_gaussian_le_volume from GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralFilling.UnivariateSublevel
namespace GaloisForLFunctions.HTGeometry.ReturnExcursions.AngularWindings
noncomputable section

/-- A normalized weighted sum of the original independent real fields is standard normal. -/
theorem normalized_field_law {I : Type*} [Fintype I] (v : I → ℝ)
    (hv : 0<‖toLp 2 v‖) :
    MeasurePreserving (fun g : I → ℝ => (∑ i, g i*v i)/‖toLp 2 v‖)
      (Measure.pi fun _ => gaussianReal 0 1) (gaussianReal 0 1) := by
  let E := EuclideanSpace ℝ I
  let σ := ‖toLp 2 v‖
  let L : StrongDual ℝ E := σ⁻¹ • innerSL ℝ (toLp 2 v)
  have hn : ‖L‖=1 := by
    rw [show L=σ⁻¹ • innerSL ℝ (toLp 2 v) from rfl,norm_smul,innerSL_apply_norm,
      Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hv),inv_mul_cancel₀ hv.ne']
  have hL : MeasurePreserving L (stdGaussian E) (gaussianReal 0 1) := by
    refine ⟨L.continuous.measurable,?_⟩
    rw [IsGaussian.map_eq_gaussianReal L,integral_strongDual_stdGaussian,variance_dual_stdGaussian,hn]
    simp
  have hX : MeasurePreserving (toLp 2 : (I→ℝ) → E) (Measure.pi fun _ => gaussianReal 0 1) (stdGaussian E) :=
    ⟨(MeasurableEquiv.toLp 2 (I→ℝ)).measurable,map_pi_eq_stdGaussian⟩
  convert hL.comp hX using 1
  funext g
  change _=σ⁻¹*inner ℝ (toLp 2 v) (toLp 2 g)
  simp only [PiLp.inner_apply,Real.inner_apply,div_eq_mul_inv,σ]
  rw [mul_comm _ (∑ i, v i*g i)]
  congr 1
  exact sum_congr rfl fun i _ => mul_comm _ _

/-- The affine center is arbitrary. The probability cost is the interval length divided
by the Euclidean norm of the coefficient vector, uniformly in the number of couplings. -/
theorem affine_slab_price {I : Type*} [Fintype I] (v : I → ℝ) (a δ : ℝ) (hδ : 0≤δ)
    (hv : 0<‖toLp 2 v‖) :
    (Measure.pi fun _ : I => gaussianReal 0 1).real {g | |a+∑ i, g i*v i| ≤ δ} ≤ 2*δ/‖toLp 2 v‖ := by
  let σ := ‖toLp 2 v‖
  let S := Icc ((-δ-a)/σ) ((δ-a)/σ)
  let f (g : I → ℝ) := (∑ i, g i*v i)/σ
  have hsub : {g : I → ℝ | |a+∑ i, g i*v i| ≤ δ} ⊆ f ⁻¹' S := by
    intro g hg
    change |a+∑ i, g i*v i|≤δ at hg
    obtain ⟨hl,hu⟩ := abs_le.mp hg
    exact ⟨div_le_div_of_nonneg_right (by linarith only [hl]) hv.le,
      div_le_div_of_nonneg_right (by linarith only [hu]) hv.le⟩
  refine (measureReal_mono hsub (measure_ne_top _ _)).trans ?_
  rw [(normalized_field_law v hv).measureReal_preimage measurableSet_Icc.nullMeasurableSet]
  have hvol := ENNReal.toReal_mono (measure_Icc_lt_top.ne) (standard_gaussian_le_volume S)
  change (gaussianReal 0 1).real S ≤ volume.real S at hvol
  apply hvol.trans
  rw [show volume.real S=(δ-a)/σ-(-δ-a)/σ from Real.volume_real_Icc_of_le
    (div_le_div_of_nonneg_right (by linarith only [hδ]) hv.le)]
  change _ ≤ 2*δ/σ
  exact le_of_eq (by ring)

#print axioms affine_slab_price
end
end GaloisForLFunctions.HTGeometry.ReturnExcursions.AngularWindings
