import GaloisForLFunctions.HTGeometry.GaussianRadialAllLateHardnessTransferLaw
import GaloisForLFunctions.HTGeometry.GreedyBumpLocalGeometry

/-! # Positive correlation of clock survival with an upper radial cutoff -/
open MeasureTheory ProbabilityTheory Set Metric Real
open scoped ENNReal
namespace GaloisForLFunctions.HTGeometry.PassageMoments.DerivativeBounds
noncomputable section

/-- If each radial survival section is an initial segment, restriction to
a fixed initial segment retains at least its unconditional radius mass. -/
theorem radial_section_product {A R : Type*} [MeasurableSpace A] [MeasurableSpace R] [LinearOrder R]
    (μ : Measure A) (ν : Measure R) [IsProbabilityMeasure ν] (E : Set (A × R)) (hE : MeasurableSet E)
    (hdown : ∀ a, IsLowerSet (Prod.mk a ⁻¹' E)) (B : Set R) (hB : MeasurableSet B)
    (hl : IsLowerSet B) :
    (μ.prod ν) E * ν B ≤ (μ.prod ν) (E ∩ Prod.snd ⁻¹' B) := by
  rw [Measure.prod_apply hE,Measure.prod_apply (hE.inter (hB.preimage measurable_snd))]
  apply (lintegral_mul_const_le _ _).trans
  apply lintegral_mono
  intro a
  let S := Prod.mk a ⁻¹' E
  change ν S*ν B ≤ ν (S ∩ B)
  by_cases h : S ⊆ B
  · rw [inter_eq_self_of_subset_left h]
    exact mul_le_of_le_one_right' ((measure_mono (μ:=ν) (subset_univ B)).trans_eq measure_univ)
  · obtain ⟨r,hr,hout⟩ := Set.not_subset.mp h
    have hb : B ⊆ S := by
      intro s hs
      exact hdown a (le_of_not_ge (fun hr' => hout (hl hr' hs))) hr
    rw [inter_eq_self_of_subset_right hb]
    exact mul_le_of_le_one_left' ((measure_mono (μ:=ν) (subset_univ S)).trans_eq measure_univ)

/-- A Gaussian radius is at most twice its root mean square with
probability at least three quarters, in every positive dimension. -/
theorem gaussian_radius_mass (m : ℕ) (hm : 0 < m) :
    (3/4:ℝ) ≤ (gaussianRadiusMeasure m).real {r | r.val ≤ 2*sqrt (m:ℝ)} := by
  let α := gaussianAngularMeasure m
  let ν := gaussianRadiusMeasure m
  letI : IsProbabilityMeasure α := ⟨gaussianAngularMeasure_univ hm⟩
  letI : IsProbabilityMeasure ν := ⟨gaussianRadiusMeasure_univ hm⟩
  let B := {r : Ioi (0:ℝ) | r.val ≤ 2*sqrt (m:ℝ)}
  have hB : MeasurableSet B := measurableSet_le measurable_subtype_coe measurable_const
  have hp : 0<(m:ℝ) := Nat.cast_pos.mpr hm
  have hmean : (∫ r : Ioi (0:ℝ), r.val^2 ∂ν)=(m:ℝ) := by
    have h := integral_stdGaussian_independent_polar hm (fun x => ‖x‖^2)
    have he (p : sphere (0 : EuclideanSpace ℝ (Fin m)) 1 × Ioi (0:ℝ)) :
        ‖p.2.val • p.1.val‖^2 = p.2.val^2 := by
      rw [norm_smul,Real.norm_eq_abs,abs_of_pos p.2.property,norm_eq_of_mem_sphere,mul_one]
    simp_rw [he] at h
    rw [greedyBump_integral_norm_sq_stdGaussian] at h
    have heq := integral_fun_snd (μ:=α) (ν:=ν) (fun r : Ioi (0:ℝ) => r.val^2)
    rw [probReal_univ,one_smul] at heq
    exact heq.symm.trans h.symm
  have hi : Integrable (fun r : Ioi (0:ℝ) => r.val^2) ν := by
    by_contra hn
    rw [integral_undef hn] at hmean
    exact hp.ne' hmean.symm
  have hmark := mul_meas_ge_le_integral_of_nonneg (μ:=ν)
    (ae_of_all _ fun r : Ioi (0:ℝ) => sq_nonneg r.val) hi (4*(m:ℝ))
  rw [hmean] at hmark
  have hs : Bᶜ ⊆ {r : Ioi (0:ℝ) | 4*(m:ℝ)≤r.val^2} := by
    intro r hr
    have hx : 2*sqrt (m:ℝ)<r.val := lt_of_not_ge hr
    have hs := mul_self_le_mul_self (mul_nonneg two_pos.le (sqrt_nonneg _)) hx.le
    change 4*(m:ℝ) ≤ r.val^2
    nlinarith only [hs,sq_sqrt hp.le]
  have hc := (mul_le_mul_of_nonneg_left (measureReal_mono (μ:=ν) hs) (by positivity : 0≤4*(m:ℝ))).trans hmark
  rw [measureReal_compl hB,probReal_univ] at hc
  change 3/4 ≤ ν.real B
  by_contra! hh
  nlinarith only [hc,mul_lt_mul_of_pos_left hh hp]

#print axioms gaussian_radius_mass
end
end GaloisForLFunctions.HTGeometry.PassageMoments.DerivativeBounds
