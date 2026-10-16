import GaloisForLFunctions.HTGeometry.BoundedVariationTranslationIntegral
import GaloisForLFunctions.RHTower.CHMDFullJumpCoreDensity

/-! # BV profiles enter the complete arithmetic source

The first Gamma jump moment consumes the variation modulus. The finite full
prime-edge measure consumes boundedness. Together they admit the literal BV
profile, with all jumps retained, into the complete compact-test source graph.
-/

noncomputable section
open MeasureTheory Set Filter Topology

namespace RHTower.CHMDDoobGraph
open GaloisForLFunctions.HTGeometry CHMDClosedJump

theorem archLevy_firstMoment_le {h : ℝ} (hh : 0 < h) :
    h * archLevyDensity h ≤ (h+1/2)*Real.exp (-h/2) := by
  have he := Real.add_one_le_exp (2*h)
  have hexp := Real.exp_pos (2*h)
  have hden : 0 < 1-Real.exp (-2*h) := by
    have := Real.exp_lt_one_iff.mpr (show -2*h < 0 by linarith)
    linarith
  have hx : h ≤ (h+1/2)*(1-Real.exp (-2*h)) := by
    rw [show -2*h = -(2*h) by ring, Real.exp_neg]
    have he' : (h+1/2)*(Real.exp (2*h))⁻¹ ≤ 1/2 := by
      rw [mul_inv_le_iff₀ hexp]
      linarith
    nlinarith
  unfold archLevyDensity
  rw [← mul_div_assoc, div_le_iff₀ hden]
  nlinarith [mul_le_mul_of_nonneg_right hx (Real.exp_pos (-h/2)).le]

theorem integrable_archLevy_firstMoment :
    IntegrableOn (fun h : ℝ => h*archLevyDensity h) (Ioi 0) := by
  have hlin : IntegrableOn (fun h : ℝ => h*Real.exp (-h/2)) (Ioi 0) := by
    convert
      (integrableOn_rpow_mul_exp_neg_mul_rpow (s := 1) (p := 1) (b := 1/2)
        (by norm_num) le_rfl (by norm_num)) using 1
    funext h
    simp only [Real.rpow_one]
    congr 2
    ring
  have hexp := (integrableOn_exp_mul_Ioi (a := -(1/2:ℝ)) (by norm_num) 0).const_mul (1/2:ℝ)
  have hmajor : IntegrableOn (fun h : ℝ => (h+1/2)*Real.exp (-h/2)) (Ioi 0) := by
    apply (hlin.add hexp).congr
    filter_upwards [] with h
    dsimp
    rw [show -(1/2:ℝ)*h = -h/2 by ring]
    ring
  apply hmajor.mono' ((measurable_id.mul measurable_archLevyDensity).aestronglyMeasurable)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with h hh
  change ‖h*archLevyDensity h‖ ≤ _
  rw [Real.norm_of_nonneg (mul_nonneg hh.le (archLevyDensity_pos hh).le)]
  exact archLevy_firstMoment_le hh

theorem bv_memLp_mass {v : ℝ → ℝ} (hv : BoundedVariationOn v univ) :
    MemLp v 2 massMeasure :=
  (memLp_top_of_bound (measurable_of_boundedVariation_univ hv).aestronglyMeasurable
    (‖v 0‖+(eVariationOn v univ).toReal)
    (Eventually.of_forall (norm_le_of_boundedVariation_univ hv))).mono_exponent le_top

theorem bv_memLp_prime_difference {v : ℝ → ℝ} (hv : BoundedVariationOn v univ) :
    MemLp (difference v) 2 (Measure.sum primeMeasure) := by
  apply (memLp_top_of_bound (measurable_difference
    (measurable_of_boundedVariation_univ hv)).aestronglyMeasurable
      (2*(‖v 0‖+(eVariationOn v univ).toReal)) ?_).mono_exponent le_top
  exact Eventually.of_forall fun e => (norm_sub_le _ _).trans (by
    have hl := norm_le_of_boundedVariation_univ hv (left e)
    have hr := norm_le_of_boundedVariation_univ hv (right e)
    linarith)

private theorem bv_stationary_integrable {v : ℝ → ℝ} (hv : BoundedVariationOn v univ) :
    Integrable (fun e : ℝ × ℝ => archLevyDensity e.1 * difference v e ^ 2) archBase := by
  have hm : Measurable (fun e : ℝ × ℝ => archLevyDensity e.1 * difference v e ^ 2) :=
    (measurable_archLevyDensity.comp measurable_fst).mul
    ((measurable_difference (measurable_of_boundedVariation_univ hv)).pow_const 2)
  apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
  constructor
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with h hh
    exact (boundedVariation_translation_sq hv hh.le).1.const_mul _
  · let C := 4*(‖v 0‖+(eVariationOn v univ).toReal)*(eVariationOn v univ).toReal
    apply (integrable_archLevy_firstMoment.const_mul C).mono'
      hm.stronglyMeasurable.norm.integral_prod_right'.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with h hh
    have hn (x : ℝ) : ‖archLevyDensity h*difference v (h,x)^2‖ =
        archLevyDensity h*(v x-v (x+h))^2 := by
      rw [Real.norm_of_nonneg (mul_nonneg (archLevyDensity_pos hh).le (sq_nonneg _))]
      rfl
    simp only [hn, integral_const_mul]
    rw [Real.norm_of_nonneg (mul_nonneg (archLevyDensity_pos hh).le
      (integral_nonneg fun x => sq_nonneg _))]
    have hb := mul_le_mul_of_nonneg_left (boundedVariation_translation_sq hv hh.le).2
      (archLevyDensity_pos hh).le
    simpa only [C, Real.norm_eq_abs, mul_assoc, mul_comm, mul_left_comm] using hb

theorem bv_integrable_arch_weighted_sq {v : ℝ → ℝ}
    (hv : BoundedVariationOn v univ) :
    Integrable (fun e => archWeight e*difference v e^2) archBase := by
  obtain ⟨C, hC, hb, _⟩ := theta_global_and_exponential_bound
  apply ((bv_stationary_integrable hv).const_mul (C^2)).mono'
    ((measurable_archWeight.mul
      ((measurable_difference (measurable_of_boundedVariation_univ hv)).pow_const 2)).aestronglyMeasurable)
  have hh : ∀ᵐ e ∂archBase, e.1 ∈ Ioi (0 : ℝ) :=
    Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Ioi)
  filter_upwards [hh] with e he
  change ‖archWeight e*difference v e^2‖ ≤ _
  have ht := (archLevyDensity_pos he).le
  have htheta := mul_le_mul (hb e.2) (hb (e.2+e.1)) (riemannKernelReal_pos _).le hC
  have hw : 0 ≤ archWeight e := mul_nonneg
    (mul_nonneg ht (riemannKernelReal_pos e.2).le) (riemannKernelReal_pos (e.2+e.1)).le
  rw [Real.norm_of_nonneg (mul_nonneg hw (sq_nonneg _))]
  dsimp only [archWeight]
  nlinarith [mul_le_mul_of_nonneg_left htheta (mul_nonneg ht (sq_nonneg (difference v e)))]

theorem bv_memLp_difference {v : ℝ → ℝ} (hv : BoundedVariationOn v univ) :
    MemLp (difference v) 2 edgeMeasure := by
  rw [memLp_two_iff_integrable_sq
    (measurable_difference (measurable_of_boundedVariation_univ hv)).aestronglyMeasurable]
  have ha : Integrable (fun e => difference v e^2) archMeasure := by
    rw [archMeasure, integrable_weighted_iff archBase measurable_archWeight archWeight_nonneg_ae]
    exact bv_integrable_arch_weighted_sq hv
  exact ha.add_measure (bv_memLp_prime_difference hv).integrable_sq

/-- Every globally BV profile is an actual vector of the complete arithmetic domain. -/
def bvLift (v : ℝ → ℝ) (hv : BoundedVariationOn v univ) : SourceGraph :=
  ofFunction massMeasure edgeMeasure left right nonsingular_left nonsingular_right v
    (bv_memLp_mass hv) (bv_memLp_difference hv)

theorem bvLift_source (v : ℝ → ℝ) (hv : BoundedVariationOn v univ) :
    (bvLift v hv).val.fst =ᵐ[massMeasure] v := (bv_memLp_mass hv).coeFn_toLp

theorem integral_prime_sq_measurable {v : ℝ → ℝ} (hv : Measurable v) (n : ℕ) :
    (∫ e, difference v e^2 ∂primeMeasure n) = ∫ x, phiDoobPrimeJump v n x := by
  rw [primeMeasure, integral_map (by fun_prop)
    ((measurable_difference hv).pow_const 2).aestronglyMeasurable,
    integral_weighted volume (continuous_primeWeight n).measurable
      (Eventually.of_forall (primeWeight_nonneg n))]
  rfl

theorem bv_integral_arch_sq {v : ℝ → ℝ} (hv : BoundedVariationOn v univ) :
    (∫ e, difference v e^2 ∂archMeasure) = phiDoobArchJumpEnergy v := by
  rw [archMeasure, integral_weighted archBase measurable_archWeight archWeight_nonneg_ae,
    archBase, integral_prod _ (bv_integrable_arch_weighted_sq hv)]
  simp only [archWeight_mul_sq, integral_const_mul]
  rfl

/-- Every prime power, the Gamma continuum and the signed mass survive BV admission. -/
theorem sourceEnergy_bvLift (v : ℝ → ℝ) (hv : BoundedVariationOn v univ) :
    sourceEnergy (bvLift v hv) = phiDoobArchJumpEnergy v +
      (∑' n, ∫ x, phiDoobPrimeJump v n x) - phiDoobCoshMass (fun x => v x^2) := by
  rw [sourceEnergy, bvLift, energy_ofFunction]
  change (∫ e, difference v e^2 ∂edgeMeasure) - _ = _
  have ha : Integrable (fun e => difference v e^2) archMeasure := by
    rw [archMeasure, integrable_weighted_iff archBase measurable_archWeight archWeight_nonneg_ae]
    exact bv_integrable_arch_weighted_sq hv
  have hp := (bv_memLp_prime_difference hv).integrable_sq
  rw [edgeMeasure, integral_add_measure ha hp, bv_integral_arch_sq hv,
    integral_sum_measure hp, integral_mass_sq]
  simp only [integral_prime_sq_measurable (measurable_of_boundedVariation_univ hv)]

/-- Charged and singular BV profiles are limits of the original compact smooth tests. -/
theorem bvLift_mem_compactTests_closure (v : ℝ → ℝ) (hv : BoundedVariationOn v univ) :
    bvLift v hv ∈ closure (compactTests : Set SourceGraph) := dense_compactTests _

/-- Nonlinear C1 responses of every admitted BV profile remain in the same arithmetic domain. -/
theorem boundedVariation_c1_comp {v F : ℝ → ℝ} (hv : BoundedVariationOn v univ)
    (hF : ContDiff ℝ 1 F) : BoundedVariationOn (fun x => F (v x)) univ := by
  let B := ‖v 0‖+(eVariationOn v univ).toReal
  obtain ⟨K, hK⟩ := (hF.contDiffOn (s := Icc (-B) B)).exists_lipschitzOnWith
    (by decide) (convex_Icc _ _) isCompact_Icc
  apply hK.comp_boundedVariationOn _ hv
  intro x _
  have hx := norm_le_of_boundedVariation_univ hv x
  exact abs_le.mp (by simpa only [B, Real.norm_eq_abs] using hx)

theorem boundedVariation_polynomial_comp {v : ℝ → ℝ} (hv : BoundedVariationOn v univ)
    (P : Polynomial ℝ) : BoundedVariationOn (fun x => P.eval (v x)) univ := by
  have hP : ContDiff ℝ 1 (fun x : ℝ => P.eval x) := by
    simpa using P.contDiff_aeval (𝕜 := ℝ) 1
  exact boundedVariation_c1_comp (v := v) (F := fun x : ℝ => P.eval x) hv hP

end RHTower.CHMDDoobGraph
