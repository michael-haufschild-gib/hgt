import GaloisForLFunctions.ArithmeticIndexDescent.TheGammaBoundaryBoundHasNoNonzeroEqualityCase

/-!
# Mixed equality and norm rigidity of the actual Gamma operator

Zero mixed reserve forces both weighted profiles to have the same constant
ratio. The Schur weight is not square integrable, so that constant vanishes.
Applying this classification to a vector and its Gamma image excludes every
nonzero vector from attaining the critical norm bound.
-/

noncomputable section

open MeasureTheory Set Filter Complex
open scoped ENNReal InnerProduct
open RHTower

namespace GaloisForLFunctions.ArithmeticIndexDescent

local notation "μ₊" => (volume.restrict (Ioi (0 : ℝ)))

private theorem mixed_zero_forces_left_zero (f g : SuzukiPositiveL2)
    (hI : (∫ p, gammaBoundaryPairReserveDensity f g p ∂(μ₊.prod μ₊)) = 0) : f = 0 := by
  have hpos : ∀ᵐ p : ℝ × ℝ ∂(μ₊.prod μ₊), 0 < p.1 ∧ 0 < p.2 := by
    rw [Measure.prod_restrict]
    exact ae_restrict_mem (measurableSet_Ioi.prod measurableSet_Ioi)
  have hnn : 0 ≤ᵐ[μ₊.prod μ₊] gammaBoundaryPairReserveDensity f g := by
    filter_upwards [hpos] with p hp
    exact gammaBoundaryPairReserveDensity_nonneg f g hp.1 hp.2
  have hzero := (integral_eq_zero_iff_of_nonneg_ae hnn
    (integrable_gammaBoundaryPairReserveDensity f g)).mp hI
  have hratio : ∀ᵐ p : ℝ × ℝ ∂(μ₊.prod μ₊),
      g p.1 / (gammaBoundarySchurWeight p.1 : ℂ) =
        f p.2 / (gammaBoundarySchurWeight p.2 : ℂ) := by
    filter_upwards [hpos, hzero] with p hp hz
    change gammaBoundaryPairReserveDensity f g p = 0 at hz
    unfold gammaBoundaryPairReserveDensity at hz
    have hk : archLevyDensity (p.1 + p.2) * gammaBoundarySchurWeight p.1 *
        gammaBoundarySchurWeight p.2 ≠ 0 :=
      mul_ne_zero (mul_ne_zero (archLevyDensity_pos (add_pos hp.1 hp.2)).ne'
        (gammaBoundarySchurWeight_pos hp.1).ne') (gammaBoundarySchurWeight_pos hp.2).ne'
    have hsq : ‖g p.1 / (gammaBoundarySchurWeight p.1 : ℂ) -
        f p.2 / (gammaBoundarySchurWeight p.2 : ℂ)‖ ^ 2 = 0 :=
      (mul_eq_zero.mp ((div_eq_zero_iff.mp hz).resolve_right (by norm_num))).resolve_left hk
    have hn : ‖g p.1 / (gammaBoundarySchurWeight p.1 : ℂ) -
        f p.2 / (gammaBoundarySchurWeight p.2 : ℂ)‖ = 0 := by
      nlinarith only [hsq]
    exact sub_eq_zero.mp (norm_eq_zero.mp hn)
  letI : NeZero μ₊ := ⟨by
    intro h
    have he := congrArg (fun m : Measure ℝ => m Set.univ) h
    change μ₊ Set.univ = 0 at he
    rw [Measure.restrict_apply MeasurableSet.univ, univ_inter, Real.volume_Ioi] at he
    exact ENNReal.top_ne_zero he⟩
  obtain ⟨s, hs⟩ := (Measure.ae_ae_of_ae_prod hratio).exists
  let c : ℂ := g s / (gammaBoundarySchurWeight s : ℂ)
  have hconst : (f : ℝ → ℂ) =ᵐ[μ₊] fun t => c * (gammaBoundarySchurWeight t : ℂ) := by
    filter_upwards [hs, ae_restrict_mem measurableSet_Ioi] with t ht htp
    have hw : (gammaBoundarySchurWeight t : ℂ) ≠ 0 := by
      exact_mod_cast (gammaBoundarySchurWeight_pos htp).ne'
    exact (div_eq_iff hw).mp ht.symm
  have hi : Integrable (fun t => ‖f t‖ ^ 2) μ₊ :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable f)).mp (Lp.memLp f)
  have hic : IntegrableOn (fun t => ‖c * (gammaBoundarySchurWeight t : ℂ)‖ ^ 2)
      (Ioi (0 : ℝ)) := by
    refine hi.congr ?_
    filter_upwards [hconst] with t ht
    rw [ht]
  have hc : c = 0 := (integrable_sq_mul_gammaBoundarySchurWeight_iff c).mp hic
  apply Lp.ext
  filter_upwards [hconst, Lp.coeFn_zero ℂ 2 μ₊] with t ht hz
  rw [hc, zero_mul] at ht
  exact ht.trans hz.symm

/-- Only the zero pair has zero mixed square reserve on the original L2 carrier. -/
theorem gammaBoundary_pair_reserve_eq_zero_iff (f g : SuzukiPositiveL2) :
    (∫ p, gammaBoundaryPairReserveDensity f g p ∂(μ₊.prod μ₊)) = 0 ↔ f = 0 ∧ g = 0 := by
  constructor
  · intro hI
    have hf := mixed_zero_forces_left_zero f g hI
    refine ⟨hf, ?_⟩
    rw [integral_gammaBoundaryPairReserveDensity, hf, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
      zero_add, map_zero, inner_zero_right, Complex.zero_re, sub_zero] at hI
    have hsq : ‖g‖ ^ 2 = 0 :=
      (mul_eq_zero.mp hI).resolve_left (div_pos Real.pi_pos (by norm_num)).ne'
    apply norm_eq_zero.mp
    nlinarith only [hsq]
  · rintro ⟨rfl, rfl⟩
    rw [integral_gammaBoundaryPairReserveDensity]
    simp

/-- Every nonzero input has strict norm deficit, without a uniform gap. -/
theorem norm_ccmGammaBoundaryCLM_apply_lt {f : SuzukiPositiveL2} (hf : f ≠ 0) :
    ‖ccmGammaBoundaryCLM f‖ < (Real.pi / 2) * ‖f‖ := by
  let C : ℝ := Real.pi / 2
  have hC : 0 < C := div_pos Real.pi_pos (by norm_num)
  have hle : ‖ccmGammaBoundaryCLM f‖ ≤ C * ‖f‖ :=
    (ccmGammaBoundaryCLM.le_opNorm f).trans
      (mul_le_mul_of_nonneg_right norm_ccmGammaBoundaryCLM_le_pi_half (norm_nonneg _))
  by_contra hnot
  have heq : ‖ccmGammaBoundaryCLM f‖ = C * ‖f‖ :=
    le_antisymm hle (le_of_not_gt hnot)
  have hnorm : ‖(C : ℂ) • f‖ = C * ‖f‖ := by
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hC]
  have hinner : (inner ℂ (ccmGammaBoundaryCLM f)
      (ccmGammaBoundaryCLM ((C : ℂ) • f))).re = C * ‖ccmGammaBoundaryCLM f‖ ^ 2 := by
    rw [map_smul, inner_smul_right]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    have h := inner_self_eq_norm_sq (𝕜 := ℂ) (ccmGammaBoundaryCLM f)
    simpa only [RCLike.re_to_complex] using congrArg (fun x : ℝ => C * x) h
  have hI : (∫ p, gammaBoundaryPairReserveDensity ((C : ℂ) • f)
      (ccmGammaBoundaryCLM f) p ∂(μ₊.prod μ₊)) = 0 := by
    rw [integral_gammaBoundaryPairReserveDensity, hnorm, hinner, heq]
    dsimp only [C]
    ring
  have hz := ((gammaBoundary_pair_reserve_eq_zero_iff _ _).mp hI).1
  have hc : (C : ℂ) ≠ 0 := by exact_mod_cast hC.ne'
  exact hf ((smul_eq_zero.mp hz).resolve_left hc)

end GaloisForLFunctions.ArithmeticIndexDescent

#print axioms GaloisForLFunctions.ArithmeticIndexDescent.gammaBoundary_pair_reserve_eq_zero_iff
#print axioms GaloisForLFunctions.ArithmeticIndexDescent.norm_ccmGammaBoundaryCLM_apply_lt
