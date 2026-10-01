import GaloisForLFunctions.RHTower.PMPowerDampedMobiusDivisorHaar
import GaloisForLFunctions.RHTower.PMPowerDampedMobiusCriterion
import GaloisForLFunctions.RHTower.PMPowerDampedMobiusEndpoint
import Mathlib.MeasureTheory.Function.JacobianOneDim

open MeasureTheory Set Filter Topology Complex
noncomputable section
namespace RHTower

theorem pm_memLp_pos_dilate {f : ℝ → ℂ} (hm : Measurable f)
    (hf : MemLp f 2 (volume.restrict (Ioi (0 : ℝ)))) {a : ℝ} (ha : 0 < a) :
    MemLp (fun t => f (a * t)) 2 (volume.restrict (Ioi (0 : ℝ))) := by
  apply (memLp_two_iff_integrable_sq_norm
    (hm.comp (measurable_const.mul measurable_id)).aestronglyMeasurable).mpr
  have hi := (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mp hf
  exact (integrableOn_Ioi_comp_mul_left_iff (fun t => ‖f t‖ ^ (2 : ℕ)) 0 ha).mpr
    (by simpa only [IntegrableOn, mul_zero] using hi)

def pmBackwardDilation (f : ℝ → ℂ) (a t : ℝ) : ℂ := f (t / a) / (a : ℂ)

theorem measurable_pmBackwardDilation {f : ℝ → ℂ} (hm : Measurable f) (a : ℝ) :
    Measurable (pmBackwardDilation f a) :=
  (hm.comp (measurable_id.div_const a)).div_const (a : ℂ)

theorem memLp_pmBackwardDilation {f : ℝ → ℂ} (hm : Measurable f)
    (hf : MemLp f 2 (volume.restrict (Ioi (0 : ℝ)))) {a : ℝ} (ha : 0 < a) :
    MemLp (pmBackwardDilation f a) 2 (volume.restrict (Ioi (0 : ℝ))) := by
  have h := (pm_memLp_pos_dilate hm hf (one_div_pos.mpr ha)).mul_const ((a : ℂ)⁻¹)
  change MemLp (fun t => f (t / a) / (a : ℂ)) 2 (volume.restrict (Ioi (0 : ℝ)))
  simpa only [div_eq_mul_inv, one_mul, mul_one, mul_comm] using h

theorem pmBackwardDilation_energy (f : ℝ → ℂ) {a : ℝ} (ha : 0 < a) :
    (∫ t in Ioi (0 : ℝ), ‖pmBackwardDilation f a t‖ ^ 2) =
      a⁻¹ * ∫ t in Ioi (0 : ℝ), ‖f t‖ ^ 2 := by
  have he : (fun t => ‖pmBackwardDilation f a t‖ ^ 2) =
      fun t => ‖f ((1 / a) * t)‖ ^ 2 / a ^ 2 := by
    funext t
    dsimp only [pmBackwardDilation]
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha, div_pow,
      show t / a = (1 / a) * t by ring]
  rw [he, integral_div, integral_comp_mul_left_Ioi (fun t => ‖f t‖ ^ (2 : ℕ)) 0
    (one_div_pos.mpr ha), mul_zero, smul_eq_mul]
  field_simp

theorem pmBackwardDilation_lpNorm_sq {f : ℝ → ℂ} (hm : Measurable f)
    (hf : MemLp f 2 (volume.restrict (Ioi (0 : ℝ)))) {a : ℝ} (ha : 0 < a) :
    lpNorm (pmBackwardDilation f a) 2 (volume.restrict (Ioi (0 : ℝ))) ^ 2 =
      a⁻¹ * lpNorm f 2 (volume.restrict (Ioi (0 : ℝ))) ^ 2 := by
  have h := pmBackwardDilation_energy f ha
  rw [pm_integral_norm_sq_toLp (memLp_pmBackwardDilation hm hf ha),
    pm_integral_norm_sq_toLp hf, Lp.norm_toLp, Lp.norm_toLp,
    toReal_eLpNorm (memLp_pmBackwardDilation hm hf ha).aestronglyMeasurable,
    toReal_eLpNorm hf.aestronglyMeasurable] at h
  exact h

theorem pmBackwardDilation_pow_two_lpNorm {f : ℝ → ℂ} (hm : Measurable f)
    (hf : MemLp f 2 (volume.restrict (Ioi (0 : ℝ)))) (k : ℕ) :
    lpNorm (pmBackwardDilation f ((2 : ℝ) ^ k)) 2 (volume.restrict (Ioi (0 : ℝ))) =
      Real.sqrt (1 / 2) ^ k * lpNorm f 2 (volume.restrict (Ioi (0 : ℝ))) := by
  have hn := pmBackwardDilation_lpNorm_sq hm hf (by positivity : (0 : ℝ) < 2 ^ k)
  have hr : (Real.sqrt (1 / 2) ^ k) ^ 2 = ((2 : ℝ) ^ k)⁻¹ := by
    calc
      _ = (Real.sqrt (1 / 2) ^ 2) ^ k := by rw [← pow_mul, ← pow_mul, Nat.mul_comm]
      _ = _ := by rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 1 / 2)]; simp [one_div, inv_pow]
  have he : (Real.sqrt (1 / 2) ^ k * lpNorm f 2 (volume.restrict (Ioi (0 : ℝ)))) ^ 2 =
      ((2 : ℝ) ^ k)⁻¹ * lpNorm f 2 (volume.restrict (Ioi (0 : ℝ))) ^ 2 := by
    rw [mul_pow, hr]
  have hp : 0 ≤ Real.sqrt (1 / 2) ^ k * lpNorm f 2 (volume.restrict (Ioi (0 : ℝ))) :=
    mul_nonneg (pow_nonneg (Real.sqrt_nonneg _) _) lpNorm_nonneg
  nlinarith [lpNorm_nonneg (f := pmBackwardDilation f ((2 : ℝ) ^ k))
    (p := 2) (μ := volume.restrict (Ioi (0 : ℝ)))]

theorem pm_backward_dyadic_factor_sum :
    (∑' k : ℕ, Real.sqrt (1 / 2) ^ (k + 1)) = 1 + Real.sqrt 2 := by
  have hq0 := Real.sqrt_nonneg (1 / 2 : ℝ)
  have hq2 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hq1 : Real.sqrt (1 / 2) < 1 := by nlinarith
  have hqne : 1 - Real.sqrt (1 / 2) ≠ 0 := ne_of_gt (sub_pos.mpr hq1)
  have hs2 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hs0 := Real.sqrt_nonneg (2 : ℝ)
  have hs : Real.sqrt 2 = 2 * Real.sqrt (1 / 2) := by nlinarith
  simp_rw [pow_succ]
  rw [tsum_mul_right, tsum_geometric_of_lt_one hq0 hq1, hs]
  field_simp
  nlinarith

def pmBackwardDyadicPrefix (f : ℝ → ℂ) (N : ℕ) (t : ℝ) : ℂ :=
  -∑ k ∈ Finset.range N, pmBackwardDilation f ((2 : ℝ) ^ (k + 1)) t

theorem memLp_pmBackwardDyadicPrefix {f : ℝ → ℂ} (hm : Measurable f)
    (hf : MemLp f 2 (volume.restrict (Ioi (0 : ℝ)))) (N : ℕ) :
    MemLp (pmBackwardDyadicPrefix f N) 2 (volume.restrict (Ioi (0 : ℝ))) := by
  have h := memLp_finsetSum (Finset.range N) (fun k _ =>
    memLp_pmBackwardDilation hm hf (by positivity : (0 : ℝ) < 2 ^ (k + 1)))
  exact h.neg

theorem pmBackwardDyadicPrefix_norm_le {f : ℝ → ℂ} (hm : Measurable f)
    (hf : MemLp f 2 (volume.restrict (Ioi (0 : ℝ)))) (N : ℕ) :
    eLpNorm (pmBackwardDyadicPrefix f N) 2 (volume.restrict (Ioi (0 : ℝ))) ≤
      ENNReal.ofReal ((1 + Real.sqrt 2) * lpNorm f 2 (volume.restrict (Ioi (0 : ℝ)))) := by
  rw [← ofReal_lpNorm (memLp_pmBackwardDyadicPrefix hm hf N)]
  apply ENNReal.ofReal_le_ofReal
  have he : pmBackwardDyadicPrefix f N =
      -(∑ k ∈ Finset.range N, pmBackwardDilation f ((2 : ℝ) ^ (k + 1))) := by
    ext t
    simp [pmBackwardDyadicPrefix]
  rw [he, lpNorm_neg]
  calc
    _ ≤ ∑ k ∈ Finset.range N,
        lpNorm (pmBackwardDilation f ((2 : ℝ) ^ (k + 1))) 2 (volume.restrict (Ioi (0 : ℝ))) :=
      lpNorm_sum_le (fun k _ => memLp_pmBackwardDilation hm hf (by positivity)) (by norm_num)
    _ = (∑ k ∈ Finset.range N, Real.sqrt (1 / 2) ^ (k + 1)) *
        lpNorm f 2 (volume.restrict (Ioi (0 : ℝ))) := by
      simp_rw [pmBackwardDilation_pow_two_lpNorm hm hf]
      rw [Finset.sum_mul]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ lpNorm_nonneg
      rw [← pm_backward_dyadic_factor_sum]
      have hs : Summable (fun k : ℕ => Real.sqrt (1 / 2) ^ (k + 1)) := by
        simpa only [pow_succ] using summable_pmDyadicHaarTerm_norm.mul_right (Real.sqrt (1 / 2))
      exact hs.sum_le_tsum _ (fun k _ => pow_nonneg (Real.sqrt_nonneg _) _)

theorem pmPowerDampedCenteredSource_norm_le_of_admission {ε : ℝ} (hε : 0 < ε)
    (hf : MemLp (pmPowerDampedFermiSource ε) 2 (volume.restrict (Ioi (0 : ℝ)))) :
    eLpNorm (pmPowerDampedCenteredSource ε) 2 (volume.restrict (Ioi (0 : ℝ))) ≤
      ENNReal.ofReal ((1 + Real.sqrt 2) * lpNorm (pmPowerDampedFermiSource ε) 2
        (volume.restrict (Ioi (0 : ℝ)))) := by
  apply Lp.eLpNorm_le_of_ae_tendsto (u := (atTop : Filter ℕ))
    (Eventually.of_forall fun N => pmBackwardDyadicPrefix_norm_le
      (measurable_pmPowerDampedFermiSource ε) hf N)
    (fun N => (memLp_pmBackwardDyadicPrefix (measurable_pmPowerDampedFermiSource ε) hf N).aestronglyMeasurable)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  simpa only [pmBackwardDyadicPrefix, pmBackwardDilation, Complex.ofReal_pow,
    Complex.ofReal_ofNat] using tendsto_pmPowerDampedCenteredSource_dyadic_sum hε ht

theorem memLp_pmPowerDampedCenteredSource_of_admission {ε : ℝ} (hε : 0 < ε)
    (hf : MemLp (pmPowerDampedFermiSource ε) 2 (volume.restrict (Ioi (0 : ℝ)))) :
    MemLp (pmPowerDampedCenteredSource ε) 2 (volume.restrict (Ioi (0 : ℝ))) :=
  ⟨(measurable_pmPowerDampedCenteredSource ε).aestronglyMeasurable,
    (pmPowerDampedCenteredSource_norm_le_of_admission hε hf).trans_lt ENNReal.ofReal_lt_top⟩

theorem memLp_pmPowerDampedFermiSource_of_centered (ε : ℝ)
    (hf : MemLp (pmPowerDampedCenteredSource ε) 2 (volume.restrict (Ioi (0 : ℝ)))) :
    MemLp (pmPowerDampedFermiSource ε) 2 (volume.restrict (Ioi (0 : ℝ))) := by
  have hd := (pm_memLp_pos_dilate (measurable_pmPowerDampedCenteredSource ε) hf
    (by norm_num : (0 : ℝ) < 2)).const_mul (2 : ℂ)
  apply (memLp_congr_ae (show (pmPowerDampedCenteredSource ε -
    fun t => 2 * pmPowerDampedCenteredSource ε (2 * t)) =ᵐ[volume.restrict (Ioi (0 : ℝ))]
      pmPowerDampedFermiSource ε from ?_)).mp (hf.sub hd)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact (pmPowerDampedFermiSource_eq_centered_difference ε ht).symm

theorem pmPowerDampedFermiSource_memLp_iff_centered {ε : ℝ} (hε : 0 < ε) :
    MemLp (pmPowerDampedFermiSource ε) 2 (volume.restrict (Ioi (0 : ℝ))) ↔
      MemLp (pmPowerDampedCenteredSource ε) 2 (volume.restrict (Ioi (0 : ℝ))) :=
  ⟨memLp_pmPowerDampedCenteredSource_of_admission hε,
    memLp_pmPowerDampedFermiSource_of_centered ε⟩

theorem pm_inv_image_positive : (fun x : ℝ => x⁻¹) '' Ioi 0 = Ioi 0 := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    change 0 < y⁻¹
    exact inv_pos.mpr (show 0 < y from hy)
  · intro hx
    refine ⟨x⁻¹, ?_, inv_inv x⟩
    change 0 < x⁻¹
    exact inv_pos.mpr (show 0 < x from hx)

theorem pm_integrable_normSq_reciprocal_iff (f : ℝ → ℂ) :
    IntegrableOn (fun t => ‖f (1 / t)‖ ^ 2) (Ioi (0 : ℝ)) ↔
      IntegrableOn (fun x => ‖f x‖ ^ 2 / x ^ 2) (Ioi (0 : ℝ)) := by
  have h := integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioi
    (fun x hx => (hasDerivAt_inv (ne_of_gt hx)).hasDerivWithinAt)
    (show InjOn (fun x : ℝ => x⁻¹) (Ioi 0) from inv_injective.injOn)
    (fun t => ‖f (1 / t)‖ ^ (2 : ℕ))
  rw [pm_inv_image_positive] at h
  have he : (fun x : ℝ => |-(x ^ 2)⁻¹| • ‖f (1 / x⁻¹)‖ ^ 2) =
      fun x => ‖f x‖ ^ 2 / x ^ 2 := by
    funext x
    simp only [one_div, inv_inv, abs_neg, abs_inv, abs_of_nonneg (sq_nonneg x), smul_eq_mul]
    ring
  rw [he] at h
  exact h

theorem pm_integral_normSq_reciprocal (f : ℝ → ℂ) :
    (∫ t in Ioi (0 : ℝ), ‖f (1 / t)‖ ^ 2) =
      ∫ x in Ioi (0 : ℝ), ‖f x‖ ^ 2 / x ^ 2 := by
  have h := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi
    (fun x hx => (hasDerivAt_inv (ne_of_gt hx)).hasDerivWithinAt)
    (show InjOn (fun x : ℝ => x⁻¹) (Ioi 0) from inv_injective.injOn)
    (fun t => ‖f (1 / t)‖ ^ (2 : ℕ))
  rw [pm_inv_image_positive] at h
  convert h using 1
  congr 1
  funext x
  simp only [one_div, inv_inv, abs_neg, abs_inv, abs_of_nonneg (sq_nonneg x), smul_eq_mul]
  ring

theorem pmPowerDampedCenteredSource_energy (ε : ℝ) :
    (∫ t in Ioi (0 : ℝ), ‖pmPowerDampedCenteredSource ε t‖ ^ 2) =
      ∫ x in Ioi (0 : ℝ), ‖pmPowerDampedDivisorRemainder ε x‖ ^ 2 / x ^ 2 :=
  pm_integral_normSq_reciprocal (pmPowerDampedDivisorRemainder ε)

theorem pmPowerDampedFermiSource_memLp_iff_divisor_energy {ε : ℝ} (hε : 0 < ε) :
    MemLp (pmPowerDampedFermiSource ε) 2 (volume.restrict (Ioi (0 : ℝ))) ↔
      IntegrableOn (fun x => ‖pmPowerDampedDivisorRemainder ε x‖ ^ 2 / x ^ 2) (Ioi (0 : ℝ)) := by
  rw [pmPowerDampedFermiSource_memLp_iff_centered hε,
    memLp_two_iff_integrable_sq_norm (measurable_pmPowerDampedCenteredSource ε).aestronglyMeasurable]
  exact pm_integrable_normSq_reciprocal_iff (pmPowerDampedDivisorRemainder ε)

theorem integrable_pmPowerDampedDivisorEnergy_of_half_le {ε : ℝ} (hε : 1 / 2 ≤ ε) :
    IntegrableOn (fun x => ‖pmPowerDampedDivisorRemainder ε x‖ ^ 2 / x ^ 2) (Ioi (0 : ℝ)) :=
  (pmPowerDampedFermiSource_memLp_iff_divisor_energy (by linarith : 0 < ε)).mp
    (memLp_pmPowerDampedFermiSource_of_half_le hε)

theorem riemannHypothesis_of_pmPowerDamped_cofinal_divisor_energy
    (henergy : ∀ δ : ℝ, 0 < δ → ∃ ε : ℝ, 0 < ε ∧ ε < δ ∧
      IntegrableOn (fun x => ‖pmPowerDampedDivisorRemainder ε x‖ ^ 2 / x ^ 2) (Ioi (0 : ℝ))) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_pmPowerDamped_cofinal_admission
  intro δ hδ
  obtain ⟨ε, hε, hεδ, hi⟩ := henergy δ hδ
  exact ⟨ε, hε, hεδ, (pmPowerDampedFermiSource_memLp_iff_divisor_energy hε).mpr hi⟩

end RHTower
