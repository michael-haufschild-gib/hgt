import GaloisForLFunctions.RHTower.PMPowerDampedMobiusL1Convergence
import GaloisForLFunctions.RHTower.ChebyshevDyadicWeightedEnergy
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# Strong L¹ derivative of the canonical power-damped Möbius source

The actual positive-damping difference quotients converge in canonical L¹(dt)
to the dyadic Chebyshev source. Its signed integral is exactly log 2.
The summable majorant comes from the certified raw-prefix L¹ errors.
-/

open MeasureTheory Set Filter Topology Complex
noncomputable section
namespace RHTower


def pmDyadicChebyshevSource (t : ℝ) : ℂ := (dyadicChebyshevError (1 / t) : ℂ)

def pmPowerDampedDifferenceQuotient (ε t : ℝ) : ℂ :=
  ε⁻¹ • (pmPowerDampedFermiSource ε t - dyadicHaar t)

theorem measurable_pmDyadicChebyshevSource : Measurable pmDyadicChebyshevSource :=
  Complex.measurable_ofReal.comp (measurable_dyadicChebyshevError.comp
    (measurable_const.div measurable_id))

theorem measurable_pmPowerDampedDifferenceQuotient (ε : ℝ) :
    Measurable (pmPowerDampedDifferenceQuotient ε) :=
  ((measurable_pmPowerDampedFermiSource ε).sub measurable_dyadicHaar).const_smul (ε⁻¹ : ℝ)

theorem tendsto_pmPowerDampedDifferenceQuotient {t : ℝ} (ht : t ∈ Ioc (0 : ℝ) 1) :
    Tendsto (fun ε : ℝ => pmPowerDampedDifferenceQuotient ε t) (𝓝[>] 0)
      (𝓝 (pmDyadicChebyshevSource t)) := by
  have h := (hasDerivAt_pmPowerDampedFermiSource_zero ht.1).tendsto_slope_zero_right
  have hd : pmDyadicChebyshevSource t =
      ((Chebyshev.psi (1 / t) - 2 * Chebyshev.psi (1 / (2 * t)) : ℝ) : ℂ) := by
    unfold pmDyadicChebyshevSource dyadicChebyshevError
    rw [show (1 / t) / 2 = 1 / (2 * t) by ring]
  rw [hd]
  simpa only [zero_add, pmPowerDampedFermiSource_zero_eq_haar ht,
    pmPowerDampedDifferenceQuotient] using h

theorem pmPowerDampedDifferenceQuotient_norm_le {ε : ℝ} (hε : 0 < ε) :
    eLpNorm (pmPowerDampedDifferenceQuotient ε) 1 (volume.restrict (Ioc (0 : ℝ) 1)) ≤
      ENNReal.ofReal (∑' n : ℕ, pmRawFermiL1Error n / (n : ℝ)) := by
  change eLpNorm (ε⁻¹ • (fun t => pmPowerDampedFermiSource ε t - dyadicHaar t)) 1 _ ≤ _
  rw [eLpNorm_const_smul, ← ofReal_norm, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hε)]
  calc
    _ ≤ ENNReal.ofReal ε⁻¹ * ENNReal.ofReal (ε * ∑' n : ℕ, pmRawFermiL1Error n / (n : ℝ)) :=
      mul_le_mul_right (pmPowerDampedFermiSource_haar_L1_error_le hε) _
    _ = _ := by
      rw [← ENNReal.ofReal_mul (inv_nonneg.mpr hε.le)]
      congr 1
      simp [hε.ne']

theorem pmDyadicChebyshevSource_L1_norm_le :
    eLpNorm pmDyadicChebyshevSource 1 (volume.restrict (Ioc (0 : ℝ) 1)) ≤
      ENNReal.ofReal (∑' n : ℕ, pmRawFermiL1Error n / (n : ℝ)) := by
  have hb : ∀ᶠ ε in 𝓝[>] (0 : ℝ), eLpNorm (pmPowerDampedDifferenceQuotient ε) 1
      (volume.restrict (Ioc (0 : ℝ) 1)) ≤
        ENNReal.ofReal (∑' n : ℕ, pmRawFermiL1Error n / (n : ℝ)) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact pmPowerDampedDifferenceQuotient_norm_le hε
  apply Lp.eLpNorm_le_of_ae_tendsto hb
    (fun ε => (measurable_pmPowerDampedDifferenceQuotient ε).aestronglyMeasurable)
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  exact tendsto_pmPowerDampedDifferenceQuotient ht

theorem integrable_pmDyadicChebyshevSource :
    Integrable pmDyadicChebyshevSource (volume.restrict (Ioc (0 : ℝ) 1)) := by
  apply memLp_one_iff_integrable.mp
  exact ⟨measurable_pmDyadicChebyshevSource.aestronglyMeasurable,
    pmDyadicChebyshevSource_L1_norm_le.trans_lt ENNReal.ofReal_lt_top⟩


def pmLogDampingGap (n : ℕ) : ℝ := Real.log ((n + 1 : ℕ) : ℝ) - Real.log (n : ℝ)

theorem hasDerivAt_pmPowerDampingGap_zero {n : ℕ} (hn : 1 ≤ n) :
    HasDerivAt (fun ε : ℝ => pmPowerDampingGap ε n) (pmLogDampingGap n) 0 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  have hneg : HasDerivAt (fun ε : ℝ => -ε) (-1) 0 := (hasDerivAt_id 0).neg
  have hd := (hneg.const_rpow hn0).sub (hneg.const_rpow hn1)
  convert hd using 1 <;> first | rfl | (simp [pmLogDampingGap]; ring)

theorem tendsto_pmPowerDampingGap_div {n : ℕ} (hn : 1 ≤ n) :
    Tendsto (fun ε : ℝ => pmPowerDampingGap ε n / ε) (𝓝[>] 0)
      (𝓝 (pmLogDampingGap n)) := by
  have h := (hasDerivAt_pmPowerDampingGap_zero hn).tendsto_slope_zero_right
  simpa only [zero_add, pmPowerDampingGap, neg_zero, Real.rpow_zero, sub_self,
    sub_zero, smul_eq_mul, div_eq_mul_inv, mul_comm] using h

theorem pmPowerDampingGap_div_le {ε : ℝ} (hε : 0 < ε) {n : ℕ} (hn : 1 ≤ n) :
    pmPowerDampingGap ε n / ε ≤ 1 / (n : ℝ) := by
  apply (div_le_iff₀ hε).2
  simpa only [div_eq_mul_inv, one_mul, mul_comm, mul_one] using pmPowerDampingGap_le hε hn

theorem pmLogDampingGap_nonneg {n : ℕ} (hn : 1 ≤ n) : 0 ≤ pmLogDampingGap n := by
  apply ge_of_tendsto (tendsto_pmPowerDampingGap_div hn)
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact div_nonneg (pmPowerDampingGap_nonneg hε hn) (le_of_lt hε)

theorem pmLogDampingGap_le {n : ℕ} (hn : 1 ≤ n) : pmLogDampingGap n ≤ 1 / (n : ℝ) := by
  apply le_of_tendsto (tendsto_pmPowerDampingGap_div hn)
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact pmPowerDampingGap_div_le hε hn

def pmDampingDerivativeMajorant (ε : ℝ) (n : ℕ) : ℝ :=
  if 1 ≤ n then |pmPowerDampingGap ε n / ε - pmLogDampingGap n| * pmRawFermiL1Error n else 0

theorem pmDampingDerivativeMajorant_nonneg (ε : ℝ) (n : ℕ) :
    0 ≤ pmDampingDerivativeMajorant ε n := by
  unfold pmDampingDerivativeMajorant
  split_ifs
  · exact mul_nonneg (abs_nonneg _) (pmRawFermiL1Error_nonneg n)
  · rfl

theorem pmDampingDerivativeMajorant_le {ε : ℝ} (hε : 0 < ε) (n : ℕ) :
    pmDampingDerivativeMajorant ε n ≤ 2 * (pmRawFermiL1Error n / (n : ℝ)) := by
  unfold pmDampingDerivativeMajorant
  split_ifs with hn
  · have hA : 0 ≤ pmPowerDampingGap ε n / ε :=
      div_nonneg (pmPowerDampingGap_nonneg hε hn) hε.le
    have hB := pmLogDampingGap_nonneg hn
    have hsum : |pmPowerDampingGap ε n / ε - pmLogDampingGap n| ≤ 2 / (n : ℝ) := by
      calc
        _ ≤ |pmPowerDampingGap ε n / ε| + |pmLogDampingGap n| := abs_sub _ _
        _ ≤ 2 / (n : ℝ) := by
          rw [abs_of_nonneg hA, abs_of_nonneg hB]
          calc
            _ ≤ 1 / (n : ℝ) + 1 / (n : ℝ) :=
              add_le_add (pmPowerDampingGap_div_le hε hn) (pmLogDampingGap_le hn)
            _ = _ := by ring
    calc
      _ ≤ (2 / (n : ℝ)) * pmRawFermiL1Error n :=
        mul_le_mul_of_nonneg_right hsum (pmRawFermiL1Error_nonneg n)
      _ = _ := by ring
  · exact mul_nonneg (by norm_num) (div_nonneg (pmRawFermiL1Error_nonneg n) (Nat.cast_nonneg n))

theorem summable_pmDampingDerivativeMajorant {ε : ℝ} (hε : 0 < ε) :
    Summable (pmDampingDerivativeMajorant ε) := by
  apply (summable_pmRawFermiL1Error_div.mul_left 2).of_nonneg_of_le
    (pmDampingDerivativeMajorant_nonneg ε)
  exact pmDampingDerivativeMajorant_le hε

theorem tendsto_pmDampingDerivativeMajorant_tsum :
    Tendsto (fun ε : ℝ => ∑' n : ℕ, pmDampingDerivativeMajorant ε n) (𝓝[>] 0) (𝓝 0) := by
  have hlim (n : ℕ) : Tendsto (fun ε : ℝ => pmDampingDerivativeMajorant ε n)
      (𝓝[>] 0) (𝓝 (0 : ℝ)) := by
    by_cases hn : 1 ≤ n
    · have h := ((tendsto_pmPowerDampingGap_div hn).sub_const (pmLogDampingGap n)).abs.mul_const
        (pmRawFermiL1Error n)
      simpa [pmDampingDerivativeMajorant, hn] using h
    · simp [pmDampingDerivativeMajorant, hn]
  have h := tendsto_tsum_of_dominated_convergence
    (summable_pmRawFermiL1Error_div.mul_left 2) hlim
    (show ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ n : ℕ,
      ‖pmDampingDerivativeMajorant ε n‖ ≤ 2 * (pmRawFermiL1Error n / (n : ℝ)) from ?_)
  · simpa using h
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    intro n
    rw [Real.norm_eq_abs, abs_of_nonneg (pmDampingDerivativeMajorant_nonneg ε n)]
    exact pmDampingDerivativeMajorant_le hε n


theorem pmPowerDampedDifferenceQuotient_eq_sum (ε : ℝ) {t : ℝ}
    (ht : t ∈ Ioc (0 : ℝ) 1) {N : ℕ} (hN : ⌊1 / t⌋₊ ≤ N) :
    pmPowerDampedDifferenceQuotient ε t =
      ∑ n ∈ Finset.Icc 1 N, ((pmPowerDampingGap ε n / ε : ℝ) : ℂ) *
        (rawMobiusFermiApprox n t - dyadicHaar t) := by
  unfold pmPowerDampedDifferenceQuotient
  rw [← pmPowerDampedAbelError_eq_source ε ht hN, pmPowerDampedAbelError, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro n _
  rw [Complex.real_smul]
  push_cast
  ring

theorem pmDyadicChebyshevSource_eq_sum {t : ℝ} (ht : t ∈ Ioc (0 : ℝ) 1)
    {N : ℕ} (hN : ⌊1 / t⌋₊ ≤ N) :
    pmDyadicChebyshevSource t =
      ∑ n ∈ Finset.Icc 1 N, (pmLogDampingGap n : ℂ) *
        (rawMobiusFermiApprox n t - dyadicHaar t) := by
  have hsum : Tendsto (fun ε : ℝ =>
      ∑ n ∈ Finset.Icc 1 N, ((pmPowerDampingGap ε n / ε : ℝ) : ℂ) *
        (rawMobiusFermiApprox n t - dyadicHaar t)) (𝓝[>] 0)
      (𝓝 (∑ n ∈ Finset.Icc 1 N, (pmLogDampingGap n : ℂ) *
        (rawMobiusFermiApprox n t - dyadicHaar t))) := by
    apply tendsto_finsetSum
    intro n hn
    exact (tendsto_pmPowerDampingGap_div (Finset.mem_Icc.mp hn).1).ofReal.mul_const _
  have hlim := hsum.congr' (Eventually.of_forall fun ε =>
    (pmPowerDampedDifferenceQuotient_eq_sum ε ht hN).symm)
  exact tendsto_nhds_unique (tendsto_pmPowerDampedDifferenceQuotient ht) hlim

def pmDampingDerivativeErrorPrefix (ε : ℝ) (N : ℕ) (t : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 N, ((pmPowerDampingGap ε n / ε - pmLogDampingGap n : ℝ) : ℂ) *
    (rawMobiusFermiApprox n t - dyadicHaar t)

theorem memLp_pmDampingDerivativeErrorPrefix (ε : ℝ) (N : ℕ) :
    MemLp (pmDampingDerivativeErrorPrefix ε N) 1 (volume.restrict (Ioc (0 : ℝ) 1)) := by
  apply memLp_finsetSum (Finset.Icc 1 N)
  intro n _
  exact ((memLp_pmRawFermiError n).mono_exponent (by norm_num : (1 : ENNReal) ≤ 2)).const_mul _

theorem pmDampingDerivativeErrorPrefix_eq_source (ε : ℝ) {t : ℝ}
    (ht : t ∈ Ioc (0 : ℝ) 1) {N : ℕ} (hN : ⌊1 / t⌋₊ ≤ N) :
    pmDampingDerivativeErrorPrefix ε N t =
      pmPowerDampedDifferenceQuotient ε t - pmDyadicChebyshevSource t := by
  rw [pmPowerDampedDifferenceQuotient_eq_sum ε ht hN, pmDyadicChebyshevSource_eq_sum ht hN,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n _
  push_cast
  ring

theorem pmDampingDerivativeErrorPrefix_norm_le {ε : ℝ} (hε : 0 < ε) (N : ℕ) :
    eLpNorm (pmDampingDerivativeErrorPrefix ε N) 1 (volume.restrict (Ioc (0 : ℝ) 1)) ≤
      ENNReal.ofReal (∑' n : ℕ, pmDampingDerivativeMajorant ε n) := by
  let F : ℕ → ℝ → ℂ := fun n =>
    ((pmPowerDampingGap ε n / ε - pmLogDampingGap n : ℝ) : ℂ) •
      (fun t => rawMobiusFermiApprox n t - dyadicHaar t)
  have hF (n : ℕ) : MemLp (F n) 1 (volume.restrict (Ioc (0 : ℝ) 1)) :=
    ((memLp_pmRawFermiError n).mono_exponent (by norm_num : (1 : ENNReal) ≤ 2)).const_smul _
  have heq : pmDampingDerivativeErrorPrefix ε N = ∑ n ∈ Finset.Icc 1 N, F n := by
    ext t
    simp [pmDampingDerivativeErrorPrefix, F]
  rw [← ofReal_lpNorm (memLp_pmDampingDerivativeErrorPrefix ε N)]
  apply ENNReal.ofReal_le_ofReal
  rw [heq]
  calc
    _ ≤ ∑ n ∈ Finset.Icc 1 N, lpNorm (F n) 1 (volume.restrict (Ioc (0 : ℝ) 1)) :=
      lpNorm_sum_le (fun n _ => hF n) le_rfl
    _ = ∑ n ∈ Finset.Icc 1 N, pmDampingDerivativeMajorant ε n := by
      apply Finset.sum_congr rfl
      intro n hn
      dsimp only [F]
      rw [lpNorm_const_smul]
      simp only [coe_nnnorm, Complex.norm_real, Real.norm_eq_abs]
      rw [← pmRawFermiL1Error_eq_lpNorm, pmDampingDerivativeMajorant,
        if_pos (Finset.mem_Icc.mp hn).1]
    _ ≤ _ := (summable_pmDampingDerivativeMajorant hε).sum_le_tsum _
      (fun n _ => pmDampingDerivativeMajorant_nonneg ε n)

theorem pmPowerDampedDifferenceQuotient_error_norm_le {ε : ℝ} (hε : 0 < ε) :
    eLpNorm (fun t => pmPowerDampedDifferenceQuotient ε t - pmDyadicChebyshevSource t) 1
      (volume.restrict (Ioc (0 : ℝ) 1)) ≤
        ENNReal.ofReal (∑' n : ℕ, pmDampingDerivativeMajorant ε n) := by
  apply Lp.eLpNorm_le_of_ae_tendsto (u := (atTop : Filter ℕ))
    (Eventually.of_forall fun N => pmDampingDerivativeErrorPrefix_norm_le hε N)
    (fun N => (memLp_pmDampingDerivativeErrorPrefix ε N).aestronglyMeasurable)
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop ⌊1 / t⌋₊] with N hN
  exact (pmDampingDerivativeErrorPrefix_eq_source ε ht hN).symm

/-- The canonical positive-damping difference quotients converge in L¹ to the actual Chebyshev source. -/
theorem tendsto_pmPowerDampedDifferenceQuotient_L1 :
    Tendsto (fun ε : ℝ => eLpNorm
      (fun t => pmPowerDampedDifferenceQuotient ε t - pmDyadicChebyshevSource t) 1
      (volume.restrict (Ioc (0 : ℝ) 1))) (𝓝[>] 0) (𝓝 0) := by
  have hmajor := ENNReal.tendsto_ofReal tendsto_pmDampingDerivativeMajorant_tsum
  rw [ENNReal.ofReal_zero] at hmajor
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hmajor
    (Eventually.of_forall fun _ => bot_le)
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact pmPowerDampedDifferenceQuotient_error_norm_le hε

theorem pmPowerDampedDifferenceQuotient_integral {ε : ℝ} (hε : 0 < ε) :
    (∫ t in Ioc (0 : ℝ) 1, pmPowerDampedDifferenceQuotient ε t) =
      (∫ t in Ioi (0 : ℝ), pmPowerDampedFermiSource ε t) / (ε : ℂ) := by
  have hA := (integrable_pmPowerDampedFermiSource hε).mono_measure
    (Measure.restrict_mono (show Ioc (0 : ℝ) 1 ⊆ Ioi 0 from fun _ ht => ht.1) le_rfl)
  have hH := memLp_pm_dyadicHaar.integrable (by norm_num : (1 : ENNReal) ≤ 2)
  unfold pmPowerDampedDifferenceQuotient
  rw [integral_smul, integral_sub hA hH, pm_integral_dyadicHaar, sub_zero,
    pmPowerDampedFermiSource_integral_carrier hε, pmPowerDampedFermiSource_integral hε,
    Complex.real_smul, Complex.ofReal_inv]
  ring

/-- The signed integral of the actual dyadic Chebyshev derivative is exactly log 2. -/
theorem pmDyadicChebyshevSource_integral :
    (∫ t in Ioc (0 : ℝ) 1, pmDyadicChebyshevSource t) = (Real.log 2 : ℂ) := by
  have hFi : ∀ᶠ ε in 𝓝[>] (0 : ℝ), Integrable (pmPowerDampedDifferenceQuotient ε)
      (volume.restrict (Ioc (0 : ℝ) 1)) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    apply memLp_one_iff_integrable.mp
    exact ⟨(measurable_pmPowerDampedDifferenceQuotient ε).aestronglyMeasurable,
      (pmPowerDampedDifferenceQuotient_norm_le hε).trans_lt ENNReal.ofReal_lt_top⟩
  have hL1 := tendsto_integral_of_L1' pmDyadicChebyshevSource
    measurable_pmDyadicChebyshevSource.aestronglyMeasurable hFi
    (show Tendsto (fun ε : ℝ => eLpNorm
      (pmPowerDampedDifferenceQuotient ε - pmDyadicChebyshevSource) 1
      (volume.restrict (Ioc (0 : ℝ) 1))) (𝓝[>] 0) (𝓝 0) from
        tendsto_pmPowerDampedDifferenceQuotient_L1)
  have hmean := tendsto_pmPowerDampedFermiSource_mean_div_parameter.congr'
    (show ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      (∫ t in Ioi (0 : ℝ), pmPowerDampedFermiSource ε t) / (ε : ℂ) =
        ∫ t in Ioc (0 : ℝ) 1, pmPowerDampedDifferenceQuotient ε t from ?_)
  · exact tendsto_nhds_unique hL1 hmean
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    exact (pmPowerDampedDifferenceQuotient_integral hε).symm

end RHTower
