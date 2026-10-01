import GaloisForLFunctions.RHTower.PMPowerDampedMobiusMean
import GaloisForLFunctions.HTGeometry.WeightedHolder

/-!
# Linear L¹ convergence of the power-damped Möbius source

Raw prefix errors occupy a shrinking interval. Their canonical L² logarithmic
savings give a summable reciprocal L¹ error budget. Finite Abel sums and Fatou
then bound the literal source's L¹ Haar error by that budget times the damping.
This result supplies no small-positive canonical L² admission.
-/

open MeasureTheory Set Filter Topology Complex
noncomputable section
namespace RHTower

def pmRawFermiL1Error (N : ℕ) : ℝ :=
  ∫ t in Ioc (0 : ℝ) 1, ‖rawMobiusFermiApprox N t - dyadicHaar t‖

theorem pmRawFermiL1Error_nonneg (N : ℕ) : 0 ≤ pmRawFermiL1Error N :=
  integral_nonneg (fun _ => norm_nonneg _)

theorem memLp_pmRawFermiError (N : ℕ) :
    MemLp (fun t => rawMobiusFermiApprox N t - dyadicHaar t) 2
      (volume.restrict (Ioc (0 : ℝ) 1)) := by
  exact ((memLp_rawMobiusFermiApprox N).mono_measure
    (Measure.restrict_mono (fun _ ht => ht.1) le_rfl)).sub memLp_pm_dyadicHaar

theorem pmRawFermiL1Error_le_shrinking_norm (N : ℕ) :
    pmRawFermiL1Error N ≤
      lpNorm (rawMobiusFermiApprox N) 2 (volume.restrict (Ioi 0)) /
        Real.sqrt ((N : ℝ) + 1) + 1 / ((N : ℝ) + 1) := by
  let r : ℝ := 1 / ((N : ℝ) + 1)
  have hr : 0 < r := by dsimp [r]; positivity
  have hr1 : r ≤ 1 := by
    dsimp [r]
    apply (div_le_iff₀ (by positivity)).2
    simp
  have hsub : Ioc (0 : ℝ) r ⊆ Ioc 0 1 := fun _ ht => ⟨ht.1, ht.2.trans hr1⟩
  have hpos : Ioc (0 : ℝ) r ⊆ Ioi 0 := fun _ ht => ht.1
  have hraw := (memLp_rawMobiusFermiApprox N).mono_measure (Measure.restrict_mono hpos le_rfl)
  have hint := hraw.integrable (by norm_num : (1 : ENNReal) ≤ 2)
  have hsq := hraw.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  have heq : pmRawFermiL1Error N =
      ∫ t in Ioc (0 : ℝ) r, ‖rawMobiusFermiApprox N t - dyadicHaar t‖ := by
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioc hsub
    intro t ht
    have hrt : r < t := by
      have h := ht.2
      simp only [mem_Ioc, not_and] at h
      exact lt_of_not_ge (h ht.1.1)
    rw [rawMobiusFermiApprox_eq_dyadicHaar N hrt ht.1.2, sub_self, norm_zero]
  have hC := GaloisForLFunctions.HTGeometry.integral_mul_le_sqrt_mul_sqrt_measure
    hraw.aestronglyMeasurable (aestronglyMeasurable_const (b := (1 : ℂ))) hsq
    (show Integrable (fun _ : ℝ => ‖(1 : ℂ)‖ ^ 2)
      (volume.restrict (Ioc (0 : ℝ) r)) from integrable_const _)
  have hvol : (volume.restrict (Ioc (0 : ℝ) r)).real univ = r := by
    simp [measureReal_def, hr.le]
  simp only [norm_one, mul_one, one_pow, integral_const, smul_eq_mul] at hC
  rw [hvol] at hC
  have hE := setIntegral_mono_set
    ((memLp_rawMobiusFermiApprox N).integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0))
    (Eventually.of_forall fun t => sq_nonneg ‖rawMobiusFermiApprox N t‖)
    (Eventually.of_forall fun t (ht : t ∈ Ioc (0 : ℝ) r) => hpos ht)
  have hRoot : Real.sqrt (∫ t in Ioc (0 : ℝ) r, ‖rawMobiusFermiApprox N t‖ ^ 2) ≤
      lpNorm (rawMobiusFermiApprox N) 2 (volume.restrict (Ioi 0)) := by
    rw [← pm_rawMobiusFermiApprox_lpNorm_sq N] at hE
    exact (Real.sqrt_le_sqrt hE).trans_eq (Real.sqrt_sq lpNorm_nonneg)
  calc
    _ = ∫ t in Ioc (0 : ℝ) r, ‖rawMobiusFermiApprox N t - dyadicHaar t‖ := heq
    _ ≤ ∫ t in Ioc (0 : ℝ) r, ‖rawMobiusFermiApprox N t‖ + 1 := by
      apply integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _)
        (hint.norm.add (integrable_const 1))
      exact Eventually.of_forall (fun t => by
        change ‖rawMobiusFermiApprox N t - dyadicHaar t‖ ≤ ‖rawMobiusFermiApprox N t‖ + 1
        simpa only [norm_dyadicHaar] using
          (norm_sub_le (rawMobiusFermiApprox N t) (dyadicHaar t)))
    _ = (∫ t in Ioc (0 : ℝ) r, ‖rawMobiusFermiApprox N t‖) + r := by
      rw [integral_add hint.norm (integrable_const 1), integral_const, hvol]
      simp
    _ ≤ Real.sqrt (∫ t in Ioc (0 : ℝ) r, ‖rawMobiusFermiApprox N t‖ ^ 2) *
        Real.sqrt r + r := by linarith [hC]
    _ ≤ lpNorm (rawMobiusFermiApprox N) 2 (volume.restrict (Ioi 0)) *
        Real.sqrt r + r := by gcongr
    _ = _ := by
      dsimp [r]
      rw [Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 1), Real.sqrt_one]
      ring

theorem pmRawFermiL1Error_le_normalized_norm {N : ℕ} (hN : 1 ≤ N) :
    pmRawFermiL1Error N ≤
      lpNorm (rawMobiusFermiApprox N) 2 (volume.restrict (Ioi 0)) /
        Real.sqrt (N : ℝ) + 1 / (N : ℝ) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  apply (pmRawFermiL1Error_le_shrinking_norm N).trans
  gcongr <;> first | exact lpNorm_nonneg | positivity | linarith

theorem summable_pmRawFermiL1Error_div :
    Summable (fun n : ℕ => pmRawFermiL1Error n / (n : ℝ)) := by
  obtain ⟨C, hC, hb⟩ := pm_rawMobiusFermiApprox_normalized_norm_log_bound
  have hs : Summable (fun n : ℕ =>
      C * (1 / ((n : ℝ) * Real.log (n : ℝ) ^ 2)) + 1 / (n : ℝ) ^ 2) :=
    (pm_summable_reciprocal_log_sq.mul_left C).add
      (Real.summable_one_div_nat_pow.mpr (by omega : 1 < 2))
  apply hs.of_norm_bounded_eventually_nat
  filter_upwards [hb, eventually_ge_atTop 1] with n hn hn1
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (pmRawFermiL1Error_nonneg n) hn0.le)]
  calc
    _ ≤ (lpNorm (rawMobiusFermiApprox n) 2 (volume.restrict (Ioi 0)) /
        Real.sqrt (n : ℝ) + 1 / (n : ℝ)) / (n : ℝ) :=
      div_le_div_of_nonneg_right (pmRawFermiL1Error_le_normalized_norm hn1) hn0.le
    _ ≤ (C / Real.log (n : ℝ) ^ 2 + 1 / (n : ℝ)) / (n : ℝ) := by gcongr
    _ = _ := by ring

theorem pmRawFermiL1Error_eq_lpNorm (N : ℕ) :
    pmRawFermiL1Error N = lpNorm (fun t => rawMobiusFermiApprox N t - dyadicHaar t) 1
      (volume.restrict (Ioc (0 : ℝ) 1)) := by
  exact (lpNorm_one_eq_integral_norm (memLp_pmRawFermiError N).aestronglyMeasurable).symm

def pmPowerDampingGap (ε : ℝ) (n : ℕ) : ℝ :=
  (n : ℝ) ^ (-ε) - ((n + 1 : ℕ) : ℝ) ^ (-ε)

theorem pmPowerDampingGap_nonneg {ε : ℝ} (hε : 0 < ε) {n : ℕ} (hn : 1 ≤ n) :
    0 ≤ pmPowerDampingGap ε n := by
  apply sub_nonneg.mpr
  apply Real.rpow_le_rpow_of_nonpos (by exact_mod_cast hn)
  · exact_mod_cast Nat.le_succ n
  · linarith

theorem pmPowerDampingGap_le {ε : ℝ} (hε : 0 < ε) {n : ℕ} (hn : 1 ≤ n) :
    pmPowerDampingGap ε n ≤ ε / (n : ℝ) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hdiff := GaloisForLFunctions.RHTower.rpow_sub_rpow_succ_le hε hn0
  have hp : (n : ℝ) ^ (-ε - 1) ≤ (n : ℝ) ^ (-1 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) (by linarith)
  calc
    _ ≤ ε * (n : ℝ) ^ (-ε - 1) := by simpa only [pmPowerDampingGap, Nat.cast_add, Nat.cast_one] using hdiff
    _ ≤ ε * (n : ℝ) ^ (-1 : ℝ) := mul_le_mul_of_nonneg_left hp hε.le
    _ = _ := by rw [Real.rpow_neg_one, div_eq_mul_inv]

theorem pmPowerDampingGap_sum (ε : ℝ) (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, pmPowerDampingGap ε n =
      1 - ((N + 1 : ℕ) : ℝ) ^ (-ε) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ N + 1), ih, pmPowerDampingGap]
    ring

def pmPowerDampedAbelError (ε : ℝ) (N : ℕ) (t : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 N, (pmPowerDampingGap ε n : ℂ) *
    (rawMobiusFermiApprox n t - dyadicHaar t)

theorem pmPowerDampedFermiPrefix_error_abel (ε : ℝ) (N : ℕ) (t : ℝ) :
    pmPowerDampedFermiPrefix ε (N + 1) t - dyadicHaar t =
      ((((N + 1 : ℕ) : ℝ) ^ (-ε) : ℝ) : ℂ) *
        (rawMobiusFermiApprox (N + 1) t - dyadicHaar t) +
          pmPowerDampedAbelError ε N t := by
  rw [pmPowerDampedFermiPrefix_abel, pmPowerDampedAbelError]
  simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
  have hsum : (∑ n ∈ Finset.Icc 1 N, (pmPowerDampingGap ε n : ℂ)) =
      1 - ((((N + 1 : ℕ) : ℝ) ^ (-ε) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_sum, pmPowerDampingGap_sum, Complex.ofReal_sub, Complex.ofReal_one]
  rw [hsum]
  change _ = _
  dsimp only [pmPowerDampingGap]
  ring

theorem memLp_pmPowerDampedAbelError (ε : ℝ) (N : ℕ) :
    MemLp (pmPowerDampedAbelError ε N) 1 (volume.restrict (Ioc (0 : ℝ) 1)) := by
  apply memLp_finsetSum (Finset.Icc 1 N)
  intro n _
  exact ((memLp_pmRawFermiError n).mono_exponent (by norm_num : (1 : ENNReal) ≤ 2)).const_mul _

theorem pmPowerDampedAbelError_norm_le {ε : ℝ} (hε : 0 < ε) (N : ℕ) :
    eLpNorm (pmPowerDampedAbelError ε N) 1 (volume.restrict (Ioc (0 : ℝ) 1)) ≤
      ENNReal.ofReal (ε * ∑' n : ℕ, pmRawFermiL1Error n / (n : ℝ)) := by
  let F : ℕ → ℝ → ℂ := fun n => (pmPowerDampingGap ε n : ℂ) •
    (fun t => rawMobiusFermiApprox n t - dyadicHaar t)
  have hF (n : ℕ) : MemLp (F n) 1 (volume.restrict (Ioc (0 : ℝ) 1)) :=
    ((memLp_pmRawFermiError n).mono_exponent (by norm_num : (1 : ENNReal) ≤ 2)).const_smul _
  have heq : pmPowerDampedAbelError ε N = ∑ n ∈ Finset.Icc 1 N, F n := by
    ext t
    simp [pmPowerDampedAbelError, F]
  rw [← ofReal_lpNorm (memLp_pmPowerDampedAbelError ε N)]
  apply ENNReal.ofReal_le_ofReal
  rw [heq]
  calc
    _ ≤ ∑ n ∈ Finset.Icc 1 N, lpNorm (F n) 1 (volume.restrict (Ioc (0 : ℝ) 1)) :=
      lpNorm_sum_le (fun n _ => hF n) le_rfl
    _ ≤ ∑ n ∈ Finset.Icc 1 N, ε * (pmRawFermiL1Error n / (n : ℝ)) := by
      apply Finset.sum_le_sum
      intro n hn
      have hn1 := (Finset.mem_Icc.mp hn).1
      dsimp only [F]
      rw [lpNorm_const_smul]
      simp only [coe_nnnorm, Complex.norm_real, Real.norm_eq_abs]
      rw [abs_of_nonneg (pmPowerDampingGap_nonneg hε hn1), ← pmRawFermiL1Error_eq_lpNorm]
      calc
        _ ≤ (ε / (n : ℝ)) * pmRawFermiL1Error n :=
          mul_le_mul_of_nonneg_right (pmPowerDampingGap_le hε hn1) (pmRawFermiL1Error_nonneg n)
        _ = _ := by ring
    _ = ε * ∑ n ∈ Finset.Icc 1 N, pmRawFermiL1Error n / (n : ℝ) := by rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (summable_pmRawFermiL1Error_div.sum_le_tsum _ (fun n _ =>
        div_nonneg (pmRawFermiL1Error_nonneg n) (Nat.cast_nonneg n))) hε.le

theorem pmPowerDampedAbelError_eq_source (ε : ℝ) {t : ℝ} (ht : t ∈ Ioc (0 : ℝ) 1)
    {N : ℕ} (hN : ⌊1 / t⌋₊ ≤ N) :
    pmPowerDampedAbelError ε N t = pmPowerDampedFermiSource ε t - dyadicHaar t := by
  have hprefix : pmPowerDampedFermiPrefix ε (N + 1) t = pmPowerDampedFermiSource ε t := by
    rw [pmPowerDampedFermiSource_eq_sum ε ht.1 (hN.trans (Nat.le_succ N))]
    simp only [pmPowerDampedFermiPrefix, Complex.ofReal_mul, Complex.ofReal_intCast]
  have hrt : 1 / (((N + 1 : ℕ) : ℝ) + 1) < t := by
    apply (div_lt_iff₀ (by positivity)).2
    have hfloor := (div_lt_iff₀ ht.1).mp (Nat.lt_floor_add_one (1 / t))
    have hcast : (⌊1 / t⌋₊ : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    push_cast
    nlinarith [mul_nonneg ht.1.le (sub_nonneg.mpr hcast)]
  have h := pmPowerDampedFermiPrefix_error_abel ε N t
  rw [hprefix, rawMobiusFermiApprox_eq_dyadicHaar (N + 1) hrt ht.2,
    sub_self, mul_zero, zero_add] at h
  exact h.symm

theorem tendsto_pmPowerDampedAbelError (ε : ℝ) {t : ℝ} (ht : t ∈ Ioc (0 : ℝ) 1) :
    Tendsto (fun N : ℕ => pmPowerDampedAbelError ε N t) atTop
      (𝓝 (pmPowerDampedFermiSource ε t - dyadicHaar t)) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop ⌊1 / t⌋₊] with N hN
  exact (pmPowerDampedAbelError_eq_source ε ht hN).symm

/-- A finite canonical reciprocal error budget gives a linear L¹ approximation rate. -/
theorem pmPowerDampedFermiSource_haar_L1_error_le {ε : ℝ} (hε : 0 < ε) :
    eLpNorm (fun t => pmPowerDampedFermiSource ε t - dyadicHaar t) 1
      (volume.restrict (Ioc (0 : ℝ) 1)) ≤
        ENNReal.ofReal (ε * ∑' n : ℕ, pmRawFermiL1Error n / (n : ℝ)) := by
  apply Lp.eLpNorm_le_of_ae_tendsto (u := (atTop : Filter ℕ))
    (Eventually.of_forall fun N => pmPowerDampedAbelError_norm_le hε N)
    (fun N => (memLp_pmPowerDampedAbelError ε N).aestronglyMeasurable)
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  exact tendsto_pmPowerDampedAbelError ε ht

/-- The literal positive-damping source converges to Haar in canonical L¹. -/
theorem tendsto_pmPowerDampedFermiSource_haar_L1 :
    Tendsto (fun ε : ℝ => eLpNorm (fun t => pmPowerDampedFermiSource ε t - dyadicHaar t) 1
      (volume.restrict (Ioc (0 : ℝ) 1))) (𝓝[>] 0) (𝓝 0) := by
  have hmajor : Tendsto (fun ε : ℝ => ENNReal.ofReal
      (ε * ∑' n : ℕ, pmRawFermiL1Error n / (n : ℝ))) (𝓝[>] 0) (𝓝 0) := by
    have hc : Continuous (fun ε : ℝ => ε * ∑' n : ℕ, pmRawFermiL1Error n / (n : ℝ)) := by
      fun_prop
    have hr := (hc.tendsto 0).mono_left
      (nhdsWithin_le_nhds : (𝓝[>] (0 : ℝ)) ≤ 𝓝 0)
    simpa using ENNReal.tendsto_ofReal hr
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hmajor
    (Eventually.of_forall fun _ => bot_le)
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact pmPowerDampedFermiSource_haar_L1_error_le hε

end RHTower
