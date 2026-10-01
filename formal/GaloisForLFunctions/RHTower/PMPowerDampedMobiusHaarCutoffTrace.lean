import GaloisForLFunctions.RHTower.PMPowerDampedMobiusClippedHaarSource

open MeasureTheory Set Filter Topology Complex
noncomputable section
namespace RHTower

theorem pm_norm_sub_sq_le (z w : ℂ) : ‖z - w‖ ^ 2 ≤ 2 * ‖z‖ ^ 2 + 2 * ‖w‖ ^ 2 := by
  have h := pow_le_pow_left₀ (norm_nonneg (z - w)) (norm_sub_le z w) 2
  nlinarith [sq_nonneg (‖z‖ - ‖w‖)]

theorem pm_norm_sq_le_sub_sq (z w : ℂ) : ‖z‖ ^ 2 ≤ 2 * ‖z - w‖ ^ 2 + 2 * ‖w‖ ^ 2 := by
  have h := pm_norm_sub_sq_le (z - w) (-w)
  simpa only [sub_neg_eq_add, sub_add_cancel, norm_neg] using h

theorem pmPowerDampedClippedCenteredSource_error_energy (ε : ℝ) {a : ℝ} (ha : 0 < a) :
    (∫ t in Ioi (0 : ℝ),
      ‖pmPowerDampedClippedCenteredSource ε a t - pmPowerDampedCenteredSource ε t‖ ^ 2) =
      ∫ t in Ioc (0 : ℝ) (1 / a),
        ‖pmPowerDampedClippedCenteredSource ε a t - pmPowerDampedCenteredSource ε t‖ ^ 2 := by
  rw [← Ioc_union_Ioi_eq_Ioi (show (0 : ℝ) ≤ 1 / a by positivity)]
  apply integral_union_eq_left_of_forall measurableSet_Ioi
  intro t ht
  simp only [pmPowerDampedClippedCenteredSource_tail ε ha (le_of_lt ht), sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0)]

theorem pmPowerDampedClippedCenteredSource_error_bounds {ε a : ℝ}
    (hε : 0 ≤ ε) (ha : 0 < a)
    (hf : MemLp (pmPowerDampedCenteredSource ε) 2 (volume.restrict (Ioi (0 : ℝ)))) :
    (∫ t in Ioi (0 : ℝ),
      ‖pmPowerDampedClippedCenteredSource ε a t - pmPowerDampedCenteredSource ε t‖ ^ 2) ≤
        2 * (‖pmPowerDampedDivisorRemainder ε a‖ ^ 2 / a) +
          2 * (∫ t in Ioc (0 : ℝ) (1 / a), ‖pmPowerDampedCenteredSource ε t‖ ^ 2) ∧
      ‖pmPowerDampedDivisorRemainder ε a‖ ^ 2 / a ≤
        2 * (∫ t in Ioi (0 : ℝ),
          ‖pmPowerDampedClippedCenteredSource ε a t - pmPowerDampedCenteredSource ε t‖ ^ 2) +
          2 * (∫ t in Ioc (0 : ℝ) (1 / a), ‖pmPowerDampedCenteredSource ε t‖ ^ 2) := by
  have hsub : Ioc (0 : ℝ) (1 / a) ⊆ Ioi 0 := fun _ hx => hx.1
  have hei₀ : IntegrableOn (fun t =>
      ‖pmPowerDampedClippedCenteredSource ε a t - pmPowerDampedCenteredSource ε t‖ ^ 2)
      (Ioi (0 : ℝ)) := ((memLp_pmPowerDampedClippedCenteredSource hε ha).sub hf).norm.integrable_sq
  have hfi₀ : IntegrableOn (fun t => ‖pmPowerDampedCenteredSource ε t‖ ^ 2)
      (Ioi (0 : ℝ)) := hf.norm.integrable_sq
  have hei : IntegrableOn (fun t =>
      ‖pmPowerDampedClippedCenteredSource ε a t - pmPowerDampedCenteredSource ε t‖ ^ 2)
      (Ioc (0 : ℝ) (1 / a)) :=
    hei₀.mono_set hsub
  have hfi : IntegrableOn (fun t => ‖pmPowerDampedCenteredSource ε t‖ ^ 2)
      (Ioc (0 : ℝ) (1 / a)) := hfi₀.mono_set hsub
  have hci : IntegrableOn (fun _ : ℝ => ‖pmPowerDampedDivisorRemainder ε a‖ ^ 2)
      (Ioc (0 : ℝ) (1 / a)) := integrable_const _
  have hcint : (∫ _t in Ioc (0 : ℝ) (1 / a), ‖pmPowerDampedDivisorRemainder ε a‖ ^ 2) =
      ‖pmPowerDampedDivisorRemainder ε a‖ ^ 2 / a := by
    rw [← intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 / a by positivity),
      intervalIntegral.integral_const]
    simp only [sub_zero, smul_eq_mul]
    ring
  have hu := setIntegral_mono_on hei ((hci.const_mul 2).add (hfi.const_mul 2))
    measurableSet_Ioc (fun t ht => by
      rw [pmPowerDampedClippedCenteredSource_initial ε ha ht]
      exact pm_norm_sub_sq_le _ _)
  have hl := setIntegral_mono_on hci ((hei.const_mul 2).add (hfi.const_mul 2))
    measurableSet_Ioc (fun t ht => by
      simp only [Pi.add_apply]
      rw [pmPowerDampedClippedCenteredSource_initial ε ha ht]
      exact pm_norm_sq_le_sub_sq _ _)
  simp only [Pi.add_apply] at hu hl
  rw [integral_add (hci.const_mul 2) (hfi.const_mul 2), integral_const_mul,
    integral_const_mul, hcint, ← pmPowerDampedClippedCenteredSource_error_energy ε ha] at hu
  rw [integral_add (hei.const_mul 2) (hfi.const_mul 2), integral_const_mul,
    integral_const_mul, hcint, ← pmPowerDampedClippedCenteredSource_error_energy ε ha] at hl
  exact ⟨hu, hl⟩

theorem tendsto_pm_initial_energy {f : ℝ → ℂ} (hm : Measurable f)
    (hf : MemLp f 2 (volume.restrict (Ioi (0 : ℝ))))
    {a : ℕ → ℝ} (ha : ∀ n, 0 < a n) (hat : Tendsto a atTop atTop) :
    Tendsto (fun n => ∫ t in Ioc (0 : ℝ) (1 / a n), ‖f t‖ ^ 2) atTop (𝓝 0) := by
  let F := fun n : ℕ => (Ioc (0 : ℝ) (1 / a n)).indicator (fun t => ‖f t‖ ^ 2)
  have h := tendsto_integral_of_dominated_convergence
    (μ := volume.restrict (Ioi (0 : ℝ))) (F := F) (f := fun _ => (0 : ℝ))
    (fun t => ‖f t‖ ^ 2)
    (fun n => ((hm.norm.pow_const 2).indicator measurableSet_Ioc).aestronglyMeasurable)
    hf.norm.integrable_sq ?_ ?_
  · have he (n : ℕ) : (∫ t in Ioi (0 : ℝ), F n t) =
        ∫ t in Ioc (0 : ℝ) (1 / a n), ‖f t‖ ^ 2 := by
      dsimp only [F]
      rw [setIntegral_indicator measurableSet_Ioc,
        inter_eq_right.mpr (show Ioc (0 : ℝ) (1 / a n) ⊆ Ioi 0 from fun _ ht => ht.1)]
    simpa only [he, integral_zero] using h
  · intro n
    exact Eventually.of_forall fun t => by
      by_cases ht : t ∈ Ioc (0 : ℝ) (1 / a n)
      · simp only [F, indicator_of_mem ht, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖f t‖), le_refl]
      · simp only [F, indicator_of_notMem ht, norm_zero]
        exact sq_nonneg _
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 < t := ht
    apply tendsto_const_nhds.congr'
    filter_upwards [hat.eventually (eventually_gt_atTop (1 / t))] with n hn
    have hlt : 1 / a n < t := (div_lt_iff₀ (ha n)).mpr
      (by simpa only [mul_comm] using (div_lt_iff₀ ht0).mp hn)
    exact (indicator_of_notMem (show t ∉ Ioc (0 : ℝ) (1 / a n) from
      fun hx => (not_le_of_gt hlt) hx.2) _).symm

theorem pmPowerDampedClippedCenteredSource_L2_iff_trace {ε : ℝ} (hε : 0 ≤ ε)
    (hf : MemLp (pmPowerDampedCenteredSource ε) 2 (volume.restrict (Ioi (0 : ℝ))))
    {a : ℕ → ℝ} (ha : ∀ n, 0 < a n) (hat : Tendsto a atTop atTop) :
    Tendsto (fun n => ∫ t in Ioi (0 : ℝ),
      ‖pmPowerDampedClippedCenteredSource ε (a n) t - pmPowerDampedCenteredSource ε t‖ ^ 2)
        atTop (𝓝 0) ↔
      Tendsto (fun n => ‖pmPowerDampedDivisorRemainder ε (a n)‖ ^ 2 / a n) atTop (𝓝 0) := by
  have htail := tendsto_pm_initial_energy (measurable_pmPowerDampedCenteredSource ε) hf ha hat
  constructor
  · intro he
    apply squeeze_zero (fun n => div_nonneg (sq_nonneg _) (ha n).le)
      (fun n => (pmPowerDampedClippedCenteredSource_error_bounds hε (ha n) hf).2)
    simpa using (he.const_mul 2).add (htail.const_mul 2)
  · intro ht
    apply squeeze_zero (fun n => integral_nonneg (fun _ => sq_nonneg _))
      (fun n => (pmPowerDampedClippedCenteredSource_error_bounds hε (ha n) hf).1)
    simpa using (ht.const_mul 2).add (htail.const_mul 2)

theorem pmForwardDyadicDifference_energy_bounds {f : ℝ → ℂ} (hm : Measurable f)
    (hf : MemLp f 2 (volume.restrict (Ioi (0 : ℝ)))) :
    (∫ t in Ioi (0 : ℝ), ‖pmForwardDyadicDifference f t‖ ^ 2) ≤
        (Real.sqrt 2 + 1) ^ 2 * (∫ t in Ioi (0 : ℝ), ‖f t‖ ^ 2) ∧
      (∫ t in Ioi (0 : ℝ), ‖f t‖ ^ 2) ≤
        (Real.sqrt 2 + 1) ^ 2 * (∫ t in Ioi (0 : ℝ), ‖pmForwardDyadicDifference f t‖ ^ 2) := by
  have hb := pmForwardDyadicDifference_lpNorm_bounds hm hf
  have hc : (Real.sqrt 2 + 1) * (Real.sqrt 2 - 1) = 1 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have hi := mul_le_mul_of_nonneg_left hb.1 (show 0 ≤ Real.sqrt 2 + 1 by positivity)
  rw [← mul_assoc, hc, one_mul] at hi
  have hu2 := pow_le_pow_left₀
    (lpNorm_nonneg (f := pmForwardDyadicDifference f) (p := 2)
      (μ := volume.restrict (Ioi (0 : ℝ)))) hb.2 2
  have hl2 := pow_le_pow_left₀
    (lpNorm_nonneg (f := f) (p := 2) (μ := volume.restrict (Ioi (0 : ℝ)))) hi 2
  have hs := memLp_pmForwardDyadicDifference hm hf
  rw [pm_integral_norm_sq_toLp hs, pm_integral_norm_sq_toLp hf,
    Lp.norm_toLp, Lp.norm_toLp, toReal_eLpNorm hs.aestronglyMeasurable,
    toReal_eLpNorm hf.aestronglyMeasurable]
  simpa only [mul_pow] using And.intro hu2 hl2

theorem pmPowerDampedRepairedHaarPrefix_error_energy (ε : ℝ) {N : ℕ} (hN : 1 ≤ N) :
    (∫ t in Ioi (0 : ℝ),
      ‖pmPowerDampedRepairedHaarPrefix ε N t - pmPowerDampedFermiSource ε t‖ ^ 2) =
      ∫ t in Ioi (0 : ℝ),
        ‖pmForwardDyadicDifference
          (pmPowerDampedClippedCenteredSource ε N - pmPowerDampedCenteredSource ε) t‖ ^ 2 := by
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [pmPowerDampedRepairedHaarPrefix_eq_clipped ε hN ht,
    pmPowerDampedFermiSource_eq_centered_difference ε ht]
  congr 2
  simp only [pmForwardDyadicDifference, Pi.sub_apply]
  ring

theorem pmPowerDampedRepairedHaarPrefix_L2_iff_trace {ε : ℝ} (hε : 0 < ε)
    (hf : MemLp (pmPowerDampedFermiSource ε) 2 (volume.restrict (Ioi (0 : ℝ))))
    {N : ℕ → ℕ} (hN : ∀ n, 1 ≤ N n) (hNt : Tendsto N atTop atTop) :
    Tendsto (fun n => ∫ t in Ioi (0 : ℝ),
      ‖pmPowerDampedRepairedHaarPrefix ε (N n) t - pmPowerDampedFermiSource ε t‖ ^ 2)
        atTop (𝓝 0) ↔
      Tendsto (fun n => ‖pmPowerDampedDivisorRemainder ε (N n)‖ ^ 2 / (N n : ℝ)) atTop (𝓝 0) := by
  have hfc := (pmPowerDampedFermiSource_memLp_iff_centered hε).mp hf
  have hNp (n : ℕ) : (0 : ℝ) < N n := by exact_mod_cast (by have := hN n; omega : 0 < N n)
  have hclip := pmPowerDampedClippedCenteredSource_L2_iff_trace hε.le hfc hNp
    (tendsto_natCast_atTop_atTop.comp hNt)
  have he (n : ℕ) := pmForwardDyadicDifference_energy_bounds
    ((measurable_pmPowerDampedClippedCenteredSource ε (N n)).sub
      (measurable_pmPowerDampedCenteredSource ε))
    ((memLp_pmPowerDampedClippedCenteredSource hε.le (hNp n)).sub hfc)
  simp only [← pmPowerDampedRepairedHaarPrefix_error_energy ε (hN _), Pi.sub_apply] at he
  rw [← hclip]
  constructor
  · intro h
    apply squeeze_zero (fun n => integral_nonneg (fun _ => sq_nonneg _)) (fun n => (he n).2)
    simpa only [mul_zero] using h.const_mul ((Real.sqrt 2 + 1) ^ 2)
  · intro h
    apply squeeze_zero (fun n => integral_nonneg (fun _ => sq_nonneg _)) (fun n => (he n).1)
    simpa only [mul_zero] using h.const_mul ((Real.sqrt 2 + 1) ^ 2)

theorem pm_exists_dyadic_small_weight {w : ℕ → ℝ} (hw : ∀ n, 0 ≤ w n)
    (hs : Summable w) {M : ℕ} (hM : 1 ≤ M) :
    ∃ k : ℕ, M ≤ k ∧ k < 2 * M ∧
      ((k : ℝ) + 2) * w k ≤ 3 * ∑' j : ℕ, w (j + M) := by
  have hMp : (0 : ℝ) < M := by exact_mod_cast (by omega : 0 < M)
  have hshift : Summable (fun j : ℕ => w (j + M)) := (summable_nat_add_iff M).mpr hs
  have hsum := hshift.sum_le_tsum (Finset.range M) (fun j _ => hw (j + M))
  have hne : (Finset.range M).Nonempty := ⟨0, by simp; omega⟩
  have havg : (∑ j ∈ Finset.range M, w (j + M)) ≤
      ∑ _j ∈ Finset.range M, (∑' j : ℕ, w (j + M)) / (M : ℝ) := by
    simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
      mul_div_cancel₀ _ (ne_of_gt hMp)] using hsum
  obtain ⟨j, hj, hsmall⟩ := Finset.exists_le_of_sum_le hne havg
  have hjM : j < M := Finset.mem_range.mp hj
  refine ⟨j + M, by omega, by omega, ?_⟩
  have hfactor : ((j + M : ℕ) : ℝ) + 2 ≤ 3 * (M : ℝ) := by
    have hjR : (j : ℝ) + 1 ≤ M := by exact_mod_cast hjM
    have hMR : (1 : ℝ) ≤ M := by exact_mod_cast hM
    push_cast
    linarith
  have hsmall' : (M : ℝ) * w (j + M) ≤ ∑' j : ℕ, w (j + M) := by
    simpa only [mul_comm] using (le_div_iff₀ hMp).mp hsmall
  calc
    _ ≤ (3 * (M : ℝ)) * w (j + M) := mul_le_mul_of_nonneg_right hfactor (hw _)
    _ = 3 * ((M : ℝ) * w (j + M)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hsmall' (by norm_num)

theorem pm_exists_strictMono_weighted_trace_zero {w : ℕ → ℝ}
    (hw : ∀ n, 0 ≤ w n) (hs : Summable w) :
    ∃ k : ℕ → ℕ, StrictMono k ∧
      Tendsto (fun n => ((k n : ℝ) + 2) * w (k n)) atTop (𝓝 0) := by
  have hex (n : ℕ) := pm_exists_dyadic_small_weight hw hs
    (M := 2 ^ n) (by
      have hp : 0 < (2 : ℕ) ^ n := by positivity
      omega : 1 ≤ (2 : ℕ) ^ n)
  choose k hlo hhi hbound using hex
  have hmono : StrictMono k := by
    apply strictMono_nat_of_lt_succ
    intro n
    have h1 := hhi n
    have h2 := hlo (n + 1)
    rw [pow_succ, Nat.mul_comm] at h2
    omega
  refine ⟨k, hmono, ?_⟩
  have hpmono : StrictMono (fun n : ℕ => (2 : ℕ) ^ n) := by
    apply strictMono_nat_of_lt_succ
    intro n
    have hp : 0 < (2 : ℕ) ^ n := by positivity
    rw [pow_succ]
    omega
  have ht := (tendsto_sum_nat_add w).comp hpmono.tendsto_atTop
  apply squeeze_zero (fun n => mul_nonneg (by positivity) (hw _)) hbound
  simpa only [Function.comp_def, mul_zero] using ht.const_mul 3

theorem pmPowerDampedDivisorRemainder_nat_norm_sq {ε : ℝ} (hε : 0 < ε) (n : ℕ) :
    ‖pmPowerDampedDivisorRemainder ε n‖ ^ 2 = pmPowerDampedCenteredDivisorPrefix ε n ^ 2 := by
  rw [pmPowerDampedDivisorRemainder_eq_centered_prefix hε (Nat.cast_nonneg n)]
  simp only [Nat.floor_natCast, Int.fract_natCast, Complex.ofReal_zero, mul_zero,
    sub_zero, Complex.norm_real, Real.norm_eq_abs, sq_abs]

theorem exists_pmPowerDamped_cofinal_trace_zero {ε : ℝ} (hε : 0 < ε)
    (hf : MemLp (pmPowerDampedFermiSource ε) 2 (volume.restrict (Ioi (0 : ℝ)))) :
    ∃ N : ℕ → ℕ, StrictMono N ∧ (∀ n, 1 ≤ N n) ∧
      Tendsto (fun n => ‖pmPowerDampedDivisorRemainder ε (N n)‖ ^ 2 / (N n : ℝ)) atTop (𝓝 0) := by
  let w := fun n : ℕ => pmPowerDampedCenteredDivisorPrefix ε (n + 1) ^ 2 /
    (((n : ℝ) + 1) * ((n : ℝ) + 2))
  have hw : ∀ n, 0 ≤ w n := fun n => by dsimp only [w]; positivity
  have hs : Summable w := (pmPowerDampedFermiSource_memLp_iff_discrete_energy hε).mp hf
  obtain ⟨k, hk, hkt⟩ := pm_exists_strictMono_weighted_trace_zero hw hs
  refine ⟨fun n => k n + 1, fun i j hij => Nat.add_lt_add_right (hk hij) 1,
    fun n => Nat.succ_le_succ (Nat.zero_le (k n)), ?_⟩
  apply hkt.congr'
  exact Eventually.of_forall fun n => by
    dsimp only
    rw [pmPowerDampedDivisorRemainder_nat_norm_sq hε]
    dsimp only [w]
    push_cast
    field_simp

theorem exists_pmPowerDamped_cofinal_repairedHaar_L2 {ε : ℝ} (hε : 0 < ε)
    (hf : MemLp (pmPowerDampedFermiSource ε) 2 (volume.restrict (Ioi (0 : ℝ)))) :
    ∃ N : ℕ → ℕ, StrictMono N ∧ (∀ n, 1 ≤ N n) ∧
      Tendsto (fun n => ∫ t in Ioi (0 : ℝ),
        ‖pmPowerDampedRepairedHaarPrefix ε (N n) t - pmPowerDampedFermiSource ε t‖ ^ 2)
        atTop (𝓝 0) := by
  obtain ⟨N, hN, hNp, ht⟩ := exists_pmPowerDamped_cofinal_trace_zero hε hf
  exact ⟨N, hN, hNp,
    (pmPowerDampedRepairedHaarPrefix_L2_iff_trace hε hf hNp hN.tendsto_atTop).mpr ht⟩

theorem pmPowerDampedFermiSource_memLp_iff_repairedHaar_budget {ε : ℝ} (hε : 0 < ε) :
    MemLp (pmPowerDampedFermiSource ε) 2 (volume.restrict (Ioi (0 : ℝ))) ↔
      ∃ N : ℕ → ℕ, StrictMono N ∧ (∀ n, 1 ≤ N n) ∧ ∃ C : ℝ,
        ∀ n, eLpNorm (pmPowerDampedRepairedHaarPrefix ε (N n)) 2
          (volume.restrict (Ioi (0 : ℝ))) ≤ ENNReal.ofReal C := by
  constructor
  · intro hf
    obtain ⟨N, hN, hNp, ht⟩ := exists_pmPowerDamped_cofinal_repairedHaar_L2 hε hf
    let C := lpNorm (pmPowerDampedFermiSource ε) 2 (volume.restrict (Ioi (0 : ℝ))) + 1
    have hbound : ∀ᶠ n : ℕ in atTop,
        eLpNorm (pmPowerDampedRepairedHaarPrefix ε (N n)) 2
          (volume.restrict (Ioi (0 : ℝ))) ≤ ENNReal.ofReal C := by
      filter_upwards [ht.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))] with n hn
      have hb := memLp_pmPowerDampedRepairedHaarPrefix hε.le (hNp n)
      have he := hb.sub hf
      have hsq : lpNorm (pmPowerDampedRepairedHaarPrefix ε (N n) - pmPowerDampedFermiSource ε)
          2 (volume.restrict (Ioi (0 : ℝ))) ^ 2 < 1 := by
        change (∫ t in Ioi (0 : ℝ),
          ‖(pmPowerDampedRepairedHaarPrefix ε (N n) - pmPowerDampedFermiSource ε) t‖ ^ 2) < 1 at hn
        rw [pm_integral_norm_sq_toLp he, Lp.norm_toLp,
          toReal_eLpNorm he.aestronglyMeasurable] at hn
        exact hn
      have hsmall : lpNorm (pmPowerDampedRepairedHaarPrefix ε (N n) - pmPowerDampedFermiSource ε)
          2 (volume.restrict (Ioi (0 : ℝ))) ≤ 1 := by nlinarith
      rw [← ofReal_lpNorm hb]
      apply ENNReal.ofReal_le_ofReal
      have hh := lpNorm_le_lpNorm_add_lpNorm_sub' hf
        (f := pmPowerDampedRepairedHaarPrefix ε (N n)) (by norm_num)
      dsimp only [C]
      linarith
    obtain ⟨n₀, hn₀⟩ := eventually_atTop.mp hbound
    refine ⟨fun n => N (n + n₀), fun i j hij => hN (Nat.add_lt_add_right hij n₀),
      fun n => hNp (n + n₀), C, fun n => hn₀ (n + n₀) (by omega)⟩
  · rintro ⟨N, hN, hNp, C, hC⟩
    refine ⟨(measurable_pmPowerDampedFermiSource ε).aestronglyMeasurable, ?_⟩
    apply lt_of_le_of_lt (Lp.eLpNorm_le_of_ae_tendsto (u := (atTop : Filter ℕ))
      (Eventually.of_forall hC)
      (fun n => (memLp_pmPowerDampedRepairedHaarPrefix hε.le (hNp n)).aestronglyMeasurable) ?_)
      ENNReal.ofReal_lt_top
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact (tendsto_pmPowerDampedRepairedHaarPrefix ε ht).comp hN.tendsto_atTop

theorem riemannHypothesis_of_pmPowerDamped_cofinal_repairedHaar_budget
    (hbudget : ∀ δ : ℝ, 0 < δ → ∃ ε : ℝ, 0 < ε ∧ ε < δ ∧
      ∃ N : ℕ → ℕ, StrictMono N ∧ (∀ n, 1 ≤ N n) ∧ ∃ C : ℝ,
        ∀ n, eLpNorm (pmPowerDampedRepairedHaarPrefix ε (N n)) 2
          (volume.restrict (Ioi (0 : ℝ))) ≤ ENNReal.ofReal C) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_pmPowerDamped_cofinal_admission
  intro δ hδ
  obtain ⟨ε, hε, hεδ, hB⟩ := hbudget δ hδ
  exact ⟨ε, hε, hεδ, (pmPowerDampedFermiSource_memLp_iff_repairedHaar_budget hε).mpr hB⟩

end RHTower
