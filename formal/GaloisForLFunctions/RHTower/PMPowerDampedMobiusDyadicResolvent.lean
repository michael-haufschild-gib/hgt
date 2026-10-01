import GaloisForLFunctions.RHTower.PMPowerDampedMobiusDerivativeMellin

/-!
# The supported dyadic Haar resolvent

The locally finite dyadic Haar sum is canonically L² with exact energy two
and mean zero. Support above one and its difference equation determine it
pointwise without a norm premise. This supplies the positive source geometry
for the prime-two deletion test.
-/

open MeasureTheory Set Filter Topology Complex
noncomputable section
namespace RHTower


theorem measurable_pmSupportedDyadicHaar : Measurable pmSupportedDyadicHaar :=
  measurable_dyadicHaar.indicator measurableSet_Ioc

theorem pmSupportedDyadicHaar_norm_sq (t : ℝ) :
    ‖pmSupportedDyadicHaar t‖ ^ (2 : ℕ) =
      (Ioc (0 : ℝ) 1).indicator (fun _ => (1 : ℝ)) t := by
  by_cases ht : t ∈ Ioc (0 : ℝ) 1
  · simp [pmSupportedDyadicHaar, Set.indicator_of_mem ht, norm_dyadicHaar]
  · simp [pmSupportedDyadicHaar, Set.indicator_of_notMem ht]

theorem integrable_pmSupportedDyadicHaar_norm_sq :
    Integrable (fun t => ‖pmSupportedDyadicHaar t‖ ^ (2 : ℕ)) (volume.restrict (Ioi 0)) := by
  have hi : Integrable ((Ioc (0 : ℝ) 1).indicator (fun _ => (1 : ℝ))) volume :=
    (integrable_indicator_iff measurableSet_Ioc).mpr
      (integrableOn_const (C := (1 : ℝ)) measure_Ioc_lt_top.ne)
  simpa only [pmSupportedDyadicHaar_norm_sq] using hi.mono_measure Measure.restrict_le_self

theorem memLp_pmSupportedDyadicHaar :
    MemLp pmSupportedDyadicHaar 2 (volume.restrict (Ioi 0)) :=
  (memLp_two_iff_integrable_sq_norm measurable_pmSupportedDyadicHaar.aestronglyMeasurable).mpr
    integrable_pmSupportedDyadicHaar_norm_sq

theorem pmSupportedDyadicHaar_energy :
    (∫ t in Ioi (0 : ℝ), ‖pmSupportedDyadicHaar t‖ ^ (2 : ℕ)) = 1 := by
  simp_rw [pmSupportedDyadicHaar_norm_sq]
  rw [setIntegral_indicator measurableSet_Ioc,
    Set.inter_eq_right.mpr (show Ioc (0 : ℝ) 1 ⊆ Ioi 0 from Ioc_subset_Ioi_self)]
  simp

theorem pmSupportedDyadicHaar_integral :
    (∫ t in Ioi (0 : ℝ), pmSupportedDyadicHaar t) = 0 := by
  unfold pmSupportedDyadicHaar
  rw [setIntegral_indicator measurableSet_Ioc,
    Set.inter_eq_right.mpr (show Ioc (0 : ℝ) 1 ⊆ Ioi 0 from Ioc_subset_Ioi_self)]
  exact pm_integral_dyadicHaar

def pmDyadicHaarTerm (k : ℕ) (t : ℝ) : ℂ := pmSupportedDyadicHaar ((2 : ℝ) ^ k * t)

theorem measurable_pmDyadicHaarTerm (k : ℕ) : Measurable (pmDyadicHaarTerm k) :=
  measurable_pmSupportedDyadicHaar.comp (measurable_const.mul measurable_id)

theorem memLp_pmDyadicHaarTerm (k : ℕ) :
    MemLp (pmDyadicHaarTerm k) 2 (volume.restrict (Ioi 0)) := by
  apply (memLp_two_iff_integrable_sq_norm (measurable_pmDyadicHaarTerm k).aestronglyMeasurable).mpr
  have h := (integrableOn_Ioi_comp_mul_left_iff
    (fun t => ‖pmSupportedDyadicHaar t‖ ^ (2 : ℕ)) 0
    (by positivity : 0 < (2 : ℝ) ^ k)).mpr
      (by
        change Integrable (fun t => ‖pmSupportedDyadicHaar t‖ ^ (2 : ℕ))
          (volume.restrict (Ioi ((2 : ℝ) ^ k * 0)))
        simpa only [mul_zero] using integrable_pmSupportedDyadicHaar_norm_sq)
  exact h

theorem pmDyadicHaarTerm_energy (k : ℕ) :
    (∫ t in Ioi (0 : ℝ), ‖pmDyadicHaarTerm k t‖ ^ (2 : ℕ)) = ((2 : ℝ) ^ k)⁻¹ := by
  unfold pmDyadicHaarTerm
  rw [integral_comp_mul_left_Ioi (fun t => ‖pmSupportedDyadicHaar t‖ ^ (2 : ℕ)) 0
    (by positivity : 0 < (2 : ℝ) ^ k), mul_zero, pmSupportedDyadicHaar_energy]
  simp

theorem pmDyadicHaarTerm_integral (k : ℕ) :
    (∫ t in Ioi (0 : ℝ), pmDyadicHaarTerm k t) = 0 := by
  unfold pmDyadicHaarTerm
  rw [integral_comp_mul_left_Ioi pmSupportedDyadicHaar 0
    (by positivity : 0 < (2 : ℝ) ^ k), mul_zero, pmSupportedDyadicHaar_integral, smul_zero]


theorem pmDyadicHaarTerm_lpNorm (k : ℕ) :
    lpNorm (pmDyadicHaarTerm k) 2 (volume.restrict (Ioi 0)) = Real.sqrt (1 / 2) ^ k := by
  have hn : lpNorm (pmDyadicHaarTerm k) 2 (volume.restrict (Ioi 0)) ^ 2 = ((2 : ℝ) ^ k)⁻¹ := by
    rw [← pmDyadicHaarTerm_energy k, pm_integral_norm_sq_toLp (memLp_pmDyadicHaarTerm k),
      Lp.norm_toLp, toReal_eLpNorm (memLp_pmDyadicHaarTerm k).aestronglyMeasurable]
  have hr : (Real.sqrt (1 / 2) ^ k) ^ 2 = ((2 : ℝ) ^ k)⁻¹ := by
    calc
      _ = (Real.sqrt (1 / 2) ^ 2) ^ k := by rw [← pow_mul, ← pow_mul, Nat.mul_comm]
      _ = _ := by rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 1 / 2)]; simp [one_div, inv_pow]
  have hp : 0 ≤ Real.sqrt (1 / 2) ^ k := pow_nonneg (Real.sqrt_nonneg _) _
  nlinarith [lpNorm_nonneg (f := pmDyadicHaarTerm k) (p := 2) (μ := volume.restrict (Ioi 0))]

theorem summable_pmDyadicHaarTerm_norm : Summable (fun k : ℕ => Real.sqrt (1 / 2) ^ k) := by
  apply summable_geometric_of_lt_one (Real.sqrt_nonneg _)
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hp := Real.sqrt_nonneg (1 / 2 : ℝ)
  nlinarith

theorem summable_pmDyadicHaarTerm (t : ℝ) : Summable (fun k : ℕ => pmDyadicHaarTerm k t) := by
  by_cases ht : 0 < t
  · have hpow := (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)).atTop_mul_const ht
    obtain ⟨N, hN⟩ := eventually_atTop.mp (hpow.eventually (eventually_gt_atTop (1 : ℝ)))
    apply summable_of_ne_finset_zero (s := Finset.range N)
    intro k hk
    apply pmSupportedDyadicHaar_eq_zero
    exact hN k (Nat.le_of_not_gt (by simpa using hk))
  · have hz (k : ℕ) : pmDyadicHaarTerm k t = 0 := by
      unfold pmDyadicHaarTerm pmSupportedDyadicHaar
      apply Set.indicator_of_notMem
      intro h
      have hp : 0 ≤ (2 : ℝ) ^ k := by positivity
      have hnonpos := mul_nonpos_of_nonneg_of_nonpos hp (le_of_not_gt ht)
      exact (not_lt_of_ge hnonpos) h.1
    simp_rw [hz]
    exact summable_zero

def pmDyadicHaarResolvent (t : ℝ) : ℂ := ∑' k : ℕ, pmDyadicHaarTerm k t

theorem measurable_pmDyadicHaarResolvent : Measurable pmDyadicHaarResolvent :=
  Measurable.tsum (fun k => measurable_pmDyadicHaarTerm k)

def pmDyadicHaarPrefix (N : ℕ) (t : ℝ) : ℂ := ∑ k ∈ Finset.range N, pmDyadicHaarTerm k t

theorem memLp_pmDyadicHaarPrefix (N : ℕ) :
    MemLp (pmDyadicHaarPrefix N) 2 (volume.restrict (Ioi 0)) := by
  apply memLp_finsetSum (Finset.range N)
  intro k _
  exact memLp_pmDyadicHaarTerm k

theorem pmDyadicHaarPrefix_norm_le (N : ℕ) :
    eLpNorm (pmDyadicHaarPrefix N) 2 (volume.restrict (Ioi 0)) ≤
      ENNReal.ofReal (∑' k : ℕ, Real.sqrt (1 / 2) ^ k) := by
  rw [← ofReal_lpNorm (memLp_pmDyadicHaarPrefix N)]
  apply ENNReal.ofReal_le_ofReal
  have heq : pmDyadicHaarPrefix N = ∑ k ∈ Finset.range N, pmDyadicHaarTerm k := by
    ext t
    simp [pmDyadicHaarPrefix]
  rw [heq]
  calc
    _ ≤ ∑ k ∈ Finset.range N, lpNorm (pmDyadicHaarTerm k) 2 (volume.restrict (Ioi 0)) :=
      lpNorm_sum_le (fun k _ => memLp_pmDyadicHaarTerm k) (by norm_num)
    _ = ∑ k ∈ Finset.range N, Real.sqrt (1 / 2) ^ k := by simp_rw [pmDyadicHaarTerm_lpNorm]
    _ ≤ _ := summable_pmDyadicHaarTerm_norm.sum_le_tsum _
      (fun k _ => pow_nonneg (Real.sqrt_nonneg _) _)

theorem memLp_pmDyadicHaarResolvent :
    MemLp pmDyadicHaarResolvent 2 (volume.restrict (Ioi 0)) := by
  have hnorm : eLpNorm pmDyadicHaarResolvent 2 (volume.restrict (Ioi 0)) ≤
      ENNReal.ofReal (∑' k : ℕ, Real.sqrt (1 / 2) ^ k) := by
    apply Lp.eLpNorm_le_of_ae_tendsto (u := (atTop : Filter ℕ))
      (Eventually.of_forall fun N => pmDyadicHaarPrefix_norm_le N)
      (fun N => (memLp_pmDyadicHaarPrefix N).aestronglyMeasurable)
    exact Eventually.of_forall fun t => (summable_pmDyadicHaarTerm t).tendsto_sum_tsum_nat
  exact ⟨measurable_pmDyadicHaarResolvent.aestronglyMeasurable,
    hnorm.trans_lt ENNReal.ofReal_lt_top⟩


theorem pmDyadicHaarResolvent_eq_zero {t : ℝ} (ht : 1 < t) : pmDyadicHaarResolvent t = 0 := by
  have hz (k : ℕ) : pmDyadicHaarTerm k t = 0 := by
    apply pmSupportedDyadicHaar_eq_zero
    have hp : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
    have hm := mul_le_mul_of_nonneg_right hp (by linarith : 0 ≤ t)
    linarith
  simp only [pmDyadicHaarResolvent, hz, tsum_zero]

theorem pmDyadicHaarResolvent_eq (t : ℝ) :
    pmDyadicHaarResolvent t = pmSupportedDyadicHaar t + pmDyadicHaarResolvent (2 * t) := by
  have h := (summable_pmDyadicHaarTerm t).sum_add_tsum_nat_add 1
  have hs (k : ℕ) : pmDyadicHaarTerm (k + 1) t = pmDyadicHaarTerm k (2 * t) := by
    unfold pmDyadicHaarTerm
    rw [pow_succ]
    congr 1
    ring
  simp only [Finset.sum_range_one] at h
  simp_rw [hs] at h
  simpa only [pmDyadicHaarTerm, pow_zero, one_mul, pmDyadicHaarResolvent] using h.symm

theorem integrable_pmDyadicHaarResolvent :
    Integrable pmDyadicHaarResolvent (volume.restrict (Ioi 0)) := by
  have hh : IntegrableOn pmDyadicHaarResolvent (Ioc (0 : ℝ) 1) :=
    (memLp_pmDyadicHaarResolvent.mono_measure
    (Measure.restrict_mono (show Ioc (0 : ℝ) 1 ⊆ Ioi 0 from Ioc_subset_Ioi_self) le_rfl)).integrable
      (by norm_num : (1 : ENNReal) ≤ 2)
  have ht : IntegrableOn pmDyadicHaarResolvent (Ioi (1 : ℝ)) := by
    apply integrableOn_zero.congr_fun _ measurableSet_Ioi
    intro t ht
    exact (pmDyadicHaarResolvent_eq_zero ht).symm
  change IntegrableOn pmDyadicHaarResolvent (Ioi (0 : ℝ))
  rw [← Ioc_union_Ioi_eq_Ioi (show (0 : ℝ) ≤ 1 from zero_le_one)]
  exact hh.union ht

theorem integrable_pmDyadicHaarResolvent_dilate :
    Integrable (fun t => pmDyadicHaarResolvent (2 * t)) (volume.restrict (Ioi 0)) := by
  apply (integrableOn_Ioi_comp_mul_left_iff pmDyadicHaarResolvent 0
    (by norm_num : (0 : ℝ) < 2)).mpr
  change Integrable pmDyadicHaarResolvent (volume.restrict (Ioi ((2 : ℝ) * 0)))
  simpa only [mul_zero] using integrable_pmDyadicHaarResolvent

theorem pmDyadicHaarResolvent_integral :
    (∫ t in Ioi (0 : ℝ), pmDyadicHaarResolvent t) = 0 := by
  have hH : Integrable pmSupportedDyadicHaar (volume.restrict (Ioi 0)) := by
    simpa [MellinConvergent, IntegrableOn] using
      (hasMellin_pmSupportedDyadicHaar (s := 1) (by norm_num)).1
  have h := integral_congr_ae (μ := volume.restrict (Ioi (0 : ℝ)))
    (Eventually.of_forall pmDyadicHaarResolvent_eq)
  rw [integral_add hH integrable_pmDyadicHaarResolvent_dilate,
    pmSupportedDyadicHaar_integral, zero_add,
    integral_comp_mul_left_Ioi pmDyadicHaarResolvent 0 (by norm_num : (0 : ℝ) < 2),
    mul_zero, Complex.real_smul] at h
  push_cast at h
  linear_combination 2 * h

theorem pmDyadicHaarResolvent_energy_decomposition {t : ℝ} (ht : 0 < t) :
    ‖pmDyadicHaarResolvent t‖ ^ (2 : ℕ) =
      ‖pmSupportedDyadicHaar t‖ ^ (2 : ℕ) +
      ‖pmDyadicHaarResolvent (2 * t)‖ ^ (2 : ℕ) -
      2 * (pmDyadicHaarResolvent (2 * t)).re := by
  by_cases hh : t ≤ 1 / 2
  · have hH : pmSupportedDyadicHaar t = -1 := by
      rw [pmSupportedDyadicHaar, Set.indicator_of_mem (show t ∈ Ioc (0 : ℝ) 1 from
        ⟨ht, by linarith⟩), dyadicHaar, if_pos hh]
    rw [pmDyadicHaarResolvent_eq t, hH]
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im,
      Complex.neg_re, Complex.neg_im, Complex.one_re, Complex.one_im]
    ring
  · have hB : pmDyadicHaarResolvent (2 * t) = 0 :=
      pmDyadicHaarResolvent_eq_zero (by linarith)
    rw [pmDyadicHaarResolvent_eq t, hB]
    simp

theorem pmDyadicHaarResolvent_energy :
    (∫ t in Ioi (0 : ℝ), ‖pmDyadicHaarResolvent t‖ ^ (2 : ℕ)) = 2 := by
  have hB := memLp_pmDyadicHaarResolvent.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  have hB2 : Integrable (fun t => ‖pmDyadicHaarResolvent (2 * t)‖ ^ (2 : ℕ))
      (volume.restrict (Ioi 0)) := by
    apply (integrableOn_Ioi_comp_mul_left_iff
      (fun t => ‖pmDyadicHaarResolvent t‖ ^ (2 : ℕ)) 0 (by norm_num : (0 : ℝ) < 2)).mpr
    change Integrable (fun t => ‖pmDyadicHaarResolvent t‖ ^ (2 : ℕ))
      (volume.restrict (Ioi ((2 : ℝ) * 0)))
    simpa only [mul_zero] using hB
  have hm : (∫ t in Ioi (0 : ℝ), (pmDyadicHaarResolvent (2 * t)).re) = 0 := by
    calc
      _ = (∫ t in Ioi (0 : ℝ), pmDyadicHaarResolvent (2 * t)).re :=
        integral_re integrable_pmDyadicHaarResolvent_dilate
      _ = 0 := by
        rw [integral_comp_mul_left_Ioi pmDyadicHaarResolvent 0 (by norm_num : (0 : ℝ) < 2),
          mul_zero, pmDyadicHaarResolvent_integral, smul_zero, Complex.zero_re]
  have h : (∫ t in Ioi (0 : ℝ), ‖pmDyadicHaarResolvent t‖ ^ (2 : ℕ)) =
      ∫ t in Ioi (0 : ℝ), (‖pmSupportedDyadicHaar t‖ ^ (2 : ℕ) +
        ‖pmDyadicHaarResolvent (2 * t)‖ ^ (2 : ℕ) - 2 * (pmDyadicHaarResolvent (2 * t)).re) :=
    setIntegral_congr_fun measurableSet_Ioi
      (fun t ht => pmDyadicHaarResolvent_energy_decomposition ht)
  erw [integral_sub (integrable_pmSupportedDyadicHaar_norm_sq.add hB2)
      (integrable_pmDyadicHaarResolvent_dilate.re.const_mul 2),
    integral_add integrable_pmSupportedDyadicHaar_norm_sq hB2,
    integral_const_mul, hm, mul_zero, sub_zero, pmSupportedDyadicHaar_energy,
    integral_comp_mul_left_Ioi (fun t => ‖pmDyadicHaarResolvent t‖ ^ (2 : ℕ)) 0
      (by norm_num : (0 : ℝ) < 2), mul_zero, smul_eq_mul] at h
  linarith

/-- Support above one and the dyadic difference equation uniquely determine the physical source. -/
theorem pmDyadicHaarResolvent_unique {f : ℝ → ℂ}
    (hf : ∀ t : ℝ, 0 < t → f t = pmSupportedDyadicHaar t + f (2 * t))
    (hsupp : ∀ t : ℝ, 1 < t → f t = 0) {t : ℝ} (ht : 0 < t) :
    f t = pmDyadicHaarResolvent t := by
  have hstep (x : ℝ) (hx : 0 < x) :
      f x - pmDyadicHaarResolvent x = f (2 * x) - pmDyadicHaarResolvent (2 * x) := by
    rw [hf x hx, pmDyadicHaarResolvent_eq x]
    ring
  have hiter (k : ℕ) : f t - pmDyadicHaarResolvent t =
      f ((2 : ℝ) ^ k * t) - pmDyadicHaarResolvent ((2 : ℝ) ^ k * t) := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [ih, hstep _ (mul_pos (by positivity) ht)]
      congr 2 <;> rw [pow_succ] <;> ring
  have hpow := (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)).atTop_mul_const ht
  obtain ⟨k, hk⟩ := (hpow.eventually (eventually_gt_atTop (1 : ℝ))).exists
  have h := hiter k
  rw [hsupp _ hk, pmDyadicHaarResolvent_eq_zero hk, sub_self] at h
  exact sub_eq_zero.mp h

/-- The complete dyadic resolvent has exact canonical norm sqrt 2. -/
theorem pmDyadicHaarResolvent_eLpNorm :
    eLpNorm pmDyadicHaarResolvent 2 (volume.restrict (Ioi 0)) = ENNReal.ofReal (Real.sqrt 2) := by
  have hn : lpNorm pmDyadicHaarResolvent 2 (volume.restrict (Ioi 0)) ^ 2 = 2 := by
    rw [← pmDyadicHaarResolvent_energy,
      pm_integral_norm_sq_toLp memLp_pmDyadicHaarResolvent,
      Lp.norm_toLp, toReal_eLpNorm memLp_pmDyadicHaarResolvent.aestronglyMeasurable]
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hp := Real.sqrt_nonneg (2 : ℝ)
  have heq : lpNorm pmDyadicHaarResolvent 2 (volume.restrict (Ioi 0)) = Real.sqrt 2 := by
    nlinarith [lpNorm_nonneg (f := pmDyadicHaarResolvent) (p := 2) (μ := volume.restrict (Ioi 0))]
  rw [← ofReal_lpNorm memLp_pmDyadicHaarResolvent, heq]

end RHTower
