import GaloisForLFunctions.RHTower.PMPowerDampedMobiusHaarCutoffTrace

open MeasureTheory Set Filter Topology Complex
noncomputable section
namespace RHTower

theorem pmForwardDyadicDifference_initial_box {a : ℝ} (ha : 0 < a)
    (z : ℂ) {t : ℝ} (ht : 0 < t) :
    pmForwardDyadicDifference ((Ioc (0 : ℝ) (1 / a)).indicator (fun _ => z)) t =
      z * pmSupportedDyadicHaar (a * t) := by
  have h1 : a * t ≤ 1 ↔ t ≤ 1 / a := by
    rw [le_div_iff₀ ha]
    simp only [mul_comm]
  have h2 : a * t ≤ 1 / 2 ↔ 2 * t ≤ 1 / a := by
    rw [le_div_iff₀ ha]
    constructor <;> intro h <;> nlinarith
  rw [pmForwardDyadicDifference, pmSupportedDyadicHaar_eq_cutoffs (mul_pos ha ht)]
  simp only [h1, h2]
  simp only [Set.indicator, Set.mem_Ioc, ht, show 0 < 2 * t by positivity, true_and]
  split_ifs <;> ring

theorem pmPowerDampedClippedCenteredSource_sub_initial (ε : ℝ) {a : ℝ}
    (ha : 0 < a) {t : ℝ} (ht : 0 < t) :
    pmPowerDampedClippedCenteredSource ε a t -
      (Ioc (0 : ℝ) (1 / a)).indicator (fun _ => pmPowerDampedDivisorRemainder ε a) t =
      (Ioi (1 / a)).indicator (pmPowerDampedCenteredSource ε) t := by
  by_cases hc : t ≤ 1 / a
  · rw [pmPowerDampedClippedCenteredSource_initial ε ha ⟨ht, hc⟩,
      indicator_of_mem (show t ∈ Ioc (0 : ℝ) (1 / a) from ⟨ht, hc⟩),
      indicator_of_notMem (show t ∉ Ioi (1 / a) from not_lt.mpr hc), sub_self]
  · have hct : 1 / a < t := lt_of_not_ge hc
    rw [pmPowerDampedClippedCenteredSource_tail ε ha hct.le,
      indicator_of_notMem (show t ∉ Ioc (0 : ℝ) (1 / a) from fun h => hc h.2),
      indicator_of_mem (show t ∈ Ioi (1 / a) from hct), sub_zero]

def pmPowerDampedEndpointHaarPrefix (ε : ℝ) (N : ℕ) (t : ℝ) : ℂ :=
  pmPowerDampedRepairedHaarPrefix ε N t -
    pmPowerDampedDivisorRemainder ε N * pmSupportedDyadicHaar ((N : ℝ) * t)

theorem measurable_pmPowerDampedEndpointHaarPrefix (ε : ℝ) (N : ℕ) :
    Measurable (pmPowerDampedEndpointHaarPrefix ε N) :=
  (measurable_pmPowerDampedRepairedHaarPrefix ε N).sub
    (measurable_const.mul (measurable_pmSupportedDyadicHaar.comp
      (measurable_const.mul measurable_id)))

theorem memLp_pmPowerDampedEndpointHaarPrefix {ε : ℝ} (hε : 0 ≤ ε)
    {N : ℕ} (hN : 1 ≤ N) :
    MemLp (pmPowerDampedEndpointHaarPrefix ε N) 2 (volume.restrict (Ioi (0 : ℝ))) := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  exact (memLp_pmPowerDampedRepairedHaarPrefix hε hN).sub
    ((memLp_pmSupportedDyadicHaar_dilation hNp).const_mul (pmPowerDampedDivisorRemainder ε N))

theorem pmPowerDampedEndpointHaarPrefix_eq_tail (ε : ℝ) {N : ℕ}
    (hN : 1 ≤ N) {t : ℝ} (ht : 0 < t) :
    pmPowerDampedEndpointHaarPrefix ε N t =
      pmForwardDyadicDifference
        ((Ioi (1 / (N : ℝ))).indicator (pmPowerDampedCenteredSource ε)) t := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  rw [pmPowerDampedEndpointHaarPrefix, pmPowerDampedRepairedHaarPrefix_eq_clipped ε hN ht,
    ← pmForwardDyadicDifference_initial_box hNp (pmPowerDampedDivisorRemainder ε N) ht]
  rw [pmForwardDyadicDifference, pmForwardDyadicDifference,
    ← pmPowerDampedClippedCenteredSource_sub_initial ε hNp ht,
    ← pmPowerDampedClippedCenteredSource_sub_initial ε hNp (by positivity : 0 < 2 * t)]
  ring

theorem pmPowerDampedEndpointHaarPrefix_error (ε : ℝ) {N : ℕ}
    (hN : 1 ≤ N) {t : ℝ} (ht : 0 < t) :
    pmPowerDampedEndpointHaarPrefix ε N t - pmPowerDampedFermiSource ε t =
      -pmForwardDyadicDifference
        ((Ioc (0 : ℝ) (1 / (N : ℝ))).indicator (pmPowerDampedCenteredSource ε)) t := by
  rw [pmPowerDampedEndpointHaarPrefix_eq_tail ε hN ht,
    pmPowerDampedFermiSource_eq_centered_difference ε ht]
  have hsplit {u : ℝ} (hu : 0 < u) :
      (Ioi (1 / (N : ℝ))).indicator (pmPowerDampedCenteredSource ε) u =
        pmPowerDampedCenteredSource ε u -
          (Ioc (0 : ℝ) (1 / (N : ℝ))).indicator (pmPowerDampedCenteredSource ε) u := by
    by_cases hc : u ≤ 1 / (N : ℝ)
    · rw [indicator_of_notMem (show u ∉ Ioi (1 / (N : ℝ)) from not_lt.mpr hc), indicator_of_mem (show u ∈ Ioc 0 (1 / (N : ℝ)) from ⟨hu, hc⟩), sub_self]
    · rw [indicator_of_mem (show u ∈ Ioi (1 / (N : ℝ)) from lt_of_not_ge hc),
        indicator_of_notMem (show u ∉ Ioc 0 (1 / (N : ℝ)) from fun h => hc h.2), sub_zero]
  simp only [pmForwardDyadicDifference, hsplit ht, hsplit (by positivity : 0 < 2 * t)]
  ring

theorem pmPowerDampedEndpointHaarPrefix_eq_source (ε : ℝ) (N : ℕ)
    {t : ℝ} (ht : 0 < t) (hN : 1 / t < (N : ℝ)) :
    pmPowerDampedEndpointHaarPrefix ε N t = pmPowerDampedFermiSource ε t := by
  rw [pmPowerDampedEndpointHaarPrefix, pmPowerDampedRepairedHaarPrefix_eq_source ε N ht hN.le,
    pmSupportedDyadicHaar_eq_zero ((div_lt_iff₀ ht).mp hN), mul_zero, sub_zero]

theorem tendsto_pmPowerDampedEndpointHaarPrefix (ε : ℝ) {t : ℝ} (ht : 0 < t) :
    Tendsto (fun N : ℕ => pmPowerDampedEndpointHaarPrefix ε N t) atTop
      (𝓝 (pmPowerDampedFermiSource ε t)) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [(tendsto_natCast_atTop_atTop (R := ℝ)).eventually (eventually_gt_atTop (1 / t))]
    with N hN
  exact (pmPowerDampedEndpointHaarPrefix_eq_source ε N ht hN).symm

theorem pm_integral_indicator_norm_sq (f : ℝ → ℂ) {s : Set ℝ} (hs : MeasurableSet s) :
    (∫ t in Ioi (0 : ℝ), ‖s.indicator f t‖ ^ 2) =
      ∫ t in Ioi (0 : ℝ) ∩ s, ‖f t‖ ^ 2 := by
  have he : (fun t => ‖s.indicator f t‖ ^ 2) = s.indicator (fun t => ‖f t‖ ^ 2) := by
    funext t
    by_cases ht : t ∈ s <;> simp [ht]
  rw [he, setIntegral_indicator hs]

theorem pmPowerDampedEndpointHaarPrefix_energy (ε : ℝ) {N : ℕ} (hN : 1 ≤ N) :
    (∫ t in Ioi (0 : ℝ), ‖pmPowerDampedEndpointHaarPrefix ε N t‖ ^ 2) =
      ∫ t in Ioi (0 : ℝ), ‖pmForwardDyadicDifference
        ((Ioi (1 / (N : ℝ))).indicator (pmPowerDampedCenteredSource ε)) t‖ ^ 2 := by
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [pmPowerDampedEndpointHaarPrefix_eq_tail ε hN ht]

theorem pmPowerDampedEndpointHaarPrefix_error_energy (ε : ℝ) {N : ℕ} (hN : 1 ≤ N) :
    (∫ t in Ioi (0 : ℝ),
      ‖pmPowerDampedEndpointHaarPrefix ε N t - pmPowerDampedFermiSource ε t‖ ^ 2) =
      ∫ t in Ioi (0 : ℝ), ‖pmForwardDyadicDifference
        ((Ioc (0 : ℝ) (1 / (N : ℝ))).indicator (pmPowerDampedCenteredSource ε)) t‖ ^ 2 := by
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [pmPowerDampedEndpointHaarPrefix_error ε hN ht, norm_neg]

theorem pmPowerDampedEndpointHaarPrefix_energy_le {ε : ℝ} (hε : 0 < ε)
    (hf : MemLp (pmPowerDampedFermiSource ε) 2 (volume.restrict (Ioi (0 : ℝ))))
    {N : ℕ} (hN : 1 ≤ N) :
    (∫ t in Ioi (0 : ℝ), ‖pmPowerDampedEndpointHaarPrefix ε N t‖ ^ 2) ≤
      (Real.sqrt 2 + 1) ^ 2 * ∫ t in Ioi (0 : ℝ), ‖pmPowerDampedCenteredSource ε t‖ ^ 2 := by
  have hfc := (pmPowerDampedFermiSource_memLp_iff_centered hε).mp hf
  have hfi := hfc.indicator (s := Ioi (1 / (N : ℝ))) measurableSet_Ioi
  have hi : (∫ t in Ioi (0 : ℝ),
      ‖(Ioi (1 / (N : ℝ))).indicator (pmPowerDampedCenteredSource ε) t‖ ^ 2) ≤
      ∫ t in Ioi (0 : ℝ), ‖pmPowerDampedCenteredSource ε t‖ ^ 2 := by
    apply integral_mono_ae hfi.norm.integrable_sq hfc.norm.integrable_sq
    exact Eventually.of_forall fun t => by
      by_cases ht : t ∈ Ioi (1 / (N : ℝ))
      · simp only [indicator_of_mem ht, le_refl]
      · simp only [indicator_of_notMem ht, norm_zero, zero_pow (by decide : 2 ≠ 0)]
        exact sq_nonneg _
  rw [pmPowerDampedEndpointHaarPrefix_energy ε hN]
  exact (pmForwardDyadicDifference_energy_bounds
    ((measurable_pmPowerDampedCenteredSource ε).indicator measurableSet_Ioi) hfi).1.trans
      (mul_le_mul_of_nonneg_left hi (sq_nonneg _))

theorem pmPowerDampedEndpointHaarPrefix_error_bounds {ε : ℝ} (hε : 0 < ε)
    (hf : MemLp (pmPowerDampedFermiSource ε) 2 (volume.restrict (Ioi (0 : ℝ))))
    {N : ℕ} (hN : 1 ≤ N) :
    (∫ t in Ioi (0 : ℝ),
      ‖pmPowerDampedEndpointHaarPrefix ε N t - pmPowerDampedFermiSource ε t‖ ^ 2) ≤
      (Real.sqrt 2 + 1) ^ 2 * (∫ t in Ioc (0 : ℝ) (1 / (N : ℝ)),
        ‖pmPowerDampedCenteredSource ε t‖ ^ 2) ∧
      (∫ t in Ioc (0 : ℝ) (1 / (N : ℝ)), ‖pmPowerDampedCenteredSource ε t‖ ^ 2) ≤
        (Real.sqrt 2 + 1) ^ 2 * (∫ t in Ioi (0 : ℝ),
          ‖pmPowerDampedEndpointHaarPrefix ε N t - pmPowerDampedFermiSource ε t‖ ^ 2) := by
  have hfc := (pmPowerDampedFermiSource_memLp_iff_centered hε).mp hf
  have h := pmForwardDyadicDifference_energy_bounds
    ((measurable_pmPowerDampedCenteredSource ε).indicator measurableSet_Ioc)
    (hfc.indicator (s := Ioc (0 : ℝ) (1 / (N : ℝ))) measurableSet_Ioc)
  rw [pm_integral_indicator_norm_sq _ measurableSet_Ioc,
    inter_eq_right.mpr (show Ioc (0 : ℝ) (1 / (N : ℝ)) ⊆ Ioi 0 from fun _ ht => ht.1),
    ← pmPowerDampedEndpointHaarPrefix_error_energy ε hN] at h
  exact h

theorem tendsto_pmPowerDampedEndpointHaarPrefix_L2 {ε : ℝ} (hε : 0 < ε)
    (hf : MemLp (pmPowerDampedFermiSource ε) 2 (volume.restrict (Ioi (0 : ℝ)))) :
    Tendsto (fun N : ℕ => ∫ t in Ioi (0 : ℝ),
      ‖pmPowerDampedEndpointHaarPrefix ε (N + 1) t - pmPowerDampedFermiSource ε t‖ ^ 2)
        atTop (𝓝 0) := by
  have hfc := (pmPowerDampedFermiSource_memLp_iff_centered hε).mp hf
  have ha : Tendsto (fun N : ℕ => ((N + 1 : ℕ) : ℝ)) atTop atTop := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      tendsto_atTop_add_const_right atTop 1 (tendsto_natCast_atTop_atTop (R := ℝ))
  have ht := tendsto_pm_initial_energy (measurable_pmPowerDampedCenteredSource ε) hfc
    (fun N => by positivity : ∀ N : ℕ, (0 : ℝ) < (N + 1 : ℕ)) ha
  apply squeeze_zero (fun N => integral_nonneg (fun _ => sq_nonneg _))
    (fun N => (pmPowerDampedEndpointHaarPrefix_error_bounds hε hf (Nat.succ_le_succ (Nat.zero_le N))).1)
  simpa only [mul_zero] using ht.const_mul ((Real.sqrt 2 + 1) ^ 2)

theorem pmPowerDampedFermiSource_memLp_iff_endpointHaar_budget {ε : ℝ} (hε : 0 < ε) :
    MemLp (pmPowerDampedFermiSource ε) 2 (volume.restrict (Ioi (0 : ℝ))) ↔
      ∃ B : ℝ, ∀ N : ℕ, 1 ≤ N →
        (∫ t in Ioi (0 : ℝ), ‖pmPowerDampedEndpointHaarPrefix ε N t‖ ^ 2) ≤ B := by
  constructor
  · intro hf
    exact ⟨_, fun N hN => pmPowerDampedEndpointHaarPrefix_energy_le hε hf hN⟩
  · rintro ⟨B, hB⟩
    have hn (n : ℕ) : eLpNorm (pmPowerDampedEndpointHaarPrefix ε (n + 1)) 2
        (volume.restrict (Ioi (0 : ℝ))) ≤ ENNReal.ofReal (Real.sqrt B) := by
      have hp := memLp_pmPowerDampedEndpointHaarPrefix hε.le
        (Nat.succ_le_succ (Nat.zero_le n))
      have hb := hB (n + 1) (Nat.succ_le_succ (Nat.zero_le n))
      rw [pm_integral_norm_sq_toLp hp, Lp.norm_toLp,
        toReal_eLpNorm hp.aestronglyMeasurable] at hb
      have hh := Real.sqrt_le_sqrt hb
      rw [Real.sqrt_sq lpNorm_nonneg] at hh
      rw [← ofReal_lpNorm hp]
      exact ENNReal.ofReal_le_ofReal hh
    refine ⟨(measurable_pmPowerDampedFermiSource ε).aestronglyMeasurable, ?_⟩
    apply lt_of_le_of_lt (Lp.eLpNorm_le_of_ae_tendsto (u := (atTop : Filter ℕ))
      (Eventually.of_forall hn)
      (fun n => (measurable_pmPowerDampedEndpointHaarPrefix ε (n + 1)).aestronglyMeasurable) ?_)
      ENNReal.ofReal_lt_top
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact (tendsto_pmPowerDampedEndpointHaarPrefix ε ht).comp (tendsto_add_atTop_nat 1)

theorem riemannHypothesis_of_pmPowerDamped_endpointHaar_budget
    (hbudget : ∀ δ : ℝ, 0 < δ → ∃ ε : ℝ, 0 < ε ∧ ε < δ ∧ ∃ B : ℝ,
      ∀ N : ℕ, 1 ≤ N →
        (∫ t in Ioi (0 : ℝ), ‖pmPowerDampedEndpointHaarPrefix ε N t‖ ^ 2) ≤ B) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_pmPowerDamped_cofinal_admission
  intro δ hδ
  obtain ⟨ε, hε, hεδ, hB⟩ := hbudget δ hδ
  exact ⟨ε, hε, hεδ, (pmPowerDampedFermiSource_memLp_iff_endpointHaar_budget hε).mpr hB⟩

end RHTower
