import GaloisForLFunctions.RHTower.FermiNymanBeurlingHaarTarget
import GaloisForLFunctions.RHTower.BaezDuarteMobiusCriticalTailObstruction
import GaloisForLFunctions.PNTPlus.Consequences

/-!
# Raw Möbius Fermi approximation: exact head and a forced tail floor

For the literal generators, `A_N = -Σ_{1≤d≤N} μ(d) φ_d` agrees with the dyadic Haar
function whenever `1/(N+1) < t ≤ 1`. Nevertheless its squared `L²(0,1]` error is at least
`(N+1) H_N² / 6`, where `H_N = Σ_{d≤N} μ(d)/d`. The corpus's unconditional cofinal
harmonic-energy floor therefore prevents this approximation error from tending to zero.

The continuous bridge uses `E_N(t) = 1_(0,1](t) + Σ μ(d){1/(dt)}` on the whole positive
half-line. Its exact tail is `H_N/t`; its dilation difference `E_N(t)-2E_N(2t)` equals
the Haar error on the unit interval and vanishes beyond it. Full-half-line coercivity
transfers the exact harmonic-tail energy to the literal Haar norm. No discrete norm
identification, zero-location hypothesis, or infinite-series interchange is used.

This obstruction concerns raw coefficients only. It does not establish the sign of
the compressed witness form, disprove Haar closure, or prove or disprove RH.
-/

open Complex MeasureTheory Set Filter Topology
open GaloisForLFunctions.NymanMellin
open ArithmeticFunction
noncomputable section
namespace RHTower

/-- The full positive-half-line difference, before any compression to the unit interval. -/
def fermiDilationDifference (f : ℝ → ℂ) (t : ℝ) : ℂ := f t - 2 * f (2 * t)

theorem integrableOn_normSq_fermiDilationDifference {f : ℝ → ℂ} (hf : Measurable f)
    (hi : IntegrableOn (fun t => ‖f t‖ ^ 2) (Ioi (0 : ℝ))) :
    IntegrableOn (fun t => ‖fermiDilationDifference f t‖ ^ 2) (Ioi (0 : ℝ)) := by
  have hg : IntegrableOn (fun t => ‖f (2 * t)‖ ^ 2) (Ioi (0 : ℝ)) := by
    apply (integrableOn_Ioi_comp_mul_left_iff (fun t => ‖f t‖ ^ 2) 0 (by norm_num : (0 : ℝ) < 2)).mpr
    simpa only [mul_zero] using hi
  have hdm : Measurable (fermiDilationDifference f) :=
    hf.sub (measurable_const.mul (hf.comp (measurable_const.mul measurable_id)))
  apply ((hi.const_mul 2).add (hg.const_mul 8)).mono' (hdm.norm.pow_const 2).aestronglyMeasurable
  filter_upwards with t
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have h := norm_sub_le (f t) ((2 : ℂ) * f (2 * t))
  rw [norm_mul] at h
  norm_num at h
  change ‖f t - 2 * f (2 * t)‖ ^ 2 ≤ 2 * ‖f t‖ ^ 2 + 8 * ‖f (2 * t)‖ ^ 2
  have hsq := pow_le_pow_left₀ (norm_nonneg _) h 2
  nlinarith [norm_nonneg (f t), norm_nonneg (f (2 * t)),
    norm_nonneg (f t - 2 * f (2 * t)), sq_nonneg (‖f t‖ - 2 * ‖f (2 * t)‖)]

/-- A rational coercivity constant for the literal half-line difference. -/
theorem integral_normSq_le_six_fermiDilationDifference {f : ℝ → ℂ} (hf : Measurable f)
    (hi : IntegrableOn (fun t => ‖f t‖ ^ 2) (Ioi (0 : ℝ))) :
    (∫ t in Ioi (0 : ℝ), ‖f t‖ ^ 2) ≤
      6 * ∫ t in Ioi (0 : ℝ), ‖fermiDilationDifference f t‖ ^ 2 := by
  have hg : IntegrableOn (fun t => ‖f (2 * t)‖ ^ 2) (Ioi (0 : ℝ)) := by
    apply (integrableOn_Ioi_comp_mul_left_iff (fun t => ‖f t‖ ^ 2) 0 (by norm_num : (0 : ℝ) < 2)).mpr
    simpa only [mul_zero] using hi
  have hd := integrableOn_normSq_fermiDilationDifference hf hi
  have hpoint : ∀ t : ℝ, 4 * ‖f (2 * t)‖ ^ 2 ≤
      (3 / 2 : ℝ) * ‖f t‖ ^ 2 + 3 * ‖fermiDilationDifference f t‖ ^ 2 := by
    intro t
    have h := norm_sub_le (f t) (fermiDilationDifference f t)
    rw [show f t - fermiDilationDifference f t = 2 * f (2 * t) by
      unfold fermiDilationDifference; ring, norm_mul] at h
    norm_num at h
    nlinarith [norm_nonneg (f t), norm_nonneg (f (2 * t)),
      norm_nonneg (fermiDilationDifference f t),
      sq_nonneg (‖f t‖ - 2 * ‖fermiDilationDifference f t‖)]
  have hle := setIntegral_mono_on (hg.const_mul 4)
    ((hi.const_mul (3 / 2)).add (hd.const_mul 3)) measurableSet_Ioi (fun t _ => hpoint t)
  simp only [Pi.add_apply] at hle
  rw [integral_add (hi.const_mul (3 / 2)) (hd.const_mul 3),
    integral_const_mul, integral_const_mul, integral_const_mul] at hle
  have hscale := integral_comp_mul_left_Ioi (fun t => ‖f t‖ ^ 2) 0 (by norm_num : (0 : ℝ) < 2)
  simp only [mul_zero, smul_eq_mul] at hscale
  rw [hscale] at hle
  norm_num at hle
  linarith

/-- Floor inversion remains exact beyond the last nonzero floor term. -/
theorem sum_moebius_floor_truncated (N : ℕ) {x : ℝ} (hx : 0 ≤ x)
    (hN : ⌊x⌋₊ ≤ N) :
    (∑ d ∈ Finset.Icc 1 N, ((moebius d : ℤ) : ℝ) * (⌊x / (d : ℝ)⌋ : ℝ)) =
      if 1 ≤ x then 1 else 0 := by
  classical
  have hzero : ∀ d : ℕ, 1 ≤ d → x < d → (⌊x / (d : ℝ)⌋ : ℤ) = 0 := by
    intro d hd hxd
    have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
    have hlo : (0 : ℤ) ≤ ⌊x / (d : ℝ)⌋ := Int.floor_nonneg.mpr (div_nonneg hx hd0.le)
    have hhi : ⌊x / (d : ℝ)⌋ < (1 : ℤ) := Int.floor_lt.mpr (by
      simpa using (div_lt_one hd0).mpr hxd)
    omega
  by_cases hx1 : 1 ≤ x
  · rw [if_pos hx1, ← sum_mobius_floor x hx1]
    apply (Finset.sum_subset (Finset.Icc_subset_Icc_right hN) ?_).symm
    intro d hd hnot
    have hd1 := (Finset.mem_Icc.mp hd).1
    have hdgt : ⌊x⌋₊ < d := by
      by_contra h
      exact hnot (Finset.mem_Icc.mpr ⟨hd1, le_of_not_gt h⟩)
    have hxd : x < d := lt_of_lt_of_le (Nat.lt_floor_add_one x) (by exact_mod_cast hdgt)
    rw [hzero d hd1 hxd]
    simp
  · rw [if_neg hx1]
    apply Finset.sum_eq_zero
    intro d hd
    rw [hzero d (Finset.mem_Icc.mp hd).1 (lt_of_lt_of_le (lt_of_not_ge hx1)
      (by exact_mod_cast (Finset.mem_Icc.mp hd).1))]
    simp

/-- The literal raw Möbius combination of the Fermi generators. -/
def rawMobiusFermiApprox (N : ℕ) (t : ℝ) : ℂ :=
  -(∑ d ∈ Finset.Icc 1 N, ((moebius d : ℤ) : ℂ) * fermiNymanGen (d : ℝ) t)

/-- The classical finite Nyman error on the whole positive half-line. -/
def rawMobiusNymanError (N : ℕ) (t : ℝ) : ℂ :=
  (Ioc (0 : ℝ) 1).indicator (fun _ => (1 : ℂ)) t +
    ∑ d ∈ Finset.Icc 1 N, ((moebius d : ℤ) : ℂ) * nymanGen (d : ℝ) t

theorem sum_moebius_nymanGen (N : ℕ) (t : ℝ) :
    (∑ d ∈ Finset.Icc 1 N, ((moebius d : ℤ) : ℂ) * nymanGen (d : ℝ) t) =
      ((deningerHarmonicPartial N / t -
        ∑ d ∈ Finset.Icc 1 N, ((moebius d : ℤ) : ℝ) * (⌊(1 / t) / d⌋ : ℝ) : ℝ) : ℂ) := by
  rw [deningerHarmonicPartial_eq_sum_Icc, Finset.sum_div, ← Finset.sum_sub_distrib]
  push_cast
  apply Finset.sum_congr rfl
  intro d hd
  unfold nymanGen Int.fract
  rw [show 1 / ((d : ℝ) * t) = (1 / t) / d by ring]
  push_cast
  ring

/-- Exact harmonic tail; the cutoff is `1/(N+1)`, including the case `N=0`. -/
theorem rawMobiusNymanError_eq_harmonic_tail (N : ℕ) {t : ℝ}
    (ht : 1 / ((N : ℝ) + 1) < t) :
    rawMobiusNymanError N t = ((deningerHarmonicPartial N / t : ℝ) : ℂ) := by
  have hNp : (0 : ℝ) < N + 1 := by positivity
  have ht0 : 0 < t := lt_trans (one_div_pos.mpr hNp) ht
  have hx : 0 ≤ 1 / t := by positivity
  have hxN : 1 / t < (N : ℝ) + 1 := by
    apply (div_lt_iff₀ ht0).mpr
    have h := (div_lt_iff₀ hNp).mp ht
    nlinarith
  have hfloor : ⌊1 / t⌋₊ ≤ N := by
    have h : (⌊1 / t⌋₊ : ℝ) < (N : ℝ) + 1 := lt_of_le_of_lt (Nat.floor_le hx) hxN
    exact Nat.le_of_lt_succ (by exact_mod_cast h)
  rw [rawMobiusNymanError, sum_moebius_nymanGen,
    sum_moebius_floor_truncated N hx hfloor]
  by_cases ht1 : t ≤ 1
  · have hx1 : 1 ≤ 1 / t := (le_div_iff₀ ht0).mpr (by simpa using ht1)
    rw [if_pos hx1, indicator_of_mem (show t ∈ Ioc (0 : ℝ) 1 from ⟨ht0, ht1⟩)]
    push_cast
    ring
  · have hx1 : ¬ 1 ≤ 1 / t := by
      rw [le_div_iff₀ ht0]
      simpa using ht1
    rw [if_neg hx1, indicator_of_notMem (fun h => ht1 h.2)]
    simp

/-- The literal Haar error is exactly the full-half-line dilation difference on `(0,1]`. -/
theorem dyadicHaar_sub_rawMobiusFermiApprox (N : ℕ) {t : ℝ} (ht : t ∈ Ioc (0 : ℝ) 1) :
    dyadicHaar t - rawMobiusFermiApprox N t =
      fermiDilationDifference (rawMobiusNymanError N) t := by
  have hgen : ∀ d : ℕ, nymanGen (d : ℝ) (2 * t) = nymanGen (2 * d) t := by
    intro d
    unfold nymanGen
    rw [show (d : ℝ) * (2 * t) = 2 * d * t by ring]
  have hchi : (Ioc (0 : ℝ) 1).indicator (fun _ => (1 : ℂ)) t -
      2 * (Ioc (0 : ℝ) 1).indicator (fun _ => (1 : ℂ)) (2 * t) = dyadicHaar t := by
    rw [indicator_of_mem ht, dyadicHaar]
    split_ifs with h
    · rw [indicator_of_mem (show 2 * t ∈ Ioc (0 : ℝ) 1 by constructor <;> linarith [ht.1])]
      norm_num
    · rw [indicator_of_notMem (show 2 * t ∉ Ioc (0 : ℝ) 1 by intro hmem; apply h; linarith [hmem.2])]
      simp
  unfold rawMobiusFermiApprox fermiDilationDifference rawMobiusNymanError
  simp_rw [fermiNymanGen, hgen, mul_sub]
  rw [Finset.sum_sub_distrib, ← hchi]
  have hsum : (∑ d ∈ Finset.Icc 1 N, ((moebius d : ℤ) : ℂ) * (2 * nymanGen (2 * d) t)) =
      2 * ∑ d ∈ Finset.Icc 1 N, ((moebius d : ℤ) : ℂ) * nymanGen (2 * d) t := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d _
    ring
  rw [hsum]
  ring

theorem fermiDilationDifference_rawMobiusNymanError_eq_zero (N : ℕ) {t : ℝ}
    (ht : 1 / ((N : ℝ) + 1) < t) :
    fermiDilationDifference (rawMobiusNymanError N) t = 0 := by
  have ht0 : 0 < t := lt_trans (by positivity) ht
  rw [fermiDilationDifference, rawMobiusNymanError_eq_harmonic_tail N ht,
    rawMobiusNymanError_eq_harmonic_tail N (by linarith : 1 / ((N : ℝ) + 1) < 2 * t)]
  push_cast
  field_simp
  ring

/-- The raw coefficients reproduce the Haar target on an expanding head interval. -/
theorem rawMobiusFermiApprox_eq_dyadicHaar (N : ℕ) {t : ℝ}
    (ht : 1 / ((N : ℝ) + 1) < t) (ht1 : t ≤ 1) :
    rawMobiusFermiApprox N t = dyadicHaar t := by
  have ht0 : 0 < t := lt_trans (by positivity) ht
  have h := dyadicHaar_sub_rawMobiusFermiApprox N ⟨ht0, ht1⟩
  rw [fermiDilationDifference_rawMobiusNymanError_eq_zero N ht] at h
  exact (sub_eq_zero.mp h).symm


theorem measurable_rawMobiusNymanError (N : ℕ) : Measurable (rawMobiusNymanError N) := by
  unfold rawMobiusNymanError
  exact (measurable_const.indicator measurableSet_Ioc).add
    (Finset.measurable_sum _ (fun d _ => measurable_const.mul (measurable_nymanGen _)))

theorem norm_rawMobiusNymanError_le (N : ℕ) (t : ℝ) :
    ‖rawMobiusNymanError N t‖ ≤ 1 + ∑ d ∈ Finset.Icc 1 N, ‖((moebius d : ℤ) : ℂ)‖ := by
  have hchi : ‖(Ioc (0 : ℝ) 1).indicator (fun _ => (1 : ℂ)) t‖ ≤ 1 := by
    by_cases ht : t ∈ Ioc (0 : ℝ) 1
    · simp [indicator_of_mem ht]
    · simp [indicator_of_notMem ht]
  unfold rawMobiusNymanError
  refine (norm_add_le _ _).trans (add_le_add hchi ?_)
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun d _ => ?_))
  rw [norm_mul]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left (norm_nymanGen_le (d : ℝ) t)
    (norm_nonneg (((moebius d : ℤ) : ℂ)))

theorem normSq_real_div_eq_rpow (H : ℝ) {t : ℝ} (ht : 0 < t) :
    ‖((H / t : ℝ) : ℂ)‖ ^ 2 = H ^ 2 * t ^ (-2 : ℝ) := by
  rw [Complex.norm_real, Real.norm_eq_abs, sq_abs, div_pow,
    Real.rpow_neg ht.le, Real.rpow_two]
  rfl

theorem integrableOn_normSq_real_div (H : ℝ) {c : ℝ} (hc : 0 < c) :
    IntegrableOn (fun t => ‖((H / t : ℝ) : ℂ)‖ ^ 2) (Ioi c) := by
  have hi : IntegrableOn (fun t : ℝ => H ^ 2 * t ^ (-2 : ℝ)) (Ioi c) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hc).const_mul (H ^ 2)
  refine hi.congr_fun (fun t ht => ?_) measurableSet_Ioi
  exact (normSq_real_div_eq_rpow H (lt_trans hc ht)).symm

theorem integral_normSq_real_div (H : ℝ) {c : ℝ} (hc : 0 < c) :
    (∫ t in Ioi c, ‖((H / t : ℝ) : ℂ)‖ ^ 2) = H ^ 2 / c := by
  rw [setIntegral_congr_fun measurableSet_Ioi (fun t ht => normSq_real_div_eq_rpow H (lt_trans hc ht)),
    integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hc]
  norm_num [Real.rpow_neg_one, div_eq_mul_inv]

theorem integrableOn_normSq_rawMobiusNymanError (N : ℕ) :
    IntegrableOn (fun t => ‖rawMobiusNymanError N t‖ ^ 2) (Ioi (0 : ℝ)) := by
  rw [← Ioc_union_Ioi_eq_Ioi (by norm_num : (0 : ℝ) ≤ 1)]
  refine IntegrableOn.union ?_ ?_
  · refine Measure.integrableOn_of_bounded
      (M := (1 + ∑ d ∈ Finset.Icc 1 N, ‖((moebius d : ℤ) : ℂ)‖) ^ 2)
      measure_Ioc_lt_top.ne ((measurable_rawMobiusNymanError N).norm.pow_const 2).aestronglyMeasurable
      (Filter.Eventually.of_forall fun t => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_rawMobiusNymanError_le N t) 2
  · refine (integrableOn_normSq_real_div (deningerHarmonicPartial N) (by norm_num : (0 : ℝ) < 1)).congr_fun
      (fun t ht => ?_) measurableSet_Ioi
    rw [rawMobiusNymanError_eq_harmonic_tail N (lt_of_le_of_lt ?_ ht)]
    exact (div_le_one (by positivity : (0 : ℝ) < N + 1)).mpr
      (le_add_of_nonneg_left (Nat.cast_nonneg N))

/-- The exact nonnegative contribution supplied by the reciprocal harmonic tail. -/
theorem integral_normSq_rawMobiusNymanError_tail (N : ℕ) :
    (∫ t in Ioi (1 / ((N : ℝ) + 1)), ‖rawMobiusNymanError N t‖ ^ 2) =
      ((N : ℝ) + 1) * deningerHarmonicPartial N ^ 2 := by
  rw [setIntegral_congr_fun measurableSet_Ioi (fun t ht => by
    rw [rawMobiusNymanError_eq_harmonic_tail N ht]),
    integral_normSq_real_div (deningerHarmonicPartial N) (by positivity)]
  field_simp

/-- The squared error of the literal finite Fermi approximation. -/
def rawMobiusFermiErrorEnergy (N : ℕ) : ℝ :=
  ∫ t in Ioc (0 : ℝ) 1, ‖dyadicHaar t - rawMobiusFermiApprox N t‖ ^ 2

/-- All of the error energy is confined to the shrinking tail interval. -/
theorem rawMobiusFermiErrorEnergy_eq_tail (N : ℕ) :
    rawMobiusFermiErrorEnergy N =
      ∫ t in Ioc (0 : ℝ) (1 / ((N : ℝ) + 1)),
        ‖dyadicHaar t - rawMobiusFermiApprox N t‖ ^ 2 := by
  have hc0 : (0 : ℝ) ≤ 1 / ((N : ℝ) + 1) := by positivity
  have hc1 : 1 / ((N : ℝ) + 1) ≤ 1 :=
    (div_le_one (by positivity)).mpr (le_add_of_nonneg_left (Nat.cast_nonneg N))
  rw [rawMobiusFermiErrorEnergy, ← Ioc_union_Ioc_eq_Ioc hc0 hc1]
  apply integral_union_eq_left_of_forall measurableSet_Ioc
  intro t ht
  rw [rawMobiusFermiApprox_eq_dyadicHaar N ht.1 ht.2]
  simp

theorem integral_normSq_difference_rawMobiusNymanError (N : ℕ) :
    (∫ t in Ioi (0 : ℝ), ‖fermiDilationDifference (rawMobiusNymanError N) t‖ ^ 2) =
      rawMobiusFermiErrorEnergy N := by
  rw [← Ioc_union_Ioi_eq_Ioi (by norm_num : (0 : ℝ) ≤ 1),
    integral_union_eq_left_of_forall measurableSet_Ioi (fun t ht => ?_)]
  · exact setIntegral_congr_fun measurableSet_Ioc
      (fun t ht => congrArg (fun z : ℂ => ‖z‖ ^ 2) (dyadicHaar_sub_rawMobiusFermiApprox N ht).symm)
  · rw [fermiDilationDifference_rawMobiusNymanError_eq_zero N (lt_of_le_of_lt ?_ ht)]
    · simp
    · exact (div_le_one (by positivity : (0 : ℝ) < N + 1)).mpr
        (le_add_of_nonneg_left (Nat.cast_nonneg N))

/-- Quantitative continuous obstruction: the shrinking support does not erase harmonic energy. -/
theorem rawMobiusFermiErrorEnergy_lower_bound (N : ℕ) :
    (((N : ℝ) + 1) / 6) * deningerHarmonicPartial N ^ 2 ≤ rawMobiusFermiErrorEnergy N := by
  have htail : (∫ t in Ioi (1 / ((N : ℝ) + 1)), ‖rawMobiusNymanError N t‖ ^ 2) ≤
      ∫ t in Ioi (0 : ℝ), ‖rawMobiusNymanError N t‖ ^ 2 := by
    apply setIntegral_mono_set (integrableOn_normSq_rawMobiusNymanError N)
      (Filter.Eventually.of_forall (fun t => sq_nonneg _))
    exact Filter.Eventually.of_forall (fun t ht => lt_trans (by positivity) ht)
  rw [integral_normSq_rawMobiusNymanError_tail] at htail
  have hd := integral_normSq_le_six_fermiDilationDifference
    (measurable_rawMobiusNymanError N) (integrableOn_normSq_rawMobiusNymanError N)
  rw [integral_normSq_difference_rawMobiusNymanError] at hd
  nlinarith

/-- Unconditional positive survivor: one fixed Haar error floor recurs cofinally. -/
theorem frequent_rawMobiusFermiErrorEnergy_floor :
    ∃ epsilon : ℝ, 0 < epsilon ∧ ∀ N₀ : ℕ, ∃ N : ℕ,
      N₀ ≤ N ∧ epsilon ≤ rawMobiusFermiErrorEnergy N := by
  obtain ⟨epsilon, hepsilon, hfreq⟩ := frequent_harmonic_energy_floor
  refine ⟨epsilon / 6, by positivity, ?_⟩
  intro N₀
  obtain ⟨N, hN, hfloor⟩ := hfreq N₀
  refine ⟨N, hN, ?_⟩
  have h := rawMobiusFermiErrorEnergy_lower_bound N
  nlinarith [sq_nonneg (deningerHarmonicPartial N)]

/-- Raw Möbius coefficients do not approximate the Haar target in the literal PM norm. -/
theorem not_tendsto_rawMobiusFermiErrorEnergy_zero :
    ¬ Tendsto rawMobiusFermiErrorEnergy atTop (𝓝 0) := by
  intro h
  obtain ⟨epsilon, hepsilon, hfreq⟩ := frequent_rawMobiusFermiErrorEnergy_floor
  obtain ⟨N₀, hN₀⟩ := Metric.tendsto_atTop.mp h epsilon hepsilon
  obtain ⟨N, hN, hfloor⟩ := hfreq N₀
  have hdist := hN₀ N hN
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (le_trans hepsilon.le hfloor)] at hdist
  exact (not_lt_of_ge hfloor) hdist


end RHTower
