import GaloisForLFunctions.RHTower.BurnolCoPoissonGeneralSeedMellin
import GaloisForLFunctions.RHTower.BurnolCoPoissonWindowIndicator

/-!
# The reflected Burnol source

The co-Poisson reciprocal of the fixed sub-window `[1/2,1]` is the indicator of `[1,2]`, so the
reflected orientation of the fixed prime-two source is the co-Poisson right sum

`f₀^∨(t) = ∑_{t/2 ≤ k ≤ t} 1/k - log 2`.

Below the aperture the window sum is empty, so the reflected source has the constant head `-log 2`.
Comparing the harmonic window with `∫_{t/2}^t dx/x = log 2` through the elementary telescoping
bounds `log(1 + 1/k) ≤ 1/k ≤ log(k/(k-1))` gives the decay `|f₀^∨(t)| ≤ 4/t`, which is exactly what
makes the Mellin integral converge on the whole critical strip.
-/

open Complex Real MeasureTheory Set Filter Topology Finset

noncomputable section

namespace RHTower

/-- The reflected (co-Poisson reciprocal) Burnol source. -/
def burnolReflectedRawSource : ℝ → ℂ :=
  burnolCoPoissonRightSum (coPoissonWindowIndicatorSeed 1 2)

theorem burnolReflectedSeedSupport :
    Function.support (coPoissonWindowIndicatorSeed 1 2) ⊆ Icc (1 / 2 : ℝ) (1 / 2 : ℝ)⁻¹ := by
  refine subset_trans (support_coPoissonWindowIndicatorSeed 1 2) ?_
  intro x hx
  refine ⟨by linarith [hx.1], ?_⟩
  rw [show ((1 / 2 : ℝ))⁻¹ = 2 by norm_num]
  exact hx.2

theorem burnolReflectedCorrection :
    coPoissonCorrectionConstant (coPoissonWindowIndicatorSeed 1 2) = ((Real.log 2 : ℝ) : ℂ) := by
  rw [coPoissonCorrectionConstant_coPoissonWindowIndicatorSeed (by norm_num) (by norm_num),
    Real.log_one, sub_zero]

/-- **The reflected head.**  Below the aperture the window sum is empty. -/
theorem burnolReflectedRawSource_head {t : ℝ} (ht : |t| < 1) :
    burnolReflectedRawSource t = -((Real.log 2 : ℝ) : ℂ) := by
  rw [burnolReflectedRawSource, burnolCoPoissonRightSum_eq_sub_correction,
    burnolReflectedCorrection]
  have hzero : ∀ n : ℕ, (((n + 1 : ℕ) : ℝ) : ℂ)⁻¹ *
      coPoissonWindowIndicatorSeed 1 2 (|t| / ((n + 1 : ℕ) : ℝ)) = 0 := by
    intro n
    have h1 : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
    have hlt : |t| / ((n + 1 : ℕ) : ℝ) < 1 := by
      refine lt_of_le_of_lt ?_ ht
      rw [div_le_iff₀ (by linarith)]
      nlinarith [abs_nonneg t, h1]
    rw [coPoissonWindowIndicatorSeed_of_notMem (fun hc => absurd hc.1 (not_le.mpr hlt)), mul_zero]
  rw [tsum_congr hzero, tsum_zero, zero_sub]

/-- The window sum collapses to the harmonic block `⌈t/2⌉ ≤ k ≤ ⌊t⌋`. -/
theorem burnolReflectedWindow_sum {t : ℝ} (ht : 0 < t) {N : ℕ} (hN : ⌊t⌋₊ ≤ N) :
    (∑ k ∈ Finset.Icc 1 N,
        (((k : ℕ) : ℝ) : ℂ)⁻¹ * coPoissonWindowIndicatorSeed 1 2 (t / ((k : ℕ) : ℝ))) =
      (((∑ k ∈ Finset.Icc ⌈t / 2⌉₊ ⌊t⌋₊, (1 : ℝ) / (k : ℝ)) : ℝ) : ℂ) := by
  have hceilpos : 1 ≤ ⌈t / 2⌉₊ := Nat.one_le_ceil_iff.mpr (by positivity)
  have hsub : Finset.Icc ⌈t / 2⌉₊ ⌊t⌋₊ ⊆ Finset.Icc 1 N := by
    intro k hk
    obtain ⟨hk1, hk2⟩ := Finset.mem_Icc.mp hk
    exact Finset.mem_Icc.mpr ⟨le_trans hceilpos hk1, le_trans hk2 hN⟩
  have hzero : ∀ k ∈ Finset.Icc 1 N, k ∉ Finset.Icc ⌈t / 2⌉₊ ⌊t⌋₊ →
      (((k : ℕ) : ℝ) : ℂ)⁻¹ * coPoissonWindowIndicatorSeed 1 2 (t / ((k : ℕ) : ℝ)) = 0 := by
    intro k hk hknot
    obtain ⟨hk1, -⟩ := Finset.mem_Icc.mp hk
    have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk1
    have hnotmem : t / (k : ℝ) ∉ Icc (1 : ℝ) 2 := by
      intro hc
      obtain ⟨hc1, hc2⟩ := hc
      refine hknot (Finset.mem_Icc.mpr ⟨?_, ?_⟩)
      · refine Nat.ceil_le.mpr ?_
        rw [div_le_iff₀ hkR] at hc2
        linarith
      · refine Nat.le_floor ?_
        rw [le_div_iff₀ hkR, one_mul] at hc1
        exact hc1
    rw [coPoissonWindowIndicatorSeed_of_notMem hnotmem, mul_zero]
  rw [← Finset.sum_subset hsub hzero]
  push_cast
  refine Finset.sum_congr rfl fun k hk => ?_
  obtain ⟨hk1, hk2⟩ := Finset.mem_Icc.mp hk
  have hkpos : 1 ≤ k := le_trans hceilpos hk1
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hkpos
  have hmem : t / (k : ℝ) ∈ Icc (1 : ℝ) 2 := by
    refine ⟨?_, ?_⟩
    · rw [le_div_iff₀ hkR, one_mul]
      exact (Nat.le_floor_iff ht.le).mp hk2
    · rw [div_le_iff₀ hkR]
      have := Nat.ceil_le.mp hk1
      linarith
  rw [coPoissonWindowIndicatorSeed_of_mem hmem, mul_one, one_div]

/-- **The reflected source is a harmonic window minus `log 2`.** -/
theorem burnolReflectedRawSource_eq_harmonic {t : ℝ} (ht : 0 < t) :
    burnolReflectedRawSource t =
      (((∑ k ∈ Finset.Icc ⌈t / 2⌉₊ ⌊t⌋₊, (1 : ℝ) / (k : ℝ)) - Real.log 2 : ℝ) : ℂ) := by
  rw [burnolReflectedRawSource, burnolCoPoissonRightSum_eq_sub_correction,
    burnolReflectedCorrection, abs_of_pos ht,
    coPoissonSum_eq_fixed_finset_sum (b := 1 / 2) (by norm_num) burnolReflectedSeedSupport ht
      le_rfl,
    burnolReflectedWindow_sum ht (by
      refine Nat.floor_le_floor ?_
      rw [le_div_iff₀ (by norm_num : (0:ℝ) < 1 / 2)]
      linarith)]
  push_cast
  ring

/-! ## The harmonic window and its decay -/

/-- The harmonic block of the reflected source. -/
def burnolHarmonicWindow (t : ℝ) : ℝ := ∑ k ∈ Finset.Icc ⌈t / 2⌉₊ ⌊t⌋₊, (1 : ℝ) / (k : ℝ)

theorem burnolHarmonicSum_Icc (n : ℕ) :
    ((harmonic n : ℚ) : ℝ) = ∑ k ∈ Finset.Icc 1 n, (1 : ℝ) / (k : ℝ) := by
  rw [harmonic_eq_sum_Icc]
  push_cast
  exact Finset.sum_congr rfl fun k _ => (one_div (k : ℝ)).symm

theorem burnolHarmonicWindow_eq_sub {a b : ℕ} (ha : 1 ≤ a) (hab : a ≤ b + 1) :
    (∑ k ∈ Finset.Icc a b, (1 : ℝ) / (k : ℝ)) =
      ((harmonic b : ℚ) : ℝ) - ((harmonic (a - 1) : ℚ) : ℝ) := by
  have hIcc : Finset.Icc a b = Finset.Ico a (b + 1) := (Finset.Ico_add_one_right_eq_Icc a b).symm
  have hlow : Finset.Icc 1 (a - 1) = Finset.Ico 1 a := by
    rw [← Finset.Ico_add_one_right_eq_Icc]
    congr 1
    omega
  have hhigh : Finset.Icc 1 b = Finset.Ico 1 (b + 1) :=
    (Finset.Ico_add_one_right_eq_Icc 1 b).symm
  have hsplit := Finset.sum_Ico_consecutive (fun k : ℕ => (1 : ℝ) / (k : ℝ)) ha hab
  rw [burnolHarmonicSum_Icc, burnolHarmonicSum_Icc, hlow, hhigh, hIcc, ← hsplit]
  ring

/-- Two-sided Euler--Mascheroni gap. -/
theorem burnolEulerGap {n : ℕ} (hn : 1 ≤ n) :
    0 ≤ ((harmonic n : ℚ) : ℝ) - Real.log n - Real.eulerMascheroniConstant ∧
      ((harmonic n : ℚ) : ℝ) - Real.log n - Real.eulerMascheroniConstant ≤ 1 / (n : ℝ) := by
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hlo := Real.eulerMascheroniConstant_lt_eulerMascheroniSeq' n
  have hhi := Real.eulerMascheroniSeq_lt_eulerMascheroniConstant n
  rw [Real.eulerMascheroniSeq'] at hlo
  rw [if_neg (by omega : ¬ n = 0)] at hlo
  rw [Real.eulerMascheroniSeq] at hhi
  constructor
  · linarith
  · have hlog : Real.log ((n : ℝ) + 1) - Real.log (n : ℝ) ≤ 1 / (n : ℝ) := by
      rw [← Real.log_div (by linarith) (ne_of_gt hnR)]
      have hval : ((n : ℝ) + 1) / (n : ℝ) = 1 + 1 / (n : ℝ) := by field_simp
      rw [hval]
      have := Real.log_le_sub_one_of_pos (x := 1 + 1 / (n : ℝ)) (by positivity)
      linarith
    linarith

/-- **The reflected harmonic window is `log 2 + O(1/t)`.** -/
theorem abs_burnolHarmonicWindow_sub_log_two_le {t : ℝ} (ht : 8 ≤ t) :
    |burnolHarmonicWindow t - Real.log 2| ≤ 8 / t := by
  have htpos : (0 : ℝ) < t := by linarith
  set b : ℕ := ⌊t⌋₊ with hb
  set a : ℕ := ⌈t / 2⌉₊ with ha
  have hbR : (b : ℝ) ≤ t := Nat.floor_le htpos.le
  have hbR' : t - 1 < (b : ℝ) := by
    have := Nat.lt_floor_add_one t
    linarith [Nat.lt_succ_floor t]
  have haR : t / 2 ≤ (a : ℝ) := Nat.le_ceil _
  have haR' : (a : ℝ) < t / 2 + 1 := Nat.ceil_lt_add_one (by linarith)
  have hb7 : 7 ≤ b := by
    have : (7 : ℝ) ≤ (b : ℝ) := by linarith
    exact_mod_cast this
  have ha4 : 4 ≤ a := by
    have : (4 : ℝ) ≤ (a : ℝ) := by linarith
    exact_mod_cast this
  have hab : a ≤ b + 1 := by
    have hle : (a : ℝ) ≤ (b : ℝ) + 1 := by linarith
    exact_mod_cast hle
  have hwin : burnolHarmonicWindow t =
      ((harmonic b : ℚ) : ℝ) - ((harmonic (a - 1) : ℚ) : ℝ) :=
    burnolHarmonicWindow_eq_sub (by omega) hab
  have hbpos : (0 : ℝ) < (b : ℝ) := by linarith
  have ha1R : (0 : ℝ) < (a : ℝ) - 1 := by
    have : (4 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha4
    linarith
  have hcast : ((a - 1 : ℕ) : ℝ) = (a : ℝ) - 1 := by
    have h1 : (1 : ℕ) ≤ a := by omega
    rw [Nat.cast_sub h1]
    norm_num
  obtain ⟨hbg0, hbg1⟩ := burnolEulerGap (n := b) (by omega)
  obtain ⟨hag0, hag1⟩ := burnolEulerGap (n := a - 1) (by omega)
  rw [hcast] at hag0 hag1
  have hlogdiff : Real.log (b : ℝ) - Real.log ((a : ℝ) - 1) - Real.log 2 =
      Real.log ((b : ℝ) / (2 * ((a : ℝ) - 1))) := by
    rw [Real.log_div hbpos.ne' (by positivity), Real.log_mul (by norm_num) (by linarith)]
    ring
  have hypos : (0 : ℝ) < (b : ℝ) / (2 * ((a : ℝ) - 1)) := by positivity
  have hupper : Real.log ((b : ℝ) / (2 * ((a : ℝ) - 1))) ≤ 4 / t := by
    refine le_trans (Real.log_le_sub_one_of_pos hypos) ?_
    rw [div_sub_one (by positivity), div_le_div_iff₀ (by positivity) htpos]
    nlinarith [hbR, haR, htpos]
  have hlower : -(2 / t) ≤ Real.log ((b : ℝ) / (2 * ((a : ℝ) - 1))) := by
    have hinv : Real.log ((2 * ((a : ℝ) - 1)) / (b : ℝ)) ≤ 2 / t := by
      refine le_trans (Real.log_le_sub_one_of_pos (by positivity)) ?_
      rw [div_sub_one hbpos.ne', div_le_div_iff₀ hbpos htpos]
      nlinarith [hbR', haR', htpos]
    rw [Real.log_div (by positivity) hbpos.ne'] at hinv
    rw [Real.log_div hbpos.ne' (by positivity)]
    linarith
  have hbinv : 1 / (b : ℝ) ≤ 2 / t := by
    rw [div_le_div_iff₀ hbpos htpos]
    linarith
  have hainv : 1 / ((a : ℝ) - 1) ≤ 4 / t := by
    rw [div_le_div_iff₀ (by linarith) htpos]
    linarith
  have hkey : ((harmonic b : ℚ) : ℝ) - ((harmonic (a - 1) : ℚ) : ℝ) - Real.log 2 =
      (((harmonic b : ℚ) : ℝ) - Real.log (b : ℝ) - Real.eulerMascheroniConstant) -
        (((harmonic (a - 1) : ℚ) : ℝ) - Real.log ((a : ℝ) - 1) -
          Real.eulerMascheroniConstant) +
        Real.log ((b : ℝ) / (2 * ((a : ℝ) - 1))) := by
    rw [← hlogdiff]
    ring
  have htinv : (0 : ℝ) < 1 / t := by positivity
  have hscale : ∀ c : ℝ, c / t = c * (1 / t) := fun c => by ring
  rw [hwin, hkey, abs_le, hscale 8]
  rw [hscale 4] at hupper hainv
  rw [hscale 2] at hlower hbinv
  constructor
  · linarith
  · linarith

/-- **The reflected source decays like `1/t`.** -/
theorem norm_burnolReflectedRawSource_le {t : ℝ} (ht : 8 ≤ t) :
    ‖burnolReflectedRawSource t‖ ≤ 8 / t := by
  have htpos : (0 : ℝ) < t := by linarith
  rw [burnolReflectedRawSource_eq_harmonic htpos, Complex.norm_real, Real.norm_eq_abs]
  exact abs_burnolHarmonicWindow_sub_log_two_le ht

/-! ## Global bound, measurability and the Mellin transform -/

theorem norm_burnolReflectedRawSource_le_nine {t : ℝ} (ht : 0 < t) (ht8 : t ≤ 8) :
    ‖burnolReflectedRawSource t‖ ≤ 9 := by
  have hlog2 : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hlog2' : Real.log 2 ≤ 1 := by
    have := Real.log_two_lt_d9
    linarith
  rcases lt_or_ge t 1 with h | h
  · rw [burnolReflectedRawSource_head (by rw [abs_of_pos ht]; exact h), norm_neg,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hlog2]
    linarith
  · rw [burnolReflectedRawSource_eq_harmonic ht, Complex.norm_real, Real.norm_eq_abs]
    have hceilpos : 1 ≤ ⌈t / 2⌉₊ := Nat.one_le_ceil_iff.mpr (by positivity)
    have hwin0 : 0 ≤ burnolHarmonicWindow t :=
      Finset.sum_nonneg fun k _ => by positivity
    have hcard : (Finset.Icc ⌈t / 2⌉₊ ⌊t⌋₊).card ≤ 8 := by
      rw [Nat.card_Icc]
      have hfl : ⌊t⌋₊ ≤ 8 := Nat.floor_le_of_le ht8
      omega
    have hterm : ∀ k ∈ Finset.Icc ⌈t / 2⌉₊ ⌊t⌋₊, (1 : ℝ) / (k : ℝ) ≤ 1 := by
      intro k hk
      obtain ⟨hk1, -⟩ := Finset.mem_Icc.mp hk
      have hk1' : 1 ≤ k := le_trans hceilpos hk1
      have hkR : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1'
      rw [div_le_one (by linarith)]
      linarith
    have hsum := Finset.sum_le_card_nsmul _ _ (1 : ℝ) hterm
    rw [nsmul_eq_mul, mul_one] at hsum
    have hcardR : ((Finset.Icc ⌈t / 2⌉₊ ⌊t⌋₊).card : ℝ) ≤ 8 := by exact_mod_cast hcard
    have hwin8 : burnolHarmonicWindow t ≤ 8 := le_trans hsum hcardR
    show |burnolHarmonicWindow t - Real.log 2| ≤ 9
    rw [abs_le]
    constructor <;> linarith

theorem measurable_burnolReflectedRawSource : Measurable burnolReflectedRawSource :=
  measurable_burnolCoPoissonRightSum_coPoissonWindowIndicatorSeed (by norm_num) (by norm_num)

theorem integrableOn_burnolReflectedRawSource_cpow {w : ℂ} (hw0 : 0 < w.re) (hw1 : w.re < 1) :
    IntegrableOn (fun t : ℝ => burnolReflectedRawSource t * ((t : ℝ) : ℂ) ^ (-w))
      (Ioi (0 : ℝ)) := by
  have hmeas : AEStronglyMeasurable
      (fun t : ℝ => burnolReflectedRawSource t * ((t : ℝ) : ℂ) ^ (-w)) volume :=
    (measurable_burnolReflectedRawSource.mul
      ((Complex.measurable_ofReal.pow_const _).comp measurable_id)).aestronglyMeasurable
  have hnear : IntegrableOn
      (fun t : ℝ => burnolReflectedRawSource t * ((t : ℝ) : ℂ) ^ (-w)) (Ioc (0 : ℝ) 8) := by
    refine MeasureTheory.Integrable.mono' (g := fun t : ℝ => 9 * t ^ (-w.re))
      (((intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := 8) (r := -w.re)
        (by linarith)).1).const_mul 9) hmeas.restrict ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht.1, Complex.neg_re]
    have hb := norm_burnolReflectedRawSource_le_nine ht.1 ht.2
    have hp : (0 : ℝ) < t ^ (-w.re) := Real.rpow_pos_of_pos ht.1 _
    nlinarith [hb, hp, norm_nonneg (burnolReflectedRawSource t)]
  have hfar : IntegrableOn
      (fun t : ℝ => burnolReflectedRawSource t * ((t : ℝ) : ℂ) ^ (-w)) (Ioi (8 : ℝ)) := by
    refine MeasureTheory.Integrable.mono' (g := fun t : ℝ => 8 * t ^ (-w.re - 1))
      ((integrableOn_Ioi_rpow_of_lt (a := -w.re - 1) (by linarith) (by norm_num)).const_mul 8)
      hmeas.restrict ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : (0 : ℝ) < t := lt_trans (by norm_num) ht
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht0, Complex.neg_re]
    have hb := norm_burnolReflectedRawSource_le (le_of_lt ht)
    have hp : (0 : ℝ) < t ^ (-w.re) := Real.rpow_pos_of_pos ht0 _
    have hsplit : t ^ (-w.re - 1) = t ^ (-w.re) / t := by
      rw [Real.rpow_sub ht0, Real.rpow_one]
    refine le_trans (mul_le_mul_of_nonneg_right hb hp.le) (le_of_eq ?_)
    rw [hsplit]
    field_simp
  have hunion : Ioc (0 : ℝ) 8 ∪ Ioi 8 = Ioi (0 : ℝ) := Ioc_union_Ioi_eq_Ioi (by norm_num)
  rw [← hunion]
  exact hnear.union hfar

/-- **The Mellin transform of the reflected source.** -/
theorem integral_burnolReflectedRawSource_cpow {w : ℂ} (hw0 : 0 < w.re) (hw1 : w.re < 1) :
    (∫ t in Ioi (0 : ℝ), burnolReflectedRawSource t * ((t : ℝ) : ℂ) ^ (-w)) =
      riemannZeta w * ((2 : ℂ) ^ (1 - w) - 1) / (1 - w) := by
  have hmain := integral_Ioi_burnolCoPoisson_cpow (b := 1 / 2) (by norm_num)
    (integrable_coPoissonWindowIndicatorSeed 1 2) burnolReflectedSeedSupport hw0 hw1
    (integrableOn_burnolReflectedRawSource_cpow hw0 hw1)
  have hseed : (∫ u in Ioi (0 : ℝ),
      coPoissonWindowIndicatorSeed 1 2 u * ((u : ℝ) : ℂ) ^ (-w)) =
      ((2 : ℂ) ^ (1 - w) - 1) / (1 - w) := by
    have hpt : ∀ u : ℝ, coPoissonWindowIndicatorSeed 1 2 u * ((u : ℝ) : ℂ) ^ (-w) =
        Set.indicator (Icc (1 : ℝ) 2) (fun v : ℝ => ((v : ℝ) : ℂ) ^ (-w)) u := by
      intro u
      by_cases hu : u ∈ Icc (1 : ℝ) 2
      · rw [coPoissonWindowIndicatorSeed_of_mem hu, Set.indicator_of_mem hu, one_mul]
      · rw [coPoissonWindowIndicatorSeed_of_notMem hu, Set.indicator_of_notMem hu, zero_mul]
    have hinter : Ioi (0 : ℝ) ∩ Icc (1 : ℝ) 2 = Icc (1 : ℝ) 2 := by
      refine Set.inter_eq_right.mpr fun x hx => ?_
      exact mem_Ioi.mpr (by linarith [hx.1])
    rw [setIntegral_congr_fun measurableSet_Ioi (fun u _ => hpt u),
      MeasureTheory.setIntegral_indicator measurableSet_Icc, hinter,
      MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by norm_num : (1 : ℝ) ≤ 2),
      integral_cpow (Or.inl (by rw [Complex.neg_re]; linarith))]
    have hexp : (-w + 1 : ℂ) = 1 - w := by ring
    rw [hexp, Complex.ofReal_one, Complex.one_cpow, Complex.ofReal_ofNat]
  rw [burnolReflectedRawSource, hmain, hseed]
  ring

end RHTower
