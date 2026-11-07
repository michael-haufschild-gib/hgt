import GaloisForLFunctions.SquareRootThreshold.EffectiveHorizons.HausdorffShifts
import GaloisForLFunctions.SquareRootThreshold.EffectiveHorizons.TheZeroMassHasItsSecondTerm

/-!
# Hausdorff shifts from the sharp zero mass

**Theorem** (`scaledHausdorffMomentDifference_nonneg_of_sharp_shift_le`). The calibrated Hausdorff row
of order `k` is nonnegative from the shift `⌈20K⌉ + ⌈K H²⌉ + 1`, with `K = 10(k+1) + 20` and
`H = max(e¹², 42(k+1) + 44K)`.

The atom estimates need two zero counts at the height `T`: at most `0.33 T log T` copies of ordinate
at most `T`, and at least `0.04 T log T` copies in the band `(6T/5, 7T/5]`. The sharp mass
`|M(T) − (T/π)(log T − log 2π − 1)| ≤ 80 + 65 log T` gives both from `T = e¹²`, in place of the
relative error `1/500`, which needs `log T` of size several hundred.
-/

open Complex Filter Topology

noncomputable section
namespace RHTower

private theorem exp_twelve_ge' : (162754 : ℝ) ≤ Real.exp 12 := by
  have h2 : Real.exp 12 = Real.exp 1 ^ 12 := by
    rw [← Real.exp_nat_mul]
    norm_num
  rw [h2]
  calc (162754 : ℝ) ≤ (2.7182818283 : ℝ) ^ 12 := by norm_num
    _ ≤ _ := pow_le_pow_left₀ (by norm_num) Real.exp_one_gt_d9.le 12

private theorem massKappa_le : massKappa ≤ 2849 / 1000 := by
  unfold massKappa
  have hl2 := Real.log_two_lt_d9
  have h1 := Real.log_le_sub_one_of_pos
    (show 0 < Real.pi / Real.exp 1 by have := Real.pi_pos; positivity)
  rw [Real.log_div Real.pi_pos.ne' (Real.exp_pos 1).ne', Real.log_exp] at h1
  have h2 : Real.pi / Real.exp 1 ≤ 11558 / 10000 := by
    rw [div_le_iff₀ (Real.exp_pos 1)]
    linarith only [Real.exp_one_gt_d9, Real.pi_lt_d4]
  norm_num at hl2
  linarith only [hl2, h1, h2]

/-- **The band `(6T/5, 7T/5]` carries at least `0.04 T log T` copies from `e¹²`.** -/
theorem band_card_ge_of_exp_twelve_le {T : ℝ} (hT : Real.exp 12 ≤ T) :
    4 / 100 * (T * Real.log T) ≤ ((xiCopiesBand (6 / 5 * T) (7 / 5 * T)).card : ℝ) := by
  have hE := exp_twelve_ge'
  have hT1 : (162754 : ℝ) ≤ T := hE.trans hT
  have hT0 : 0 < T := by linarith only [hT1]
  have hL : 12 ≤ Real.log T := (Real.le_log_iff_exp_le hT0).mpr hT
  have hLu : Real.log T ≤ 11 + T / 162754 := by
    have h1 := Real.log_le_sub_one_of_pos (show 0 < T / Real.exp 12 by positivity)
    rw [Real.log_div hT0.ne' (Real.exp_pos 12).ne', Real.log_exp] at h1
    have h2 : T / Real.exp 12 ≤ T / 162754 := div_le_div_of_nonneg_left hT0.le (by norm_num) hE
    linarith only [h1, h2]
  rw [card_xiCopiesBand_eq_real (by positivity) (by linarith only [hT0])]
  have h7 := (abs_le.mp (abs_xiSymmetricMass_sub_sharp_le (T := 7 / 5 * T)
    (by linarith only [hT1]))).1
  have h6 := (abs_le.mp (abs_xiSymmetricMass_sub_sharp_le (T := 6 / 5 * T)
    (by linarith only [hT1]))).2
  rw [Real.log_mul (by norm_num) hT0.ne'] at h7 h6
  have hl7 : 0 ≤ Real.log (7 / 5 : ℝ) := Real.log_nonneg (by norm_num)
  have hl6 : Real.log (6 / 5 : ℝ) ≤ 1 / 5 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 6 / 5 by norm_num)
    linarith only [this]
  have hl6' : 0 ≤ Real.log (6 / 5 : ℝ) := Real.log_nonneg (by norm_num)
  have hκ := massKappa_le
  have hP : 318 / 1000 ≤ 1 / Real.pi := by
    rw [le_div_iff₀ Real.pi_pos]
    linarith only [Real.pi_lt_d4]
  -- The main term of the band.
  have hmain : 1 / Real.pi * (7 / 5 * T * (Real.log (7 / 5) + Real.log T - massKappa)) -
      1 / Real.pi * (6 / 5 * T * (Real.log (6 / 5) + Real.log T - massKappa)) ≥
      318 / 1000 * (T * (Real.log T / 5 - 8098 / 10000)) := by
    have e : 1 / Real.pi * (7 / 5 * T * (Real.log (7 / 5) + Real.log T - massKappa)) -
        1 / Real.pi * (6 / 5 * T * (Real.log (6 / 5) + Real.log T - massKappa)) =
        1 / Real.pi * (T * (Real.log T / 5 - massKappa / 5 + 7 / 5 * Real.log (7 / 5) -
          6 / 5 * Real.log (6 / 5))) := by ring
    rw [e]
    have hb : Real.log T / 5 - 8098 / 10000 ≤ Real.log T / 5 - massKappa / 5 +
        7 / 5 * Real.log (7 / 5) - 6 / 5 * Real.log (6 / 5) := by
      linarith only [hκ, hl7, hl6]
    have hb0 : 0 ≤ Real.log T / 5 - 8098 / 10000 := by linarith only [hL]
    have h1 : T * (Real.log T / 5 - 8098 / 10000) ≤ T * (Real.log T / 5 - massKappa / 5 +
        7 / 5 * Real.log (7 / 5) - 6 / 5 * Real.log (6 / 5)) :=
      mul_le_mul_of_nonneg_left hb hT0.le
    have h2 := mul_le_mul hP h1 (by positivity) (by positivity)
    linarith only [h2]
  have hlog7 : Real.log (7 / 5 : ℝ) ≤ 2 / 5 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 7 / 5 by norm_num)
    linarith only [this]
  have hTL : 12 * T ≤ T * Real.log T := by nlinarith only [mul_le_mul_of_nonneg_left hL hT0.le]
  nlinarith only [h7, h6, hmain, hLu, hTL, hlog7, hl6, hT1]

/-- A closed-form shift from the sharp mass, after which the calibrated Hausdorff row is
nonnegative. -/
def sharpPrimeArchHausdorffShift (k : ℕ) : ℕ :=
  let K : ℝ := 10 * ((k + 1 : ℕ) : ℝ) + 20
  let H : ℝ := max (Real.exp 12) (42 * ((k + 1 : ℕ) : ℝ) + 44 * K)
  ⌈20 * K⌉₊ + ⌈K * H ^ 2⌉₊ + 1

/-- **Every Hausdorff row is nonnegative after its sharp shift.** -/
theorem scaledHausdorffMomentDifference_nonneg_of_sharp_shift_le (k r : ℕ)
    (hr : sharpPrimeArchHausdorffShift k ≤ r) :
    0 ≤ scaledHausdorffMomentDifference primeArchEndpointHausdorffRadius
      normalizedPrimeArchMoment k r := by
  classical
  have hR : 0 < primeArchEndpointHausdorffRadius := primeArchEndpointHausdorffRadius_pos
  set K : ℝ := 10 * ((k + 1 : ℕ) : ℝ) + 20 with hK_def
  have hk0 : (0 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by positivity
  have hK1 : 1 ≤ K := by rw [hK_def]; linarith
  have hK10 : 10 * ((k + 1 : ℕ) : ℝ) ≤ K := by rw [hK_def]; linarith
  have hE := exp_twelve_ge'
  set Tstar : ℝ := max (Real.exp 12) (42 * ((k + 1 : ℕ) : ℝ) + 44 * K) with hTstar_def
  have hTstar0 : 0 ≤ Tstar := le_trans (Real.exp_pos 12).le (le_max_left _ _)
  change ⌈20 * K⌉₊ + ⌈K * Tstar ^ 2⌉₊ + 1 ≤ r at hr
  have hr' : ((⌈20 * K⌉₊ + ⌈K * Tstar ^ 2⌉₊ + 1 : ℕ) : ℝ) ≤ r := by
    exact_mod_cast hr
  push_cast at hr'
  have hc1 := Nat.le_ceil (20 * K)
  have hc2 := Nat.le_ceil (K * Tstar ^ 2)
  have hc1' : (0 : ℝ) ≤ (⌈20 * K⌉₊ : ℝ) := by positivity
  have hc2' : (0 : ℝ) ≤ (⌈K * Tstar ^ 2⌉₊ : ℝ) := by positivity
  have hr20 : 20 * K ≤ (r : ℝ) := by linarith
  have hR1 : primeArchEndpointHausdorffRadius ≤ 1 :=
    primeArchEndpointHausdorffRadius_lt_one.le
  have hRT : K * primeArchEndpointHausdorffRadius * Tstar ^ 2 ≤ K * Tstar ^ 2 := by
    have hKR1 := mul_le_mul_of_nonneg_left hR1 (by linarith : 0 ≤ K)
    simpa only [mul_one] using mul_le_mul_of_nonneg_right hKR1 (sq_nonneg Tstar)
  have hrT : K * primeArchEndpointHausdorffRadius * Tstar ^ 2 < (r : ℝ) := by linarith
  have hKR : 0 < K * primeArchEndpointHausdorffRadius := by positivity
  set T : ℝ := Real.sqrt ((r : ℝ) / (K * primeArchEndpointHausdorffRadius)) with hT_def
  have hT2 : T ^ 2 = r / (K * primeArchEndpointHausdorffRadius) := Real.sq_sqrt (by
    have : 0 < (r : ℝ) := by linarith
    positivity)
  have hTpos : 0 < T := Real.sqrt_pos.mpr (by
    have : 0 < (r : ℝ) := by linarith
    positivity)
  have hΛ : K * primeArchEndpointHausdorffRadius / r = 1 / T ^ 2 := by
    rw [hT2]
    field_simp
  have hTstar : Tstar ≤ T := by
    rw [hT_def, ← Real.sqrt_sq hTstar0]
    apply Real.sqrt_le_sqrt
    rw [le_div_iff₀ hKR]
    linarith
  have hTE : Real.exp 12 ≤ T := le_trans (le_max_left _ _) hTstar
  have hT500 : 500 ≤ T := by linarith
  have hT10 : 10 ≤ T := by linarith
  have hTK : 42 * ((k + 1 : ℕ) : ℝ) + 44 * K ≤ T := le_trans (le_max_right _ _) hTstar
  rw [scaledHausdorffMomentDifference_eq_re_xiCentralSum]
  have hsum : Summable (fun q => hausdorffAtomTerm primeArchEndpointHausdorffRadius k r q) :=
    summable_xiCentralScaledHausdorffTerm primeArchEndpointHausdorffRadius k r
  have hfsum : Summable (fun q => (hausdorffAtomTerm primeArchEndpointHausdorffRadius k r q).re) :=
    ⟨_, Complex.hasSum_re hsum.hasSum⟩
  change 0 ≤ (∑' q, hausdorffAtomTerm primeArchEndpointHausdorffRadius k r q).re
  rw [Complex.re_tsum hsum]
  set B : Finset XiZeroCopy :=
    (xiCopiesBand 0 T).filter (fun q => 1 / T ^ 2 < xiThermalNode q) with hB_def
  set A : Finset XiZeroCopy := xiCopiesBand (6 / 5 * T) (7 / 5 * T) with hA_def
  have hmemB : ∀ q, 1 / T ^ 2 < xiThermalNode q → q ∈ B := by
    intro q hq
    rw [hB_def, Finset.mem_filter, mem_xiCopiesBand]
    exact ⟨⟨abs_pos.mpr (xiSupport_im_ne_zero q.1),
      (abs_ordinate_lt_of_inv_sq_lt_xiThermalNode hTpos hq).le⟩, hq⟩
  have hB_node : ∀ q ∈ B, 1 / T ^ 2 < xiThermalNode q := fun q hq =>
    (Finset.mem_filter.mp hq).2
  have hB_ord : ∀ q ∈ B, |(q.1 : ℂ).im| ≤ T := fun q hq =>
    (mem_xiCopiesBand.mp (Finset.mem_filter.mp hq).1).2
  have hA_node : ∀ q ∈ A, xiThermalNode q ≤ 1 / T ^ 2 := by
    intro q hq
    rw [hA_def, mem_xiCopiesBand] at hq
    have h := (xiThermalNode_mem_of_ordinate_band hT10 hq.1 hq.2).2
    exact h.trans (div_le_div_of_nonneg_right (by norm_num) (by positivity))
  have hdisj : Disjoint B A := by
    rw [Finset.disjoint_left]
    intro q hqB hqA
    exact absurd (hA_node q hqA) (not_le.mpr (hB_node q hqB))
  set α : ℝ := 1 / 2 * (49 / 100 * (1 / T ^ 2)) ^ (k + 1) *
    primeArchEndpointHausdorffRadius ^ r * Real.exp (-(3 / 4 * K)) with hα
  set β : ℝ := (41 / 10 * (1 / T ^ 2)) ^ (k + 1) * primeArchEndpointHausdorffRadius ^ r *
    Real.exp (-(99 / 100 * K)) with hβ
  have hα0 : 0 ≤ α := by positivity
  have hβ0 : 0 ≤ β := by positivity
  have hA_term : ∀ q ∈ A, α ≤ (hausdorffAtomTerm primeArchEndpointHausdorffRadius k r q).re := by
    intro q hq
    rw [hA_def, mem_xiCopiesBand] at hq
    exact band_re_hausdorffAtomTerm_ge k r hR hK1 hr20 hT10 hTK hΛ hq.1 hq.2
  have hB_term : ∀ q ∈ B, -β ≤ (hausdorffAtomTerm primeArchEndpointHausdorffRadius k r q).re := by
    intro q hq
    have h := norm_hausdorffAtomTerm_le_of_threshold_lt k r hR hK10 hK1 hr20 hT500 hΛ
      (xiThermalNode_le_primeArchEndpointHausdorffRadius q) (hB_node q hq)
    have h2 := neg_norm_le_re' (hausdorffAtomTerm primeArchEndpointHausdorffRadius k r q)
    linarith
  have htail : ∀ q, q ∉ B ∪ A →
      0 ≤ (hausdorffAtomTerm primeArchEndpointHausdorffRadius k r q).re := by
    intro q hq
    have hqB : q ∉ B := fun h => hq (Finset.mem_union_left _ h)
    have hle : xiThermalNode q ≤ 1 / T ^ 2 := by
      by_contra hlt
      exact hqB (hmemB q (not_le.mp hlt))
    have h := half_norm_le_re_of_node_le_threshold k r hR hK1 hr20 hT10 hTK hΛ hle
    have h2 := norm_nonneg (hausdorffAtomTerm primeArchEndpointHausdorffRadius k r q)
    linarith
  -- The counts from the sharp mass.
  have hBcard : (B.card : ℝ) ≤ 33 / 100 * (T * Real.log T) :=
    (card_le_xiSymmetricMass_of_forall_abs_im_le hTpos.le hB_ord).trans
      (xiSymmetricMass_le_of_exp_twelve_le hTE)
  have hAcard := band_card_ge_of_exp_twelve_le hTE
  have hβα : β ≤ α / 9 := by
    have h := threshold_constant_le_band_constant k
    rw [← hK_def] at h
    rw [hβ, hα]
    have hpos : 0 ≤ (1 / T ^ 2) ^ (k + 1) * primeArchEndpointHausdorffRadius ^ r := by
      positivity
    calc (41 / 10 * (1 / T ^ 2)) ^ (k + 1) * primeArchEndpointHausdorffRadius ^ r *
          Real.exp (-(99 / 100 * K))
        = ((41 / 10) ^ (k + 1) * Real.exp (-(99 / 100 * K))) *
            ((1 / T ^ 2) ^ (k + 1) * primeArchEndpointHausdorffRadius ^ r) := by
          rw [mul_pow]
          ring
      _ ≤ (1 / 9 * (1 / 2 * (49 / 100) ^ (k + 1) * Real.exp (-(3 / 4 * K)))) *
            ((1 / T ^ 2) ^ (k + 1) * primeArchEndpointHausdorffRadius ^ r) := by
          gcongr
      _ = 1 / 2 * (49 / 100 * (1 / T ^ 2)) ^ (k + 1) * primeArchEndpointHausdorffRadius ^ r *
            Real.exp (-(3 / 4 * K)) / 9 := by
          rw [mul_pow]
          ring
  have hTlog : 0 ≤ T * Real.log T :=
    mul_nonneg hTpos.le (Real.log_nonneg (by linarith))
  exact tsum_nonneg_of_band_dominates hfsum hdisj hα0 hβ0 hTlog hA_term hB_term htail hBcard
    hAcard hβα

/-- RH reduces to the sharp finite initial segment of each Hausdorff row. -/
theorem riemannHypothesis_iff_forall_lt_sharp_HausdorffShift_nonneg :
    RiemannHypothesis ↔
      ∀ k r : ℕ, r < sharpPrimeArchHausdorffShift k →
        0 ≤ scaledHausdorffMomentDifference primeArchEndpointHausdorffRadius
          normalizedPrimeArchMoment k r := by
  constructor
  · intro hRH k r _
    exact scaledPrimeArchHausdorffMomentDifferencesNonnegative_of_riemannHypothesis hRH k r
  · intro h
    apply riemannHypothesis_of_scaledPrimeArchHausdorffMomentDifferencesNonnegative
      primeArchEndpointHausdorffRadius_pos
    intro k r
    by_cases hr : sharpPrimeArchHausdorffShift k ≤ r
    · exact scaledHausdorffMomentDifference_nonneg_of_sharp_shift_le k r hr
    · exact h k r (not_le.mp hr)

end RHTower
