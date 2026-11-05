import GaloisForLFunctions.SquareRootThreshold.EffectiveHorizons.XiZeroMass
import GaloisForLFunctions.RHTower.PrimeArchHausdorffFixedOrderLargeShiftPositivity

/-!
# Explicit shifts for the calibrated Hausdorff tower

An explicit symmetric zero-mass threshold supplies the band counts in the
Hausdorff atom estimate. Each row is therefore nonnegative beyond a closed-form
shift; RH is equivalent to positivity below these explicit row thresholds.
-/

open Complex Filter Topology

noncomputable section
namespace RHTower


/-- A closed-form shift after which the endpoint-calibrated Hausdorff row is nonnegative. -/
def explicitPrimeArchHausdorffShift (k : ℕ) : ℕ :=
  let K : ℝ := 10 * ((k + 1 : ℕ) : ℝ) + 20
  let H : ℝ := max (xiMassHeight (1 / 500))
    (max 500 (42 * ((k + 1 : ℕ) : ℝ) + 44 * K))
  ⌈20 * K⌉₊ + ⌈K * H ^ 2⌉₊ + 1

/-- Every Hausdorff row is nonnegative after its explicit shift. -/
theorem scaledHausdorffMomentDifference_nonneg_of_explicit_shift_le (k r : ℕ)
    (hr : explicitPrimeArchHausdorffShift k ≤ r) :
    0 ≤ scaledHausdorffMomentDifference primeArchEndpointHausdorffRadius
      normalizedPrimeArchMoment k r := by
  classical
  have hR : 0 < primeArchEndpointHausdorffRadius := primeArchEndpointHausdorffRadius_pos
  set K : ℝ := 10 * ((k + 1 : ℕ) : ℝ) + 20 with hK_def
  have hk0 : (0 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by positivity
  have hK1 : 1 ≤ K := by rw [hK_def]; linarith
  have hK10 : 10 * ((k + 1 : ℕ) : ℝ) ≤ K := by rw [hK_def]; linarith
  let T₀ : ℝ := xiMassHeight (1 / 500)
  have hT₀4 : 4 ≤ T₀ := four_le_xiMassHeight _
  have hclose : ∀ T : ℝ, T₀ ≤ T →
      |(xiSymmetricMass T : ℝ) - (1 / Real.pi) * (T * Real.log T)|
        ≤ (1 / 500) * (T * Real.log T) :=
    fun _ hT => xiSymmetricMass_close_explicit (by norm_num) hT
  set Tstar : ℝ := max T₀ (max 500 (42 * ((k + 1 : ℕ) : ℝ) + 44 * K)) with hTstar_def
  have hTstar0 : 0 ≤ Tstar := le_trans (by linarith) (le_max_left _ _)
  change ⌈20 * K⌉₊ + ⌈K * Tstar ^ 2⌉₊ + 1 ≤ r at hr
  have hr' : ((⌈20 * K⌉₊ + ⌈K * Tstar ^ 2⌉₊ + 1 : ℕ) : ℝ) ≤ r := by
    exact_mod_cast hr
  push_cast at hr'
  have hc1 := Nat.le_ceil (20 * K)
  have hc2 := Nat.le_ceil (K * Tstar ^ 2)
  have hc1' : (0 : ℝ) ≤ (⌈20 * K⌉₊ : ℝ) := by positivity
  have hc2' : (0 : ℝ) ≤ (⌈K * Tstar ^ 2⌉₊ : ℝ) := by
    positivity
  have hr20 : 20 * K ≤ (r : ℝ) := by linarith
  have hR1 : primeArchEndpointHausdorffRadius ≤ 1 :=
    primeArchEndpointHausdorffRadius_lt_one.le
  have hRT : K * primeArchEndpointHausdorffRadius * Tstar ^ 2 ≤ K * Tstar ^ 2 := by
    have hKR1 := mul_le_mul_of_nonneg_left hR1 (by linarith : 0 ≤ K)
    simpa only [mul_one] using mul_le_mul_of_nonneg_right hKR1 (sq_nonneg Tstar)
  have hrT : K * primeArchEndpointHausdorffRadius * Tstar ^ 2 < (r : ℝ) := by linarith
  have hrpos : 0 < (r : ℝ) := by linarith
  have hKR : 0 < K * primeArchEndpointHausdorffRadius := by positivity
  set T : ℝ := Real.sqrt ((r : ℝ) / (K * primeArchEndpointHausdorffRadius)) with hT_def
  have hT2 : T ^ 2 = r / (K * primeArchEndpointHausdorffRadius) := Real.sq_sqrt (by positivity)
  have hTpos : 0 < T := Real.sqrt_pos.mpr (by positivity)
  have hΛ : K * primeArchEndpointHausdorffRadius / r = 1 / T ^ 2 := by
    rw [hT2]
    field_simp
  have hTstar : Tstar ≤ T := by
    rw [hT_def, ← Real.sqrt_sq hTstar0]
    apply Real.sqrt_le_sqrt
    rw [le_div_iff₀ hKR]
    linarith
  have hT500 : 500 ≤ T :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hTstar
  have hT10 : 10 ≤ T := by linarith
  have hTK : 42 * ((k + 1 : ℕ) : ℝ) + 44 * K ≤ T :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hTstar
  have hTT0 : T₀ ≤ T := le_trans (le_max_left _ _) hTstar
  -- the array value as a real series over the atoms
  rw [scaledHausdorffMomentDifference_eq_re_xiCentralSum]
  have hsum : Summable (fun q => hausdorffAtomTerm primeArchEndpointHausdorffRadius k r q) :=
    summable_xiCentralScaledHausdorffTerm primeArchEndpointHausdorffRadius k r
  have hfsum : Summable (fun q => (hausdorffAtomTerm primeArchEndpointHausdorffRadius k r q).re) :=
    ⟨_, Complex.hasSum_re hsum.hasSum⟩
  change 0 ≤ (∑' q, hausdorffAtomTerm primeArchEndpointHausdorffRadius k r q).re
  rw [Complex.re_tsum hsum]
  -- the two finite families
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
  -- per-atom bounds
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
  -- counts and the constant margin
  have hBcard := card_le_of_mass_close hclose hT500 hTT0 hB_ord
  have hAcard := band_card_ge_of_mass_close hclose hT500 hTT0
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

/-- RH reduces to the explicit finite initial segment of each Hausdorff row. -/
theorem riemannHypothesis_iff_forall_lt_explicit_HausdorffShift_nonneg :
    RiemannHypothesis ↔
      ∀ k r : ℕ, r < explicitPrimeArchHausdorffShift k →
        0 ≤ scaledHausdorffMomentDifference primeArchEndpointHausdorffRadius
          normalizedPrimeArchMoment k r := by
  constructor
  · intro hRH k r _
    exact scaledPrimeArchHausdorffMomentDifferencesNonnegative_of_riemannHypothesis hRH k r
  · intro h
    apply riemannHypothesis_of_scaledPrimeArchHausdorffMomentDifferencesNonnegative
      primeArchEndpointHausdorffRadius_pos
    intro k r
    by_cases hr : explicitPrimeArchHausdorffShift k ≤ r
    · exact scaledHausdorffMomentDifference_nonneg_of_explicit_shift_le k r hr
    · exact h k r (not_le.mp hr)

#print axioms scaledHausdorffMomentDifference_nonneg_of_explicit_shift_le
#print axioms riemannHypothesis_iff_forall_lt_explicit_HausdorffShift_nonneg

end RHTower
