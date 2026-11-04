import GaloisForLFunctions.CriticalScaleArithmeticRigidity.ReceivingCharges.FixedPacketCriticalCancellation
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.CompleteConductorResidualsAreUniformOnLogarithmicFamilies
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.CompleteWeilCriticalMultipleAndWindowCorollaries

/-!
# Fixed-conductor cancellation for every smooth atom

The complete conductor residual has three decaying rates at critical overlap.
Together with decay of the completed conductor energy, this annihilates each
fixed normalized conductor in the complete operator norm, for every admissible atom.
-/

noncomputable section

open Finset Filter Topology MeasureTheory
open scoped Classical RealInnerProductSpace

namespace GaloisForLFunctions.CriticalScaleArithmeticRigidity

open CriticalArithmeticCorrelationTheory ArithmeticHodgeTheoryOfDegenerations
  RenormalizedArithmeticPotentialTheory RenormalizedArithmeticPotentialTheory.CompletedShell
  SpacingScaleHarmonicAnalysis ArithmeticCouplingTheory

/-- Every overlap power below eight is negligible relative to the logarithmic horizon. -/
theorem criticalCurve_pow_div_log {c : ℕ → ℝ}
    (hc : ∀ N, 1 ≤ c N) {R : ℝ} (hR : 0 < R)
    (hcrit : Tendsto (fun N : ℕ => c N ^ 8 / Real.log N) atTop (𝓝 R))
    {k : ℕ} (hk : k < 8) :
    Tendsto (fun N : ℕ => c N ^ k / Real.log N) atTop (𝓝 0) := by
  have hcinf := (criticalCurve_facts hc hR hcrit).1
  have hinv := tendsto_inv_atTop_zero.comp
    ((tendsto_pow_atTop (by omega : 8 - k ≠ 0)).comp hcinf)
  have h := hcrit.mul hinv
  simp only [mul_zero] at h
  apply h.congr
  intro N
  have hc0 : c N ≠ 0 := (zero_lt_one.trans_le (hc N)).ne'
  have hp : c N ^ 8 = c N ^ k * c N ^ (8 - k) := by
    rw [← pow_add, Nat.add_sub_of_le hk.le]
  simp only [Function.comp_apply]
  calc
    _ = c N ^ k * (c N ^ (8 - k) * (c N ^ (8 - k))⁻¹) / Real.log N := by
      rw [hp]
      ring
    _ = _ := by rw [mul_inv_cancel₀ (pow_ne_zero _ hc0), mul_one]

/-- The full residual of any fixed conductor vanishes at every positive critical ratio. -/
theorem tendsto_fixedConductor_critical_residual_norm_of_atom {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) {c : ℕ → ℝ}
    (hc : ∀ N, 1 ≤ c N) {R : ℝ} (hR : 0 < R)
    (hcrit : Tendsto (fun N : ℕ => c N ^ 8 / Real.log N) atTop (𝓝 R))
    {m : ℕ} (hm : 0 < m) :
    Tendsto (fun N : ℕ =>
      ‖Matrix.toEuclideanLin (completeWeilMatrix φ (c N) N)
          (normalizedRamanujanHorizonVector m N) -
        completedConductorEnergy φ (c N) m • normalizedRamanujanHorizonVector m N‖)
      atTop (𝓝 0) := by
  obtain ⟨K, hK, hbound⟩ := exists_completeWeil_uniform_conductor_residual_bound hφ hsupp hM
  have hfive := criticalCurve_pow_div_log hc hR hcrit (by norm_num : 5 < 8)
  have hsix := (criticalCurve_pow_div_log hc hR hcrit (by norm_num : 6 < 8)).sqrt
  have hthree : Tendsto (fun N : ℕ => c N ^ 3 / Real.sqrt (Real.log N)) atTop (𝓝 0) := by
    simp only [Real.sqrt_zero] at hsix
    apply hsix.congr
    intro N
    rw [Real.sqrt_div (pow_nonneg (zero_le_one.trans (hc N)) 6),
      show c N ^ 6 = (c N ^ 3) ^ 2 by ring,
      Real.sqrt_sq (pow_nonneg (zero_le_one.trans (hc N)) _)]
  have hboundary := (criticalCurve_pow_log_div_natCast hc hR hcrit 5 1).pow 2
  have hlim := ((hfive.add hboundary).add hthree).const_mul (K * (m : ℝ) ^ 4)
  simp only [pow_one, zero_pow two_ne_zero, add_zero, mul_zero] at hlim
  have hwidth := (criticalCurve_pow_log_div_natCast hc hR hcrit 2 0).const_mul
    (4 * (Real.exp 1 + 3) ^ 2)
  simp only [pow_zero, mul_one, mul_zero] at hwidth
  have hlog := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hsq : Tendsto (fun N : ℕ =>
      ‖Matrix.toEuclideanLin (completeWeilMatrix φ (c N) N)
          (normalizedRamanujanHorizonVector m N) -
        completedConductorEnergy φ (c N) m • normalizedRamanujanHorizonVector m N‖ ^ 2)
      atTop (𝓝 0) := by
    refine squeeze_zero' (Eventually.of_forall fun _ => sq_nonneg _) ?_ hlim
    filter_upwards [hbound 1 (by norm_num), hlog.eventually_ge_atTop m,
      hwidth.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)), eventually_ge_atTop 1]
      with N hb hmN hw hN
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
    have hw' : 4 * (Real.exp 1 + 3) ^ 2 * c N ^ 2 ≤ (N : ℝ) := by
      have h := (div_lt_iff₀ hN0).mp (show
        (4 * (Real.exp 1 + 3) ^ 2 * c N ^ 2) / N < 1 by simpa only [mul_div_assoc] using hw)
      simpa only [one_mul] using h.le
    have h := hb m hm (by simpa only [Real.rpow_one] using hmN) (c N) (hc N) hw'
    convert h using 1 <;> ring
  simpa only [Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using hsq.sqrt

/-- Each fixed normalized conductor has vanishing complete output for every admissible atom. -/
theorem tendsto_fixedConductor_critical_complete_norm_of_atom {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) {c : ℕ → ℝ}
    (hc : ∀ N, 1 ≤ c N) {R : ℝ} (hR : 0 < R)
    (hcrit : Tendsto (fun N : ℕ => c N ^ 8 / Real.log N) atTop (𝓝 R))
    {m : ℕ} (hm : 0 < m) :
    Tendsto (fun N : ℕ =>
      ‖Matrix.toEuclideanLin (completeWeilMatrix φ (c N) N)
        (normalizedRamanujanHorizonVector m N)‖) atTop (𝓝 0) := by
  have hE := (tendsto_completedConductorEnergy_atTop hφ hsupp hM m).comp
    (criticalCurve_facts hc hR hcrit).1
  have hnorm : Tendsto (fun N : ℕ => ‖normalizedRamanujanHorizonVector m N‖ ^ 2)
      atTop (𝓝 (1 : ℝ)) := by
    simpa only [real_inner_self_eq_norm_sq, if_true] using
      tendsto_normalizedRamanujanHorizonVector_gram hm hm
  have hlim := (tendsto_fixedConductor_critical_residual_norm_of_atom hφ hsupp hM
    hc hR hcrit hm).add (hE.mul_const 2)
  simp only [Function.comp_apply, zero_mul, zero_add] at hlim
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hlim
  filter_upwards [hnorm.eventually (gt_mem_nhds (by norm_num : (1 : ℝ) < 4))]
    with N hnormN
  have hv : ‖normalizedRamanujanHorizonVector m N‖ ≤ 2 := by
    nlinarith only [hnormN, norm_nonneg (normalizedRamanujanHorizonVector m N)]
  have hE0 := completedConductorEnergy_nonneg hφ hsupp hM
    (zero_lt_one.trans_le (hc N)) hm
  calc
    _ ≤ ‖Matrix.toEuclideanLin (completeWeilMatrix φ (c N) N)
          (normalizedRamanujanHorizonVector m N) -
        completedConductorEnergy φ (c N) m • normalizedRamanujanHorizonVector m N‖ +
        ‖completedConductorEnergy φ (c N) m • normalizedRamanujanHorizonVector m N‖ := by
      simpa only [sub_add_cancel] using norm_add_le
        (Matrix.toEuclideanLin (completeWeilMatrix φ (c N) N)
          (normalizedRamanujanHorizonVector m N) -
          completedConductorEnergy φ (c N) m • normalizedRamanujanHorizonVector m N)
        (completedConductorEnergy φ (c N) m • normalizedRamanujanHorizonVector m N)
    _ ≤ _ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hE0]
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hv hE0)

/-- Finite fixed conductor packets retain cancellation with bounded varying coefficients. -/
theorem tendsto_fixedPacket_critical_complete_norm_of_atom {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) {c : ℕ → ℝ}
    (hc : ∀ N, 1 ≤ c N) {R : ℝ} (hR : 0 < R)
    (hcrit : Tendsto (fun N : ℕ => c N ^ 8 / Real.log N) atTop (𝓝 R))
    (S : Finset ℕ) (hS : ∀ m ∈ S, 0 < m) (a : ℕ → ℕ → ℝ) (B : ℕ → ℝ)
    (hB : ∀ᶠ N in atTop, ∀ m ∈ S, |a N m| ≤ B m) :
    Tendsto (fun N : ℕ =>
      ‖Matrix.toEuclideanLin (completeWeilMatrix φ (c N) N)
        (∑ m ∈ S, a N m • normalizedRamanujanHorizonVector m N)‖) atTop (𝓝 0) := by
  have hlim := tendsto_finsetSum S (fun m hm =>
    (tendsto_fixedConductor_critical_complete_norm_of_atom hφ hsupp hM hc hR hcrit
      (hS m hm)).const_mul (B m))
  simp only [mul_zero, sum_const_zero] at hlim
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hlim
  filter_upwards [hB] with N hBN
  simp only [map_sum, map_smul]
  refine (norm_sum_le _ _).trans (sum_le_sum ?_)
  intro m hm
  rw [norm_smul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right (hBN m hm) (norm_nonneg _)

/-- Literal harmonic pole subtraction preserves fixed-packet cancellation for every atom. -/
theorem tendsto_harmonicCentered_fixedPacket_complete_norm_of_atom {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) {c : ℕ → ℝ}
    (hc : ∀ N, 1 ≤ c N) {R : ℝ} (hR : 0 < R)
    (hcrit : Tendsto (fun N : ℕ => c N ^ 8 / Real.log N) atTop (𝓝 R))
    (Q : ℕ) (a : ℕ → ℝ) :
    Tendsto (fun N : ℕ =>
      ‖Matrix.toEuclideanLin (completeWeilMatrix φ (c N) N)
        ((Real.sqrt (Real.log N))⁻¹ • packetVector
          (normalizedConductorPacket Q (harmonicCenteredCoefficients Q N a)) N)‖)
      atTop (𝓝 0) := by
  simp only [physicalPacket_eq_sum_normalizedModes]
  apply tendsto_fixedPacket_critical_complete_norm_of_atom hφ hsupp hM hc hR hcrit
    (Icc 1 Q) (fun m hm => (mem_Icc.mp hm).1)
    (fun N => harmonicCenteredCoefficients Q N a)
    (fun m => |a m| + ∑ j ∈ Icc 1 Q, |a j| * modeBound j)
  filter_upwards [eventually_ge_atTop 1] with N hN m _
  exact harmonicCentered_fixedCoefficient_abs_le Q hN a m

/-- The canonical clock agrees exactly with the clipped critical-overlap formula. -/
theorem canonicalCriticalCurve_power_mul {K : ℝ} (hK : 0 < K) (N : ℕ) :
    canonicalCriticalCurve ((2 * K) ^ 8) N =
      max 1 (2 * K * Real.log N ^ (1 / 8 : ℝ)) := by
  unfold canonicalCriticalCurve
  rw [Real.mul_rpow (pow_nonneg (by positivity : 0 ≤ 2 * K) 8) (Real.log_natCast_nonneg N)]
  have hp : ((2 * K) ^ 8) ^ (1 / 8 : ℝ) = 2 * K := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity : 0 ≤ 2 * K)]
    norm_num
  rw [hp]

/-- The literal critical-overlap family also annihilates every fixed conductor column. -/
theorem tendsto_fixedConductor_complete_norm_at_critical_overlap {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) {K : ℝ} (hK : 0 < K) {m : ℕ} (hm : 0 < m) :
    Tendsto (fun N : ℕ =>
      ‖Matrix.toEuclideanLin (completeWeilMatrix φ (2 * K * Real.log N ^ (1 / 8 : ℝ)) N)
        (normalizedRamanujanHorizonVector m N)‖) atTop (𝓝 0) := by
  have hR : 0 < (2 * K) ^ 8 := by positivity
  have h := tendsto_fixedConductor_critical_complete_norm_of_atom hφ hsupp hM
    (one_le_canonicalCriticalCurve ((2 * K) ^ 8)) hR
    (tendsto_canonicalCriticalCurve_pow_eight hR) hm
  apply h.congr'
  filter_upwards [eventually_primeCharge_criticalOverlap_facts hK] with N hN
  rw [canonicalCriticalCurve_power_mul hK, max_eq_right hN.1]

/-- Harmonic-centered fixed packets cancel on the literal critical-overlap family. -/
theorem tendsto_harmonicCentered_fixedPacket_complete_norm_at_critical_overlap {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) {K : ℝ} (hK : 0 < K)
    (Q : ℕ) (a : ℕ → ℝ) :
    Tendsto (fun N : ℕ =>
      ‖Matrix.toEuclideanLin (completeWeilMatrix φ (2 * K * Real.log N ^ (1 / 8 : ℝ)) N)
        ((Real.sqrt (Real.log N))⁻¹ • packetVector
          (normalizedConductorPacket Q (harmonicCenteredCoefficients Q N a)) N)‖)
      atTop (𝓝 0) := by
  have hR : 0 < (2 * K) ^ 8 := by positivity
  have h := tendsto_harmonicCentered_fixedPacket_complete_norm_of_atom hφ hsupp hM
    (one_le_canonicalCriticalCurve ((2 * K) ^ 8)) hR
    (tendsto_canonicalCriticalCurve_pow_eight hR) Q a
  apply h.congr'
  filter_upwards [eventually_primeCharge_criticalOverlap_facts hK] with N hN
  rw [canonicalCriticalCurve_power_mul hK, max_eq_right hN.1]

#print axioms criticalCurve_pow_div_log
#print axioms tendsto_fixedConductor_critical_residual_norm_of_atom
#print axioms tendsto_fixedConductor_critical_complete_norm_of_atom
#print axioms tendsto_harmonicCentered_fixedPacket_complete_norm_of_atom
#print axioms tendsto_fixedConductor_complete_norm_at_critical_overlap
#print axioms tendsto_harmonicCentered_fixedPacket_complete_norm_at_critical_overlap

end GaloisForLFunctions.CriticalScaleArithmeticRigidity
