import GaloisForLFunctions.CriticalScaleArithmeticRigidity.ReceivingCharges.PrimeChargeScaleLimits
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.SmallWidthKeepsPrimeGeometryPolynomial

/-!
# Uniform geometry beyond a fixed power of the conductor cutoff

The condition `Q⁶⁴ ≤ N` supplies every conductor frame needed by the
quadratic decomposition. The remaining near-radius and width conditions
hold on the critical curve independently of `Q`.
-/

noncomputable section

open Filter Topology

namespace GaloisForLFunctions.CriticalScaleArithmeticRigidity

open CriticalArithmeticCorrelationTheory

/-- A distant horizon gives the logarithmic conductor frame uniformly in its cutoff. -/
theorem primeCharge_far_cutoff_frame {Q N : ℕ} (hQ : 2 ≤ Q)
    (hQN : Q ^ 64 ≤ N) (hL : 64 ≤ Real.log N) :
    Q ^ 4 ≤ N ∧ 18 * (1 + Real.log Q) ≤ Real.log N := by
  have hQR : (0 : ℝ) < Q := by exact_mod_cast (show 0 < Q by omega)
  have hp : (Q : ℝ) ^ 64 ≤ N := by exact_mod_cast hQN
  have hlog := Real.log_le_log (pow_pos hQR 64) hp
  rw [Real.log_pow] at hlog
  norm_num only [Nat.cast_ofNat] at hlog
  exact ⟨(Nat.pow_le_pow_right (by omega : 1 ≤ Q) (by omega : 4 ≤ 64)).trans hQN,
    by linarith only [hlog, hL]⟩

/-- The radius square condition already controls the full conductor sampling size. -/
theorem primeCharge_near_size_of_radius {Q N : ℕ} {c : ℝ}
    (hQ : 1 ≤ Q) (hQ4 : Q ^ 4 ≤ N) (hc : 0 ≤ c)
    (hrad : 4 * (linearNearRowRadius c + 1) ^ 2 ≤ N) :
    ((Q * Q : ℕ) + 1 : ℝ) * (linearNearRowRadius c + 1) ≤ N := by
  have hQR : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hQ4R : (Q : ℝ) ^ 4 ≤ N := by exact_mod_cast hQ4
  have hq2 : (1 : ℝ) ≤ (Q : ℝ) ^ 2 := by nlinarith only [hQR]
  have hA : ((Q : ℝ) ^ 2 + 1) ^ 2 ≤ 4 * (Q : ℝ) ^ 4 := by
    nlinarith only [hq2, sq_nonneg ((Q : ℝ) ^ 2 - 1)]
  have h1 := mul_le_mul_of_nonneg_right hA (sq_nonneg (linearNearRowRadius c + 1))
  have h2 := mul_le_mul_of_nonneg_left hrad (pow_nonneg (Nat.cast_nonneg Q) 4)
  have h3 := mul_le_mul_of_nonneg_right hQ4R (Nat.cast_nonneg N)
  have hsq : (((Q : ℝ) ^ 2 + 1) * (linearNearRowRadius c + 1)) ^ 2 ≤ (N : ℝ) ^ 2 := by
    nlinarith only [h1, h2, h3]
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hrad0 : 0 ≤ linearNearRowRadius c + 1 := by
    unfold linearNearRowRadius
    positivity
  have hprod : 0 ≤ ((Q : ℝ) ^ 2 + 1) * (linearNearRowRadius c + 1) := by positivity
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_one]
  nlinarith only [hsq, hN, hprod]

/-- Every fixed power of critical overlap is negligible compared with the horizon. -/
theorem tendsto_primeCharge_critical_power_div_nat (K : ℝ) (k : ℕ) :
    Tendsto (fun N : ℕ =>
      (2 * K * Real.log N ^ (1 / 8 : ℝ)) ^ k / (N : ℝ)) atTop (𝓝 0) := by
  have h := (tendsto_log_rpow_div_nat ((1 / 8 : ℝ) * k)).const_mul ((2 * K) ^ k)
  simp only [mul_zero] at h
  convert h using 1
  funext N
  have hp : (Real.log N ^ (1 / 8 : ℝ)) ^ k =
      Real.log N ^ ((1 / 8 : ℝ) * k) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Real.log_natCast_nonneg N)]
  rw [mul_pow, hp, mul_div_assoc]

/-- All finite quadratic-channel geometry holds eventually, uniformly for `Q⁶⁴ ≤ N`. -/
theorem eventually_primeCharge_uniform_geometry {K : ℝ} (hK : 0 < K) :
    ∀ᶠ N : ℕ in atTop,
      let c := 2 * K * Real.log N ^ (1 / 8 : ℝ)
      1 ≤ Real.log N ∧ 1 ≤ c ∧ c / N ≤ 1 / 3 ∧
        4 * (linearNearRowRadius c + 1) ^ 2 ≤ N ∧ c ^ 4 ≤ N ∧
        ∀ Q : ℕ, 2 ≤ Q → Q ^ 64 ≤ N →
          Q ^ 4 ≤ N ∧ 18 * (1 + Real.log Q) ≤ Real.log N ∧
            ((Q * Q : ℕ) + 1 : ℝ) * (linearNearRowRadius c + 1) ≤ N := by
  have hr : Tendsto (fun N : ℕ =>
      4 * (linearNearRowRadius (2 * K * Real.log N ^ (1 / 8 : ℝ)) + 1) ^ 2 /
        (N : ℝ)) atTop (𝓝 0) := by
    have h := (((tendsto_primeCharge_critical_power_div_nat K 2).const_mul
      (4 * (2 * Real.exp 2) ^ 2)).add
        ((tendsto_primeCharge_critical_power_div_nat K 1).const_mul (8 * (2 * Real.exp 2)))).add
          (tendsto_natCast_atTop_atTop.const_div_atTop (4 : ℝ))
    simp only [mul_zero, zero_add, add_zero] at h
    convert h using 1
    funext N
    unfold linearNearRowRadius
    ring
  have hL := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop 1, hL.eventually_ge_atTop 64,
    eventually_primeCharge_criticalOverlap_facts hK,
    hr.eventually (ge_mem_nhds zero_lt_one),
    (tendsto_primeCharge_critical_power_div_nat K 4).eventually (ge_mem_nhds zero_lt_one)]
      with N hN hlog hc hrad hc4
  dsimp only
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hrad' := (div_le_one hNR).mp hrad
  have hc4' := (div_le_one hNR).mp hc4
  refine ⟨by linarith only [hlog], hc.1, hc.2, hrad', hc4', ?_⟩
  intro Q hQ hQN
  obtain ⟨hQ4, hframe⟩ := primeCharge_far_cutoff_frame hQ hQN hlog
  exact ⟨hQ4, hframe, primeCharge_near_size_of_radius (by omega) hQ4
    (zero_le_one.trans hc.1) hrad'⟩

#print axioms primeCharge_near_size_of_radius
#print axioms eventually_primeCharge_uniform_geometry

end GaloisForLFunctions.CriticalScaleArithmeticRigidity
