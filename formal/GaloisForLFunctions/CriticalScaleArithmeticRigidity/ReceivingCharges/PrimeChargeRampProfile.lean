import GaloisForLFunctions.CriticalScaleArithmeticRigidity.ReceivingCharges.PrimeChargeSignedReceiver

/-!
# The full receiving tail is a logarithmic ramp

The harmonic second moment of prime incidence controls the complete tower
error in norm, uniformly in the horizon. Thus every bounded receiver reads
the same limiting signed profile as the logarithmic ramp.
-/

noncomputable section

open Finset Filter Topology
open scoped Classical RealInnerProductSpace

namespace GaloisForLFunctions.CriticalScaleArithmeticRigidity

open ArithmeticCouplingTheory RenormalizedArithmeticPotentialTheory
  SelectiveMultiscaleArithmeticPositivity
open _root_.RHTower.Sieve

/-- The logarithmic receiving ramp in physical horizon coordinates. -/
def primeChargeRampVector (Q N : ℕ) (t : ℝ) :
    EuclideanSpace ℝ (PrimeHorizonIndex N) :=
  (Real.sqrt (Real.log N))⁻¹ • packetVector
    (fun n => (t / primePoleScale Q) * max (Real.log Q + Real.log n - Real.log N) 0) N

private theorem ramp_error_harmonic_square_le {Q N : ℕ} (hQ : 1 ≤ Q) (b : ℝ) :
    (∑ n ∈ Icc 1 N,
      (completedPrimeDilationTail Q (primeIncidenceCoefficients (fun _ => b)) (N / n) n -
        b * max (Real.log Q + Real.log n - Real.log N) 0) ^ 2 / (n : ℝ)) ≤
      2 * b ^ 2 * harmonicMass N *
        (primeChargeRampErrorConstant + 1 + ∑ p ∈ (Icc 1 Q).filter Nat.Prime, 1 / (p : ℝ)) ^ 2 := by
  let P := (Icc 1 Q).filter Nat.Prime
  let C := primeChargeRampErrorConstant
  let S := ∑ p ∈ P, 1 / (p : ℝ)
  have hC : 0 ≤ C := primeChargeRampErrorConstant_nonneg
  have hS : 0 ≤ S := sum_nonneg fun p _ => by positivity
  have hH : 0 ≤ harmonicMass N := sum_nonneg fun n _ => by positivity
  have hpoint (n : ℕ) (hn : n ∈ Icc 1 N) :
      (completedPrimeDilationTail Q (primeIncidenceCoefficients (fun _ => b)) (N / n) n -
        b * max (Real.log Q + Real.log n - Real.log N) 0) ^ 2 ≤
          2 * b ^ 2 * (C ^ 2 + primeDivisorCount P n ^ 2) := by
    have h := abs_completedPrimeDilationTail_coherent_sub_ramp_le hQ
      (mem_Icc.mp hn).1 (mem_Icc.mp hn).2 b
    change |_ - _| ≤ |b| * (C + primeDivisorCount P n) at h
    have hs := pow_le_pow_left₀ (abs_nonneg _) h 2
    rw [sq_abs, mul_pow, sq_abs] at hs
    refine hs.trans ?_
    have he : (C + primeDivisorCount P n) ^ 2 ≤
        2 * (C ^ 2 + primeDivisorCount P n ^ 2) := by
      nlinarith only [sq_nonneg (C - primeDivisorCount P n)]
    exact (mul_le_mul_of_nonneg_left he (sq_nonneg b)).trans_eq (by ring)
  calc
    _ ≤ ∑ n ∈ Icc 1 N, (2 * b ^ 2 * (C ^ 2 + primeDivisorCount P n ^ 2)) / n :=
      sum_le_sum fun n hn => div_le_div_of_nonneg_right (hpoint n hn) (Nat.cast_nonneg n)
    _ = 2 * b ^ 2 * (C ^ 2 * harmonicMass N +
        ∑ n ∈ Icc 1 N, primeDivisorCount P n ^ 2 / (n : ℝ)) := by
      simp only [harmonicMass, mul_sum, mul_add, add_div, ← sum_add_distrib]
      exact sum_congr rfl fun n _ => by ring
    _ ≤ 2 * b ^ 2 * (C ^ 2 * harmonicMass N + harmonicMass N * (S ^ 2 + S)) :=
      mul_le_mul_of_nonneg_left (add_le_add le_rfl
        (primeDivisorCount_harmonic_second_moment_le
          (fun p hp => (mem_filter.mp hp).2) N)) (by positivity)
    _ = 2 * b ^ 2 * harmonicMass N * (C ^ 2 + S ^ 2 + S) := by ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity : 0 ≤ 2 * b ^ 2 * harmonicMass N)
      change C ^ 2 + S ^ 2 + S ≤ (C + 1 + S) ^ 2
      nlinarith only [hC, hS, mul_nonneg hC hS]

/-- The full tail differs from the ramp by a horizon-uniform vanishing norm. -/
theorem primeChargeTailVector_sub_ramp_norm_le {Q N : ℕ}
    (hQ : 2 ≤ Q) (hL : 1 ≤ Real.log N) (t : ℝ) :
    ‖primeChargeTailVector Q N t - primeChargeRampVector Q N t‖ ≤
      2 * |t| * ((primeChargeRampErrorConstant + 1 +
        ∑ p ∈ (Icc 1 Q).filter Nat.Prime, 1 / (p : ℝ)) / primePoleScale Q) := by
  let b := t / primePoleScale Q
  let T : ℕ → ℝ := fun n => completedPrimeDilationTail Q
    (primeIncidenceCoefficients (fun _ => b)) (N / n) n
  let R : ℕ → ℝ := fun n => b * max (Real.log Q + Real.log n - Real.log N) 0
  let A := primeChargeRampErrorConstant + 1 +
    ∑ p ∈ (Icc 1 Q).filter Nat.Prime, 1 / (p : ℝ)
  have hA : 0 ≤ A := by
    have hC := primeChargeRampErrorConstant_nonneg
    have hS : 0 ≤ ∑ p ∈ (Icc 1 Q).filter Nat.Prime, 1 / (p : ℝ) :=
      sum_nonneg fun p _ => by positivity
    dsimp only [A]
    positivity
  have hB := primePoleScale_pos hQ
  have hL0 : 0 < Real.log N := zero_lt_one.trans_le hL
  have hH : harmonicMass N ≤ 2 * Real.log N := by
    have h := harmonic_le_one_add_log N
    have he : (harmonic N : ℝ) = harmonicMass N := by
      simpa only [harmonicMass, one_div] using
        _root_.RHTower.RegularizedDivisorHarmonic.harmonic_cast_eq_sum N
    rw [he] at h
    linarith only [h, hL]
  have hsub : packetVector (fun n => T n - R n) N = packetVector T N - packetVector R N := by
    have he : (fun n => T n - R n) = (fun n => T n + (-1 : ℝ) * R n) := by
      funext n
      ring
    rw [he, packetVector_add, packetVector_const_mul, neg_one_smul]
    rfl
  have hid : primeChargeTailVector Q N t - primeChargeRampVector Q N t =
      (Real.sqrt (Real.log N))⁻¹ • packetVector (fun n => T n - R n) N := by
    rw [hsub, smul_sub]
    rfl
  have hsq : ‖primeChargeTailVector Q N t - primeChargeRampVector Q N t‖ ^ 2 ≤
      (2 * |t| * (A / primePoleScale Q)) ^ 2 := by
    rw [hid, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, inv_pow,
      Real.sq_sqrt (Real.log_natCast_nonneg N), packetVector_norm_sq]
    have hb := ramp_error_harmonic_square_le (N := N) (by omega : 1 ≤ Q) b
    calc
      _ ≤ (Real.log N)⁻¹ * (2 * b ^ 2 * harmonicMass N * A ^ 2) :=
        mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hL0.le)
      _ ≤ (Real.log N)⁻¹ * (2 * b ^ 2 * (2 * Real.log N) * A ^ 2) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hH (by positivity)) (sq_nonneg A))
            (inv_nonneg.mpr hL0.le)
      _ = _ := by
        dsimp only [b]
        rw [mul_pow, mul_pow, sq_abs]
        field_simp [hL0.ne', hB.ne']
  have hnonneg : 0 ≤ 2 * |t| * (A / primePoleScale Q) := by positivity
  change _ ≤ 2 * |t| * (A / primePoleScale Q)
  nlinarith only [hsq, hnonneg, norm_nonneg (primeChargeTailVector Q N t - primeChargeRampVector Q N t)]

/-- Convergence of the complete receiving tail to its ramp is uniform over every horizon with `log N ≥ 1`. -/
theorem primeChargeTailVector_ramp_uniform (t : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ Q₀ : ℕ, ∀ Q ≥ Q₀, ∀ N : ℕ, 1 ≤ Real.log N →
      ‖primeChargeTailVector Q N t - primeChargeRampVector Q N t‖ < ε := by
  have h := (tendsto_primeReciprocal_add_div_primePoleScale
    (primeChargeRampErrorConstant + 1)).const_mul (2 * |t|)
  simp only [mul_zero] at h
  have he := h.eventually (gt_mem_nhds hε)
  obtain ⟨Q₀, hQ₀⟩ := eventually_atTop.1 ((eventually_ge_atTop 2).and he)
  refine ⟨Q₀, fun Q hQ N hN => ?_⟩
  exact (primeChargeTailVector_sub_ramp_norm_le (hQ₀ Q hQ).1 hN t).trans_lt (hQ₀ Q hQ).2

#print axioms primeChargeTailVector_sub_ramp_norm_le
#print axioms primeChargeTailVector_ramp_uniform

end GaloisForLFunctions.CriticalScaleArithmeticRigidity
