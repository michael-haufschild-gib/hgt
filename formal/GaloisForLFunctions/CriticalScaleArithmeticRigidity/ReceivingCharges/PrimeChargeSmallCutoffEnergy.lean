import GaloisForLFunctions.CriticalScaleArithmeticRigidity.ReceivingCharges.PrimeChargeUniformFiniteBounds
import GaloisForLFunctions.CriticalScaleArithmeticRigidity.ReceivingCharges.PrimeChargeUniformScales

/-!
# Vanishing complete energy below a logarithmic prime cutoff

For `Q³² ≤ log N`, the two coefficient moments in the complete conductor
residual lose powers of `log N`. The completed diagonal vanishes with `Q`,
including the exact harmonic-centering coefficient.
-/

noncomputable section

open Finset Filter Topology MeasureTheory

namespace GaloisForLFunctions.CriticalScaleArithmeticRigidity

open ArithmeticCouplingTheory RenormalizedArithmeticPotentialTheory CompletedArithmeticForms

private theorem small_cutoff_powers {Q : ℕ} {L : ℝ}
    (hQ : 1 ≤ Q) (hQL : (Q : ℝ) ^ 32 ≤ L) :
    (Q : ℝ) ^ 5 ≤ L ^ (1 / 4 : ℝ) ∧
      (Q : ℝ) ^ 11 ≤ L ^ (1 / 2 : ℝ) ∧ (Q : ℝ) ≤ L := by
  have h8 := Real.rpow_le_rpow (pow_nonneg (Nat.cast_nonneg Q) 32) hQL
    (by norm_num : (0 : ℝ) ≤ 1 / 4)
  have h16 := Real.rpow_le_rpow (pow_nonneg (Nat.cast_nonneg Q) 32) hQL
    (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have he8 : ((Q : ℝ) ^ 32) ^ (1 / 4 : ℝ) = (Q : ℝ) ^ 8 := by
    rw [← Real.rpow_natCast (Q : ℝ) 32, ← Real.rpow_mul (Nat.cast_nonneg Q)]
    norm_num
  have he16 : ((Q : ℝ) ^ 32) ^ (1 / 2 : ℝ) = (Q : ℝ) ^ 16 := by
    rw [← Real.rpow_natCast (Q : ℝ) 32, ← Real.rpow_mul (Nat.cast_nonneg Q)]
    norm_num
  rw [he8] at h8
  rw [he16] at h16
  refine ⟨?_, ?_, ?_⟩
  · exact (show (Q : ℝ) ^ 5 ≤ (Q : ℝ) ^ 8 by
      exact_mod_cast Nat.pow_le_pow_right hQ (by omega : 5 ≤ 8)).trans h8
  · exact (show (Q : ℝ) ^ 11 ≤ (Q : ℝ) ^ 16 by
      exact_mod_cast Nat.pow_le_pow_right hQ (by omega : 11 ≤ 16)).trans h16
  · exact (show (Q : ℝ) ≤ (Q : ℝ) ^ 32 by
      exact_mod_cast (Nat.le_pow (by omega : 0 < 32) : Q ≤ Q ^ 32)).trans hQL

/-- The literal complete physical energy vanishes in the smallest-cutoff range. -/
theorem tendsto_harmonicPrimeCharge_energy_small_cutoff {ι : Type*} {l : Filter ι}
    {Q N : ι → ℕ} (hQ : Tendsto Q l atTop) (hN : Tendsto N l atTop)
    (hfar : ∀ᶠ i in l, Q i ^ 64 ≤ N i)
    (hsmall : ∀ᶠ i in l, (Q i : ℝ) ^ 32 ≤ Real.log (N i))
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2)
    {K : ℝ} (hK : 0 < K) (t : ℝ) :
    Tendsto (fun i => completeWeilEnergy φ (2 * K * Real.log (N i) ^ (1 / 8 : ℝ))
      (N i) (harmonicPrimeChargeVector (Q i) (N i) t)) l (𝓝 0) := by
  obtain ⟨A, hA, hb⟩ := exists_harmonicPrimeCharge_small_cutoff_bound hφ hsupp hM
  let D := |completeWeilSelfFinitePart φ 1| + 3
  let c := fun n : ℕ => 2 * K * Real.log n ^ (1 / 8 : ℝ)
  let P := fun i => (|t| + 8 * |t| / primePoleScale (Q i)) / Real.log (N i)
  let V := fun q : ℕ => (t / primePoleScale q) ^ 2 *
    ∑ p ∈ (Icc 1 q).filter Nat.Prime, 1 / (p : ℝ)
  let T := fun q : ℕ => (t / primePoleScale q) ^ 2 *
    ((∑ p ∈ (Icc 1 q).filter Nat.Prime, 1 / (p : ℝ)) + primePoleScale q)
  let G := fun n : ℕ => A * (Real.log n ^ (1 / 4 : ℝ) * c n / Real.log n +
      Real.log n ^ (3 / 2 : ℝ) * c n ^ 5 / n) +
    9 * D * ((1 + Real.log (Real.log n)) ^ 2 / Real.log n)
  have hG : Tendsto G atTop (𝓝 0) := by
    have h1 := tendsto_receiving_log_mul_critical_power_div_log K (1 / 4) 1 (by norm_num)
    have h2 := tendsto_receiving_log_mul_critical_power_div_nat_rpow K (3 / 2) 5
      (by norm_num : (0 : ℝ) < 1)
    have h3 := tendsto_receiving_loglog_square_div_log.const_mul (9 * D)
    have h := ((h1.add h2).const_mul A).add h3
    simpa only [G, c, pow_one, Real.rpow_one, mul_zero, zero_add] using h
  have hP := (tendsto_primeCharge_polar_bound hQ hN t).pow 2
  have hV := (tendsto_primeCharge_reciprocal_mass t).comp hQ
  have hT := (tendsto_primeCharge_completed_coefficient_mass t).comp hQ
  have hz := ((hP.add hT).const_mul D).add ((hG.comp hN).mul (hP.add hV))
  simp only [zero_pow two_ne_zero, zero_add, mul_zero, add_zero] at hz
  refine squeeze_zero_norm' ?_ hz
  filter_upwards [hQ.eventually (eventually_ge_atTop 2),
    hN.eventually (eventually_primeCharge_uniform_geometry hK), hfar, hsmall]
      with i hQi hgeom hQiN hsmalli
  obtain ⟨hL, hc, hw, hrad, hc4, hgeomQ⟩ := hgeom
  obtain ⟨hQ4, hframe, hsize⟩ := hgeomQ (Q i) hQi hQiN
  have hQ2 : Q i * Q i ≤ N i := by
    rw [← pow_two]
    exact (Nat.pow_le_pow_right (by omega : 1 ≤ Q i) (by omega : 2 ≤ 4)).trans hQ4
  have hL0 : 0 < Real.log (N i) := zero_lt_one.trans_le hL
  have hc0 : 0 ≤ c (N i) := zero_le_one.trans hc
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  obtain ⟨hQ5, hQ11, hQL⟩ := small_cutoff_powers (by omega : 1 ≤ Q i) hsmalli
  have hlogQ := Real.log_le_log (show (0 : ℝ) < Q i by exact_mod_cast (show 0 < Q i by omega)) hQL
  have hGram : (1 + Real.log (Q i)) ^ 2 ≤ (1 + Real.log (Real.log (N i))) ^ 2 :=
    pow_le_pow_left₀ (by linarith only [Real.log_natCast_nonneg (Q i)])
      (add_le_add le_rfl hlogQ) 2
  have heL : Real.log (N i) ^ (1 / 2 : ℝ) * Real.log (N i) =
      Real.log (N i) ^ (3 / 2 : ℝ) := by
    rw [show (3 / 2 : ℝ) = 1 / 2 + 1 by norm_num, Real.rpow_add hL0, Real.rpow_one]
  have hfirst : (Q i : ℝ) ^ 5 * c (N i) / Real.log (N i) ≤
      Real.log (N i) ^ (1 / 4 : ℝ) * c (N i) / Real.log (N i) :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hQ5 hc0) hL0.le
  have hsecond : (Q i : ℝ) ^ 11 * c (N i) ^ 5 * Real.log (N i) / N i ≤
      Real.log (N i) ^ (3 / 2 : ℝ) * c (N i) ^ 5 / N i := by
    refine (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hQ11 (pow_nonneg hc0 5)) hL0.le)
      (Nat.cast_nonneg (N i))).trans_eq ?_
    rw [mul_right_comm, heL]
  have hbracket : A * ((Q i : ℝ) ^ 5 * c (N i) / Real.log (N i) +
      (Q i : ℝ) ^ 11 * c (N i) ^ 5 * Real.log (N i) / N i) +
      9 * D * (1 + Real.log (Q i)) ^ 2 / Real.log (N i) ≤ G (N i) := by
    exact (add_le_add (mul_le_mul_of_nonneg_left (add_le_add hfirst hsecond) hA.le)
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hGram (by positivity)) hL0.le)).trans_eq
        (by dsimp only [G]; ring)
  have hZ : 0 ≤ P i ^ 2 + V (Q i) := by dsimp only [V]; positivity
  have he := hb hQi hQ2 hframe hc hrad hc4 t
  rw [Real.norm_eq_abs]
  refine he.trans ?_
  exact (add_le_add_left (mul_le_mul_of_nonneg_right hbracket hZ) _).trans_eq
    (by dsimp only [P, V, T, D]; ring)

#print axioms tendsto_harmonicPrimeCharge_energy_small_cutoff

end GaloisForLFunctions.CriticalScaleArithmeticRigidity
