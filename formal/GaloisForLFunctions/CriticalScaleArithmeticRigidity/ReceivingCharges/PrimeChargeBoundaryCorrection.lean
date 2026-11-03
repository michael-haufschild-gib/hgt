import GaloisForLFunctions.CriticalScaleArithmeticRigidity.ReceivingCharges.FiniteHorizonPrimeCharge
import GaloisForLFunctions.RHTower.RegularizedDivisorHarmonicLimit

/-!
# The finite boundary correction of coherent prime charge

Subtracting the logarithmic adjunction term from dilation energy leaves
`−t²/2`. The remainder is uniform over every horizon above the prime cutoff.
The factor one half comes from the triangular sum of cumulative prime weights.
-/

noncomputable section

open Finset Filter Topology
open scoped Classical

namespace GaloisForLFunctions.CriticalScaleArithmeticRigidity

open ArithmeticCouplingTheory SelectiveMultiscaleArithmeticPositivity

private theorem cumulative_square (w : ℕ → ℝ) (Q : ℕ) :
    2 * (∑ p ∈ Icc 1 Q, w p * ∑ q ∈ Icc 1 p, w q) =
      (∑ p ∈ Icc 1 Q, w p) ^ 2 + ∑ p ∈ Icc 1 Q, w p ^ 2 := by
  induction Q with
  | zero => simp
  | succ Q ih =>
    rw [sum_Icc_succ_top (by omega), sum_Icc_succ_top (by omega),
      sum_Icc_succ_top (by omega)]
    nlinarith only [ih]

/-- The cumulative prime weights fill one triangle, including its diagonal. -/
theorem primePoleScale_triangular (Q : ℕ) :
    2 * (∑ p ∈ (Icc 1 Q).filter Nat.Prime,
      (Real.log p / p) * primePoleScale p) =
      primePoleScale Q ^ 2 +
        ∑ p ∈ (Icc 1 Q).filter Nat.Prime, (Real.log p / p) ^ 2 := by
  have h := cumulative_square
    (fun p => if p.Prime then Real.log p / (p : ℝ) else 0) Q
  simpa only [primePoleScale, sum_filter, ite_mul, zero_mul,
    ite_pow, zero_pow two_ne_zero] using h

/-- The exact cofactor boundary after removing half the squared charge. -/
def primeChargeBoundaryError (Q N : ℕ) : ℝ :=
  (∑ p ∈ (Icc 1 Q).filter Nat.Prime, (Real.log p / p) *
    (harmonicMass (N / p) - Real.log N + primePoleScale p)) -
      (1 / 2) * ∑ p ∈ (Icc 1 Q).filter Nat.Prime, (Real.log p / p) ^ 2

/-- Exact signed boundary decomposition, before taking any energy limit. -/
theorem harmonicPrimeCharge_jumpEnergy_boundary {Q : ℕ} (hQ : 2 ≤ Q)
    (N : ℕ) (t : ℝ) :
    jumpEnergy N (normalizedConductorPacket Q (harmonicPrimeChargeCoefficients Q N t)) -
        (t ^ 2 / primePoleScale Q) * Real.log N + t ^ 2 / 2 =
      (t / primePoleScale Q) ^ 2 * primeChargeBoundaryError Q N := by
  rw [harmonicPrimeCharge_jumpEnergy (by omega : 1 ≤ Q)]
  have htri := primePoleScale_triangular Q
  have hexp : primeChargeBoundaryError Q N =
      (∑ p ∈ (Icc 1 Q).filter Nat.Prime, Real.log p / p * harmonicMass (N / p)) -
        primePoleScale Q * Real.log N + primePoleScale Q ^ 2 / 2 := by
    unfold primeChargeBoundaryError
    simp only [mul_add, mul_sub, sum_add_distrib, sum_sub_distrib, ← sum_mul]
    change _ - primePoleScale Q * Real.log N + _ - _ = _
    linarith only [htri]
  rw [hexp]
  field_simp [(primePoleScale_pos hQ).ne']

private def mertensBound : ℝ :=
  (Real.log 4 + 4) + (8 + _root_.RHTower.Mertens.mertensTail)

/-- An absolute constant for the uniform finite-horizon boundary remainder. -/
def primeChargeBoundaryConstant : ℝ :=
  4 + |Real.eulerMascheroniConstant| + mertensBound + 1 / 2

private theorem cofactor_boundary_le {N p : ℕ} (hp : 1 ≤ p) (hpN : p ≤ N) :
    |harmonicMass (N / p) - Real.log N + primePoleScale p| ≤
      4 + |Real.eulerMascheroniConstant| + mertensBound := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hNR : (0 : ℝ) < N := by exact_mod_cast hp.trans hpN
  have hH := _root_.RHTower.RegularizedDivisorHarmonic.abs_harmonic_sub_log_div_le hp hpN
  have hcast : (harmonic (N / p) : ℝ) = harmonicMass (N / p) := by
    simpa only [harmonicMass, one_div] using
      _root_.RHTower.RegularizedDivisorHarmonic.harmonic_cast_eq_sum (N / p)
  rw [hcast, Real.log_div hNR.ne' hpR.ne'] at hH
  have hfour : 4 * (p : ℝ) / N ≤ 4 := by
    rw [div_le_iff₀ hNR]
    have : (p : ℝ) ≤ N := by exact_mod_cast hpN
    linarith only [this]
  have hB := primePoleScale_logarithmic hp
  have heq : harmonicMass (N / p) - Real.log N + primePoleScale p =
      (harmonicMass (N / p) - (Real.log N - Real.log p) - Real.eulerMascheroniConstant) +
        Real.eulerMascheroniConstant + (primePoleScale p - Real.log p) := by ring
  rw [heq]
  calc
    _ ≤ |harmonicMass (N / p) - (Real.log N - Real.log p) -
          Real.eulerMascheroniConstant + Real.eulerMascheroniConstant| +
        |primePoleScale p - Real.log p| := abs_add_le _ _
    _ ≤ (|harmonicMass (N / p) - (Real.log N - Real.log p) -
          Real.eulerMascheroniConstant| + |Real.eulerMascheroniConstant|) +
        |primePoleScale p - Real.log p| :=
      add_le_add (abs_add_le _ _) le_rfl
    _ ≤ _ := add_le_add (add_le_add (hH.trans hfour) le_rfl) hB

private theorem prime_weight_bounds {p : ℕ} (hp : 1 ≤ p) :
    0 ≤ Real.log p / (p : ℝ) ∧ Real.log p / (p : ℝ) ≤ 1 := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  refine ⟨div_nonneg (Real.log_natCast_nonneg _) hpR.le, ?_⟩
  rw [div_le_one hpR]
  exact (Real.log_le_sub_one_of_pos hpR).trans (sub_le_self _ zero_le_one)

/-- The boundary remainder costs only one prime Mertens mass. -/
theorem abs_primeChargeBoundaryError_le {Q N : ℕ} (hQN : Q ≤ N) :
    |primeChargeBoundaryError Q N| ≤ primeChargeBoundaryConstant * primePoleScale Q := by
  let P := (Icc 1 Q).filter Nat.Prime
  have hterm (p : ℕ) (hp : p ∈ P) :
      |(Real.log p / p) * (harmonicMass (N / p) - Real.log N + primePoleScale p)| ≤
        (Real.log p / p) * (4 + |Real.eulerMascheroniConstant| + mertensBound) := by
    have hp1 := (mem_Icc.mp (mem_filter.mp hp).1).1
    rw [abs_mul, abs_of_nonneg (prime_weight_bounds hp1).1]
    exact mul_le_mul_of_nonneg_left
      (cofactor_boundary_le hp1 ((mem_Icc.mp (mem_filter.mp hp).1).2.trans hQN))
      (prime_weight_bounds hp1).1
  have hsq : (∑ p ∈ P, (Real.log p / p) ^ 2) ≤ primePoleScale Q := by
    apply sum_le_sum
    intro p hp
    obtain ⟨h0, h1⟩ := prime_weight_bounds (mem_Icc.mp (mem_filter.mp hp).1).1
    nlinarith only [h0, h1]
  have hsq0 : 0 ≤ ∑ p ∈ P, (Real.log p / p) ^ 2 := sum_nonneg fun _ _ => sq_nonneg _
  calc
    |primeChargeBoundaryError Q N| ≤
        |∑ p ∈ P, (Real.log p / p) *
          (harmonicMass (N / p) - Real.log N + primePoleScale p)| +
        (1 / 2) * (∑ p ∈ P, (Real.log p / p) ^ 2) := by
      have h := abs_sub (∑ p ∈ P, (Real.log p / p) *
            (harmonicMass (N / p) - Real.log N + primePoleScale p))
            ((1 / 2) * ∑ p ∈ P, (Real.log p / p) ^ 2)
      rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2),
        abs_of_nonneg hsq0] at h
      exact h
    _ ≤ (∑ p ∈ P, (Real.log p / p) *
        (4 + |Real.eulerMascheroniConstant| + mertensBound)) +
        (1 / 2) * primePoleScale Q :=
      add_le_add ((abs_sum_le_sum_abs _ _).trans (sum_le_sum hterm))
        (mul_le_mul_of_nonneg_left hsq (by norm_num))
    _ = primeChargeBoundaryConstant * primePoleScale Q := by
      rw [← sum_mul]
      change primePoleScale Q * _ + _ = _
      unfold primeChargeBoundaryConstant
      ring

/-- The renormalized dilation energy has a uniform signed half-charge remainder. -/
theorem harmonicPrimeCharge_boundary_error_le {Q N : ℕ}
    (hQ : 2 ≤ Q) (hQN : Q ≤ N) (t : ℝ) :
    |jumpEnergy N (normalizedConductorPacket Q (harmonicPrimeChargeCoefficients Q N t)) -
        (t ^ 2 / primePoleScale Q) * Real.log N + t ^ 2 / 2| ≤
      primeChargeBoundaryConstant * t ^ 2 / primePoleScale Q := by
  rw [harmonicPrimeCharge_jumpEnergy_boundary hQ, abs_mul,
    abs_of_nonneg (sq_nonneg _)]
  calc
    _ ≤ (t / primePoleScale Q) ^ 2 *
        (primeChargeBoundaryConstant * primePoleScale Q) :=
      mul_le_mul_of_nonneg_left (abs_primeChargeBoundaryError_le hQN) (sq_nonneg _)
    _ = _ := by field_simp [(primePoleScale_pos hQ).ne']

/-- Every choice of horizons above the cutoff has the same boundary correction. -/
theorem tendsto_harmonicPrimeCharge_boundary (H : ℕ → ℕ) (t : ℝ) :
    Tendsto (fun Q =>
      jumpEnergy (Q + H Q) (normalizedConductorPacket Q
        (harmonicPrimeChargeCoefficients Q (Q + H Q) t)) -
          (t ^ 2 / primePoleScale Q) * Real.log (Q + H Q))
      atTop (𝓝 (-(t ^ 2 / 2))) := by
  rw [← tendsto_sub_nhds_zero_iff]
  refine squeeze_zero_norm' ?_
    (primePoleScale_tendsto_atTop.const_div_atTop (primeChargeBoundaryConstant * t ^ 2))
  filter_upwards [eventually_ge_atTop 2] with Q hQ
  simpa only [Real.norm_eq_abs, sub_neg_eq_add, Nat.cast_add] using
    harmonicPrimeCharge_boundary_error_le hQ (Nat.le_add_right Q (H Q)) t

private theorem diagonal_horizon_error_le {Q : ℕ} (hQ : 2 ≤ Q) (t : ℝ) :
    |jumpEnergy Q (normalizedConductorPacket Q (harmonicPrimeChargeCoefficients Q Q t)) -
        t ^ 2 / 2| ≤
      (primeChargeBoundaryConstant + mertensBound) * t ^ 2 / primePoleScale Q := by
  have hB := primePoleScale_pos hQ
  have hM : |Real.log Q - primePoleScale Q| ≤ mertensBound := by
    rw [abs_sub_comm]
    exact primePoleScale_logarithmic (by omega)
  have heq : jumpEnergy Q
      (normalizedConductorPacket Q (harmonicPrimeChargeCoefficients Q Q t)) - t ^ 2 / 2 =
      (jumpEnergy Q (normalizedConductorPacket Q (harmonicPrimeChargeCoefficients Q Q t)) -
        (t ^ 2 / primePoleScale Q) * Real.log Q + t ^ 2 / 2) +
      (t ^ 2 / primePoleScale Q) * (Real.log Q - primePoleScale Q) := by
    field_simp [hB.ne']
    ring
  rw [heq]
  calc
    _ ≤ |jumpEnergy Q
        (normalizedConductorPacket Q (harmonicPrimeChargeCoefficients Q Q t)) -
          (t ^ 2 / primePoleScale Q) * Real.log Q + t ^ 2 / 2| +
        |(t ^ 2 / primePoleScale Q) * (Real.log Q - primePoleScale Q)| := abs_add_le _ _
    _ ≤ primeChargeBoundaryConstant * t ^ 2 / primePoleScale Q +
        (t ^ 2 / primePoleScale Q) * mertensBound := by
      refine add_le_add (harmonicPrimeCharge_boundary_error_le hQ le_rfl t) ?_
      rw [abs_mul, abs_of_nonneg (div_nonneg (sq_nonneg _) hB.le)]
      exact mul_le_mul_of_nonneg_left hM (div_nonneg (sq_nonneg _) hB.le)
    _ = _ := by ring

/-- At the cutoff horizon the dilation energy retains exactly half the squared charge. -/
theorem tendsto_harmonicPrimeCharge_cutoff_energy (t : ℝ) :
    Tendsto (fun Q => jumpEnergy Q
      (normalizedConductorPacket Q (harmonicPrimeChargeCoefficients Q Q t)))
      atTop (𝓝 (t ^ 2 / 2)) := by
  rw [← tendsto_sub_nhds_zero_iff]
  refine squeeze_zero_norm' ?_ (primePoleScale_tendsto_atTop.const_div_atTop
    ((primeChargeBoundaryConstant + mertensBound) * t ^ 2))
  filter_upwards [eventually_ge_atTop 2] with Q hQ
  simpa only [Real.norm_eq_abs] using diagonal_horizon_error_le hQ t

#print axioms harmonicPrimeCharge_jumpEnergy_boundary
#print axioms abs_primeChargeBoundaryError_le
#print axioms tendsto_harmonicPrimeCharge_boundary
#print axioms tendsto_harmonicPrimeCharge_cutoff_energy

end GaloisForLFunctions.CriticalScaleArithmeticRigidity
