import GaloisForLFunctions.CriticalScaleArithmeticRigidity.VanishingEnergyCharge
import GaloisForLFunctions.CriticalScaleArithmeticRigidity.AdjunctionResidualCoercivity

/-!
# Source charge survives vanishing physical input

For horizons above the conductor cutoff, harmonic packet sampling costs
an absolute multiple of coefficient mass. The normalized coherent prime
family consequently has vanishing physical input and nonconstant output,
while retaining any prescribed constant generator charge. Harmonic pole
projection preserves the charge and contracts the input square.
-/

noncomputable section

open Finset Filter Topology
open scoped Classical

namespace GaloisForLFunctions.CriticalScaleArithmeticRigidity

open SelectiveMultiscaleArithmeticPositivity SuccessorShellArithmetic
  ArithmeticIntersectionTheory

private theorem log_horizon_pos {Q N : ℕ} (hQ : 2 ≤ Q) (hQN : Q ≤ N) :
    0 < Real.log (N : ℝ) :=
  Real.log_pos (by exact_mod_cast (show 1 < N by omega))

/-- Above the conductor cutoff, normalized harmonic sampling has an absolute mass bound. -/
theorem harmonicPacket_sq_div_log_le_mass {Q N : ℕ}
    (hQ : 2 ≤ Q) (hQN : Q ≤ N) (a : ℕ → ℝ) :
    (∑ n ∈ Icc 1 N, normalizedConductorPacket Q a n ^ 2 / (n : ℝ)) / Real.log N ≤
      52 * ∑ m ∈ Icc 1 Q, a m ^ 2 := by
  have hL := log_horizon_pos hQ hQN
  have hQNlog : Real.log (Q : ℝ) ≤ Real.log (N : ℝ) :=
    Real.log_le_log (by exact_mod_cast (show 0 < Q by omega)) (by exact_mod_cast hQN)
  have hQlog : Real.log 2 ≤ Real.log (Q : ℝ) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hQ)
  have hfactor : Real.log N + 17 * (1 + Real.log Q) ≤ 52 * Real.log N := by
    linarith only [hQNlog, hQlog, Real.log_two_gt_d9]
  have hmass : 0 ≤ ∑ m ∈ Icc 1 Q, a m ^ 2 := sum_nonneg fun _ _ => sq_nonneg _
  have h := harmonicConductorPacket_le_log hQ N a
  change (∑ n ∈ Icc 1 N, normalizedConductorPacket Q a n ^ 2 / (n : ℝ)) ≤ _ at h
  calc
    _ ≤ ((Real.log N + 17 * (1 + Real.log Q)) * ∑ m ∈ Icc 1 Q, a m ^ 2) /
        Real.log N := div_le_div_of_nonneg_right h hL.le
    _ = ((Real.log N + 17 * (1 + Real.log Q)) / Real.log N) *
        ∑ m ∈ Icc 1 Q, a m ^ 2 := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right ((div_le_iff₀ hL).mpr hfactor) hmass

private theorem removeConstantConductor_primeOnly (a : ℕ → ℝ) :
    removeConstantConductor (primeOnly a) = primeOnly a := by
  funext m
  by_cases hm : m = 1
  · subst m
    simp [removeConstantConductor, primeOnly]
  · simp only [removeConstantConductor, if_neg hm]

/-- The physical harmonic projection contracts the square of a conductor packet. -/
theorem harmonicCentered_profile_sq_le {Q N : ℕ}
    (hQ : 1 ≤ Q) (hN : 1 ≤ N) (a : ℕ → ℝ) :
    (∑ n ∈ Icc 1 N, conductorHorizonProfile Q (harmonicCenteredCoefficients Q N a) n ^ 2) ≤
      ∑ n ∈ Icc 1 N, conductorHorizonProfile Q a n ^ 2 := by
  simp only [conductorHorizonProfile_harmonicCentered hQ]
  rw [sum_sq_poleProj hN]
  exact sub_le_self _ (div_nonneg (sq_nonneg _) (harmonicMass_pos hN).le)

/-- Prime input has small physical norm after literal harmonic pole removal. -/
theorem harmonicCentered_prime_input_sq_le {Q N : ℕ}
    (hQ : 2 ≤ Q) (hQN : Q ≤ N) (a : ℕ → ℝ) :
    (∑ n ∈ Icc 1 N,
      conductorHorizonProfile Q (harmonicCenteredCoefficients Q N (primeOnly a)) n ^ 2) /
        Real.log N ≤ (26 / Real.log 2) * primeAdjunctionMass Q (primeOnly a) := by
  have hL := log_horizon_pos hQ hQN
  have htwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hproj := harmonicCentered_profile_sq_le (by omega : 1 ≤ Q)
    (by omega : 1 ≤ N) (primeOnly a)
  have hmass := coefficient_mass_le_adjunction_gap Q (primeOnly a)
  rw [removeConstantConductor_primeOnly] at hmass
  have hbound := harmonicPacket_sq_div_log_le_mass hQ hQN (primeOnly a)
  have hprofile : (∑ n ∈ Icc 1 N, conductorHorizonProfile Q (primeOnly a) n ^ 2) =
      ∑ n ∈ Icc 1 N, normalizedConductorPacket Q (primeOnly a) n ^ 2 / (n : ℝ) := by
    simp only [conductorHorizonProfile, div_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
  rw [hprofile] at hproj
  refine ((div_le_div_of_nonneg_right hproj hL.le).trans hbound).trans ?_
  calc
    _ = (26 / Real.log 2) * ((2 * Real.log 2) *
        ∑ m ∈ Icc 1 Q, primeOnly a m ^ 2) := by field_simp [htwo.ne']; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hmass (div_nonneg (by norm_num) htwo.le)

/-- The sharp centered prime-sector bound transfers uniformly to every physical horizon `N≥Q`. -/
theorem primeCenteredGenerator_harmonic_sq_le {Q N : ℕ}
    (hQ : 2 ≤ Q) (hQN : Q ≤ N) (a : ℕ → ℝ) :
    (∑ n ∈ Icc 1 N,
      (arithmeticPrimeGenerator Q (primeOnly a) n - primePoleResponse Q a) ^ 2 / (n : ℝ)) /
        Real.log N ≤ (26 * Real.log 2) * primeAdjunctionMass Q (primeOnly a) := by
  let b : ℕ → ℝ := primeOnly (fun p => tameDifferent p * a p)
  have heq (n : ℕ) :
      (arithmeticPrimeGenerator Q (primeOnly a) n - primePoleResponse Q a) ^ 2 =
        normalizedConductorPacket Q b n ^ 2 := by
    rw [arithmeticPrimeGenerator_primeOnly_decomposition]
    dsimp only [b]
    ring
  have hmass : (∑ m ∈ Icc 1 Q, b m ^ 2) =
      packetMean Q (fun n =>
        (arithmeticPrimeGenerator Q (primeOnly a) n - primePoleResponse Q a) ^ 2) := by
    simp only [heq, packetMean_normalizedPacket_sq]
  simp only [heq]
  have h := harmonicPacket_sq_div_log_le_mass hQ hQN b
  rw [hmass] at h
  have hcenter := mul_le_mul_of_nonneg_left (primeCenteredGenerator_period_sq_le Q a)
    (by norm_num : (0 : ℝ) ≤ 52)
  exact h.trans (hcenter.trans_eq (by ring))

/-- Arbitrary receiving charge survives vanishing energy and vanishing physical input,
uniformly over every horizon above the chosen conductor cutoff. -/
theorem exists_harmonic_neutral_physical_vanishing_charge
    (R : ℕ) (t : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ Q : ℕ, R ≤ Q ∧ 2 ≤ Q ∧ ∀ N : ℕ, Q ≤ N → ∃ a : ℕ → ℝ,
      harmonicSum N (conductorHorizonProfile Q a) = 0 ∧
      primeAdjunctionMass Q a < ε ∧
      packetMean Q (arithmeticPrimeGenerator Q a) = t ∧
      (∑ n ∈ Icc 1 N, conductorHorizonProfile Q a n ^ 2) / Real.log N < ε ∧
      (∑ n ∈ Icc 1 N, (arithmeticPrimeGenerator Q a n - t) ^ 2 / (n : ℝ)) /
        Real.log N < ε := by
  let u : ℝ := 26 / Real.log 2
  let v : ℝ := 26 * Real.log 2
  have htwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hu : 0 ≤ u := div_nonneg (by norm_num) htwo.le
  have hv : 0 ≤ v := mul_nonneg (by norm_num) htwo.le
  have hlarge := (tendsto_atTop.mp primePoleScale_tendsto_atTop)
    ((1 + u + v) * t ^ 2 / ε + 1)
  obtain ⟨Q, hQR, hQ2, hBlarge⟩ :=
    ((eventually_ge_atTop R).and ((eventually_ge_atTop 2).and hlarge)).exists
  have hB := primePoleScale_pos hQ2
  let b : ℕ → ℝ := fun p => (t / primePoleScale Q) * primePoleWitness p
  have hb := normalizedPrimeCharge_response_and_energy hQ2 t
  have hsmall : (1 + u + v) * (t ^ 2 / primePoleScale Q) < ε := by
    have hmul := mul_le_mul_of_nonneg_right hBlarge hε.le
    rw [add_mul, div_mul_cancel₀ _ hε.ne', one_mul] at hmul
    rw [← mul_div_assoc, div_lt_iff₀ hB]
    nlinarith only [hmul, hε]
  have hz : 0 ≤ t ^ 2 / primePoleScale Q := div_nonneg (sq_nonneg _) hB.le
  have huL := mul_nonneg hu hz
  have hvL := mul_nonneg hv hz
  have henergy : t ^ 2 / primePoleScale Q < ε := by
    nlinarith only [hsmall, huL, hvL]
  have hinput : u * (t ^ 2 / primePoleScale Q) < ε := by
    nlinarith only [hsmall, hz, hvL]
  have houtput : v * (t ^ 2 / primePoleScale Q) < ε := by
    nlinarith only [hsmall, hz, huL]
  refine ⟨Q, hQR, hQ2, ?_⟩
  intro N hQN
  refine ⟨harmonicCenteredCoefficients Q N (primeOnly b),
    harmonicSum_centeredCoefficients (by omega : 1 ≤ Q) (by omega : 1 ≤ N) _, ?_, ?_, ?_, ?_⟩
  · rw [primeAdjunctionMass_harmonicCentered]
    exact hb.2.trans_lt henergy
  · change packetMean Q (fun n => arithmeticPrimeGenerator Q
      (harmonicCenteredCoefficients Q N (primeOnly b)) n) = t
    simp only [arithmeticPrimeGenerator_harmonicCentered]
    rw [packetMean_arithmeticPrimeGenerator_primeOnly]
    exact hb.1
  · have h := harmonicCentered_prime_input_sq_le hQ2 hQN b
    rw [show primeAdjunctionMass Q (primeOnly b) = t ^ 2 / primePoleScale Q from hb.2] at h
    exact h.trans_lt hinput
  · simp only [arithmeticPrimeGenerator_harmonicCentered]
    have h := primeCenteredGenerator_harmonic_sq_le hQ2 hQN b
    rw [show primePoleResponse Q b = t from hb.1,
      show primeAdjunctionMass Q (primeOnly b) = t ^ 2 / primePoleScale Q from hb.2] at h
    exact h.trans_lt houtput

#print axioms harmonicPacket_sq_div_log_le_mass
#print axioms harmonicCentered_prime_input_sq_le
#print axioms primeCenteredGenerator_harmonic_sq_le
#print axioms exists_harmonic_neutral_physical_vanishing_charge

end GaloisForLFunctions.CriticalScaleArithmeticRigidity
