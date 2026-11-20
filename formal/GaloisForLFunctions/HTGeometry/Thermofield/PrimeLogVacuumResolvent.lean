import GaloisForLFunctions.HTGeometry.PrimeLogKMSRealization
import Mathlib.Analysis.Real.Sqrt

/-!
# Resolvent estimation of the thermofield vacuum

The squared-resolvent pole mechanism of Han, Lee and Lim (arXiv:2611.04410,
§§3 and 5) gives the vacuum pole with coefficient equal to its Gibbs weight.
Every excited level is at least `log 2` away. This bounds the regular part
and gives a cubic error for a calibrated vacuum estimator.
-/

open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry.Thermofield

open _root_.HTGeometry

noncomputable section

private abbrev Distance := Set.Ioi (0 : ℝ)

private abbrev weight (P : Finset Nat.Primes) (β : ℝ) :=
  finiteGibbsStateWeight β (primeLogKMSFiniteEnergy P)

/-- Squared resolvent norm in the Gibbs spectral state, evaluated below the vacuum. -/
def primeLogVacuumResolventEnergy (P : Finset Nat.Primes) (β : ℝ) (d : Distance) : ℝ :=
  ∑ i, weight P β i / (primeLogKMSFiniteEnergy P i + (d : ℝ)) ^ 2

/-- Contributions from excited levels to the squared resolvent norm. -/
def primeLogVacuumResolventRemainder (P : Finset Nat.Primes) (β : ℝ) (d : Distance) : ℝ :=
  ∑ p : P, weight P β (some p) / (primeLogSupport p.1 + (d : ℝ)) ^ 2

/-- The pole coefficient is the actual Gibbs probability of the vacuum. -/
theorem primeLogVacuumResolventEnergy_split (P : Finset Nat.Primes) (β : ℝ) (d : Distance) :
    primeLogVacuumResolventEnergy P β d =
      weight P β none / (d : ℝ) ^ 2 + primeLogVacuumResolventRemainder P β d := by
  rw [primeLogVacuumResolventEnergy, Fintype.sum_option]
  simp only [primeLogKMSFiniteEnergy, zero_add, primeLogVacuumResolventRemainder]

/-- The regular part is bounded by the excited Gibbs mass divided by the square
of its distance from the probe. -/
theorem primeLogVacuumResolventRemainder_bounds (P : Finset Nat.Primes) (β : ℝ)
    (d : Distance) :
    0 ≤ primeLogVacuumResolventRemainder P β d ∧
      primeLogVacuumResolventRemainder P β d ≤
        (1 - weight P β none) / (Real.log 2 + (d : ℝ)) ^ 2 := by
  have hd : 0 < (d : ℝ) := d.2
  have hg : 0 < Real.log 2 + (d : ℝ) := add_pos (Real.log_pos one_lt_two) hd
  have hw := sum_finiteGibbsStateWeight_eq_one β (primeLogKMSFiniteEnergy P)
  rw [Fintype.sum_option] at hw
  have hsum : (∑ p : P, weight P β (some p)) = 1 - weight P β none := by
    linarith only [hw]
  unfold primeLogVacuumResolventRemainder
  refine ⟨Finset.sum_nonneg fun p _ => div_nonneg (finiteGibbsStateWeight_pos _ _ _).le
    (sq_nonneg _), ?_⟩
  rw [← hsum, Finset.sum_div]
  refine Finset.sum_le_sum fun p _ => ?_
  have hpn : (2 : ℝ) ≤ (p.1 : ℕ) := by exact_mod_cast p.1.2.two_le
  have hl : Real.log 2 ≤ primeLogSupport p.1 :=
    Real.strictMonoOn_log.monotoneOn
      (Set.mem_Ioi.mpr (show (0 : ℝ) < 2 from zero_lt_two))
      (Set.mem_Ioi.mpr ((show (0 : ℝ) < 2 from zero_lt_two).trans_le hpn)) hpn
  have hle := add_le_add hl (le_refl (d : ℝ))
  exact div_le_div_of_nonneg_left (finiteGibbsStateWeight_pos _ _ _).le (sq_pos_of_pos hg)
    ((sq_le_sq₀ hg.le (hg.le.trans hle)).mpr hle)

/-- Distance inferred from the squared resolvent using a calibrated vacuum weight. -/
def primeLogVacuumDistanceEstimate (P : Finset Nat.Primes) (β : ℝ) (d : Distance) : ℝ :=
  Real.sqrt (weight P β none / primeLogVacuumResolventEnergy P β d)

/-- The excited modes shift the calibrated estimate downward by at most a cubic
error, with a constant determined by the measured Gibbs mass and spectral gap. -/
theorem primeLogVacuumDistanceEstimate_error (P : Finset Nat.Primes) (β : ℝ) (d : Distance) :
    0 ≤ (d : ℝ) - primeLogVacuumDistanceEstimate P β d ∧
      (d : ℝ) - primeLogVacuumDistanceEstimate P β d ≤
        (d : ℝ) ^ 3 * (1 - weight P β none) /
          (2 * weight P β none * (Real.log 2 + (d : ℝ)) ^ 2) := by
  let w := weight P β none
  let r := primeLogVacuumResolventRemainder P β d
  let u := (d : ℝ) ^ 2 * r / w
  let q := Real.sqrt (1 + u)
  have hd : 0 < (d : ℝ) := d.2
  have hw : 0 < w := finiteGibbsStateWeight_pos _ _ _
  obtain ⟨hr, hru⟩ := primeLogVacuumResolventRemainder_bounds P β d
  have hu : 0 ≤ u := div_nonneg (mul_nonneg (sq_nonneg _) hr) hw.le
  have hq : 1 ≤ q := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt (show 1 ≤ 1 + u by linarith)
  have hqpos : 0 < q := zero_lt_one.trans_le hq
  have hsq : q ^ 2 = 1 + u := Real.sq_sqrt (by linarith)
  have hJ : primeLogVacuumResolventEnergy P β d = w / (d : ℝ) ^ 2 * q ^ 2 := by
    rw [primeLogVacuumResolventEnergy_split]
    change w / (d : ℝ) ^ 2 + r = w / (d : ℝ) ^ 2 * q ^ 2
    rw [hsq]
    dsimp only [u]
    field_simp [hw.ne', hd.ne'] <;> ring
  have hest : primeLogVacuumDistanceEstimate P β d = (d : ℝ) / q := by
    rw [primeLogVacuumDistanceEstimate, hJ,
      show weight P β none / (w / (d : ℝ) ^ 2 * q ^ 2) = ((d : ℝ) / q) ^ 2 by
        change w / (w / (d : ℝ) ^ 2 * q ^ 2) = _
        field_simp [hw.ne', hd.ne', hqpos.ne'],
      Real.sqrt_sq (div_nonneg hd.le hqpos.le)]
  have herr : (d : ℝ) - (d : ℝ) / q = (d : ℝ) * u / (q * (q + 1)) := by
    rw [show u = q ^ 2 - 1 by linarith only [hsq]]
    field_simp [hqpos.ne', (by positivity : 0 < q + 1).ne'] <;> ring
  have hlarge : 2 ≤ q * (q + 1) := by
    have hl := mul_le_mul hq (add_le_add hq (le_refl (1 : ℝ)))
      (by positivity : 0 ≤ (1 : ℝ) + 1) hqpos.le
    linarith only [hl]
  rw [hest, herr]
  refine ⟨by positivity, ?_⟩
  calc
    _ ≤ (d : ℝ) * u / 2 :=
      div_le_div_of_nonneg_left (mul_nonneg hd.le hu) (by norm_num) hlarge
    _ = (d : ℝ) ^ 3 * r / (2 * w) := by dsimp only [u]; ring
    _ ≤ (d : ℝ) ^ 3 * ((1 - w) / (Real.log 2 + (d : ℝ)) ^ 2) / (2 * w) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hru (pow_nonneg hd.le _))
        (by positivity)
    _ = _ := by
      change _ = (d : ℝ) ^ 3 * (1 - w) / (2 * w * (Real.log 2 + (d : ℝ)) ^ 2)
      rw [mul_div_assoc, div_div, mul_comm ((Real.log 2 + (d : ℝ)) ^ 2)]

#print axioms primeLogVacuumResolventRemainder_bounds
#print axioms primeLogVacuumDistanceEstimate_error

end

end GaloisForLFunctions.HTGeometry.Thermofield
