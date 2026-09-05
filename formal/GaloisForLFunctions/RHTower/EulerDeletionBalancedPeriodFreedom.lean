import GaloisForLFunctions.RHTower.EulerDeletionFactorizationGraded
import GaloisForLFunctions.RHTower.EulerDeletionCoprimeWordPeriodicity

/-!
# Quadratic freedom on balanced arithmetic periods

The factorization-curvature coefficient has a four-channel linear normal form. Opposite
perturbations of weights on two literal copies of a period preserve all linear observations
simultaneously while changing quadratic observations by an explicit square term. A closed
sixty-integer example has positive weights, zero endpoints for every divisor of thirty, and
either sign of quadratic curvature. This is a finite countermodel to an algebraic endpoint
inference, not a model of the infinite Mellin weights or a statement about zeta zeros.
-/

noncomputable section
open scoped BigOperators
namespace RHTower.DeletionBalancedPeriods

def coefficient (d n : ℕ) : ℝ := blockDeletionCoefficient d n

def curvatureCoefficient (p q r n : ℕ) : ℝ :=
  coefficient p n * coefficient q n ^ 2 +
    coefficient (p*q) n * coefficient r n ^ 2 -
    coefficient q n * coefficient r n ^ 2 -
    coefficient p n * coefficient (q*r) n ^ 2

theorem grade_coefficient_linear {p q : ℕ} (hpq : p.Coprime q) (n : ℕ) :
    coefficient p n * coefficient q n ^ 2 =
      coefficient p n + (2 - (q : ℝ)) * coefficient q n +
        ((q : ℝ) - 2) * coefficient (p*q) n := by
  have hs : coefficient q n ^ 2 =
      (q : ℝ) - 1 + (2 - (q : ℝ)) * coefficient q n := by
    dsimp only [coefficient]
    exact_mod_cast blockDeletionCoefficient_sq_eq q n
  have hm : coefficient p n * coefficient q n =
      coefficient p n + coefficient q n - coefficient (p*q) n := by
    dsimp only [coefficient]
    exact_mod_cast blockDeletionCoefficient_mul_eq_add_sub_product_of_coprime hpq n
  rw [hs]
  calc
    _ = ((q : ℝ) - 1) * coefficient p n +
        (2 - (q : ℝ)) * (coefficient p n * coefficient q n) := by ring
    _ = _ := by rw [hm]; ring

/-- The apparent cubic curvature coefficient is a linear combination of four channels. -/
theorem curvature_coefficient_linear {p q r : ℕ}
    (hpq : p.Coprime q) (hpr : p.Coprime r) (hqr : q.Coprime r) (n : ℕ) :
    curvatureCoefficient p q r n = ((q : ℝ) - 1) *
      (coefficient (p*q) n - coefficient q n +
        (r : ℝ) * (coefficient (q*r) n - coefficient (p*q*r) n)) := by
  rw [curvatureCoefficient, grade_coefficient_linear hpq,
    grade_coefficient_linear (Nat.Coprime.mul_left hpr hqr),
    grade_coefficient_linear hqr,
    grade_coefficient_linear (Nat.Coprime.mul_right hpq hpr)]
  rw [← Nat.mul_assoc p q r]
  push_cast
  ring

theorem coefficient_periodic_of_dvd {d L : ℕ} (hd : d ∣ L) :
    Function.Periodic (coefficient d) L := by
  obtain ⟨k, rfl⟩ := hd
  intro n
  have h := (DeletionCoprimeWords.deletion_periodic d).nat_mul k n
  simpa [coefficient, Nat.mul_comm, Nat.cast_id] using congrArg (Int.cast : ℤ → ℝ) h

theorem coefficient_period_sum_zero {d L : ℕ} (hd : d ∣ L) :
    (∑ n : Fin L, coefficient d (n.val + 1)) = 0 := by
  obtain ⟨k, rfl⟩ := hd
  rw [Fin.sum_univ_eq_sum_range (fun n => coefficient d (n+1))]
  dsimp only [coefficient]
  exact_mod_cast (sum_blockDeletionCoefficient_product_block_eq_zero (p := d) (q := k))

/-- Two literal consecutive copies of a period, with opposite perturbations of their weights. -/
def linearObservation (L : ℕ) (h : Fin L → ℝ) (f : ℕ → ℝ) : ℝ :=
  ∑ n : Fin L, (f (n.val+1) * (1+h n) + f (n.val+1+L) * (1-h n))

def quadraticObservation (L : ℕ) (h : Fin L → ℝ) (f : ℕ → ℝ) : ℝ :=
  ∑ n : Fin L, (f (n.val+1) * (1+h n)^2 + f (n.val+1+L) * (1-h n)^2)

theorem linear_observation (L : ℕ) (h : Fin L → ℝ) {f : ℕ → ℝ}
    (hf : Function.Periodic f L) :
    linearObservation L h f = 2 * ∑ n : Fin L, f (n.val+1) := by
  rw [linearObservation, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _
  rw [hf (n.val+1)]
  ring

/-- Complete quadratic freedom left by the simultaneous linear endpoint constraints. -/
theorem quadratic_observation (L : ℕ) (h : Fin L → ℝ) {f : ℕ → ℝ}
    (hf : Function.Periodic f L) :
    quadraticObservation L h f =
      2 * ∑ n : Fin L, f (n.val+1) + 2 * ∑ n : Fin L, f (n.val+1) * (h n)^2 := by
  rw [quadraticObservation, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n _
  rw [hf (n.val+1)]
  ring

theorem all_divisor_endpoints_zero (L : ℕ) (h : Fin L → ℝ) :
    ∀ d, d ∣ L → linearObservation L h (coefficient d) = 0 := by
  intro d hd
  rw [linear_observation L h (coefficient_periodic_of_dvd hd),
    coefficient_period_sum_zero hd, mul_zero]

def spike {L : ℕ} (j : Fin L) (t : ℝ) (n : Fin L) : ℝ := if n = j then t else 0

theorem spike_positive {L : ℕ} (j : Fin L) {t : ℝ} (ht : |t| < 1) :
    ∀ n, 0 < 1 + spike j t n ∧ 0 < 1 - spike j t n := by
  intro n
  rcases abs_lt.mp ht with ⟨hl, hu⟩
  by_cases hn : n = j
  · simp only [spike, hn, if_true]
    constructor <;> linarith
  · simp [spike, hn]

theorem quadratic_observation_spike {L : ℕ} (j : Fin L) (t : ℝ)
    {f : ℕ → ℝ} (hf : Function.Periodic f L) :
    quadraticObservation L (spike j t) f =
      2 * ∑ n : Fin L, f (n.val+1) + 2 * t^2 * f (j.val+1) := by
  rw [quadratic_observation L (spike j t) hf]
  simp [spike, ite_pow, mul_ite]
  ring

def cellCurvature : ℕ → ℝ := curvatureCoefficient 2 3 5

theorem cell_curvature_linear (n : ℕ) :
    cellCurvature n = 2 * (coefficient 6 n - coefficient 3 n +
      5 * (coefficient 15 n - coefficient 30 n)) := by
  have h := curvature_coefficient_linear
    (p := 2) (q := 3) (r := 5) (by norm_num) (by norm_num) (by norm_num) n
  norm_num at h
  exact h

theorem cell_curvature_periodic : Function.Periodic cellCurvature 30 := by
  intro n
  rw [cell_curvature_linear, cell_curvature_linear,
    coefficient_periodic_of_dvd (by norm_num : 6 ∣ 30) n,
    coefficient_periodic_of_dvd (by norm_num : 3 ∣ 30) n,
    coefficient_periodic_of_dvd (by norm_num : 15 ∣ 30) n,
    coefficient_periodic_of_dvd (by norm_num : 30 ∣ 30) n]

theorem cell_curvature_period_sum_zero :
    (∑ n : Fin 30, cellCurvature (n.val+1)) = 0 := by
  simp_rw [cell_curvature_linear]
  rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, Finset.sum_sub_distrib,
    coefficient_period_sum_zero (by norm_num : 6 ∣ 30),
    coefficient_period_sum_zero (by norm_num : 3 ∣ 30),
    coefficient_period_sum_zero (by norm_num : 15 ∣ 30),
    coefficient_period_sum_zero (by norm_num : 30 ∣ 30)]
  ring

theorem cell_curvature_three : cellCurvature 3 = 6 := by
  rw [cell_curvature_linear]
  norm_num [coefficient, blockDeletionCoefficient]

theorem cell_curvature_six : cellCurvature 6 = -6 := by
  rw [cell_curvature_linear]
  norm_num [coefficient, blockDeletionCoefficient]

def positiveCurvatureWeights : Fin 30 → ℝ := spike ⟨2, by omega⟩ (1/2)
def negativeCurvatureWeights : Fin 30 → ℝ := spike ⟨5, by omega⟩ (1/2)

theorem positive_curvature_value :
    quadraticObservation 30 positiveCurvatureWeights cellCurvature = 3 := by
  rw [positiveCurvatureWeights, quadratic_observation_spike _ _ cell_curvature_periodic,
    cell_curvature_period_sum_zero]
  norm_num [cell_curvature_three]

theorem negative_curvature_value :
    quadraticObservation 30 negativeCurvatureWeights cellCurvature = -3 := by
  rw [negativeCurvatureWeights, quadratic_observation_spike _ _ cell_curvature_periodic,
    cell_curvature_period_sum_zero]
  norm_num [cell_curvature_six]

/-- Closed finite arithmetic countermodels: the same full divisor endpoint constraints admit
strictly positive weights with either sign of quadratic factorization curvature. -/
theorem positive_weights_closed_endpoints_opposite_curvatures :
    ∃ hPlus hMinus : Fin 30 → ℝ,
      (∀ n, 0 < 1+hPlus n ∧ 0 < 1-hPlus n) ∧
      (∀ n, 0 < 1+hMinus n ∧ 0 < 1-hMinus n) ∧
      (∀ d, d ∣ 30 → linearObservation 30 hPlus (coefficient d) = 0) ∧
      (∀ d, d ∣ 30 → linearObservation 30 hMinus (coefficient d) = 0) ∧
      quadraticObservation 30 hPlus cellCurvature = 3 ∧
      quadraticObservation 30 hMinus cellCurvature = -3 := by
  refine ⟨positiveCurvatureWeights, negativeCurvatureWeights, ?_, ?_,
    all_divisor_endpoints_zero _ _, all_divisor_endpoints_zero _ _,
    positive_curvature_value, negative_curvature_value⟩
  · exact spike_positive _ (by norm_num)
  · exact spike_positive _ (by norm_num)

end RHTower.DeletionBalancedPeriods
