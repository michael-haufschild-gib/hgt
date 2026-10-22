import GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy.SignedDampingWorkOfTheMobiusEnergy
import GaloisForLFunctions.TransHorizonIncidenceMechanics.DampedMoebiusFirstMomentAndChebyshevTangentBridge

/-!
# The scalar damping work is uniformly paid away from zero

The tangent need not have bounded critical square energy. Its absolute first
pronic moment nevertheless has one bound for every horizon and every damping
above a fixed positive number. Thus subtracting the constant source changes
signed work by a paid scalar term; the remaining covariance is the open demand.
-/

open Finset RHTower
open GaloisForLFunctions.BezoutValuationIncidence
open GaloisForLFunctions.TransHorizonIncidenceMechanics

namespace GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy
noncomputable section
set_option autoImplicit false

private theorem scalar_prefix_eq (η : ℝ) (n : ℕ) :
    weightCenteredPrefix (pmPowerDampedRealWeight η) (dampedDensity η) n =
      pmPowerDampedCenteredDivisorPrefix η n := by
  rw [weightCenteredPrefix, pmPowerDampedCenteredDivisorPrefix_eq]
  rfl

/-- The actual tangent is the negated centered logarithmic Möbius row. -/
theorem dampedChebyshevError_eq_neg_logPrefix {η : ℝ} (hη : 0 < η) (n : ℕ) :
    dampedChebyshevError η n =
      -weightCenteredPrefix (logWeight (pmPowerDampedRealWeight η))
        (∑' d : ℕ, logWeight (pmPowerDampedRealWeight η) d / d) n := by
  have h := hasDerivAt_weightCenteredPrefix_pmPowerDamped hη n
  simp_rw [scalar_prefix_eq] at h
  exact (hasDerivAt_pmPowerDampedCenteredDivisorPrefix hη n).unique h

private theorem scalar_uniform_class {a η : ℝ} (haη : a ≤ η) :
    DampedClass 1 a (pmPowerDampedRealWeight η) := by
  intro d
  by_cases hd : d = 0
  · subst d
    simp [pmPowerDampedRealWeight, moebiusReal]
  · have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hd
    exact (pmPowerDampedRealWeight_mem_dampedClass η d).trans
      (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hd1 (neg_le_neg haη)) zero_le_one)

private theorem scalar_cell_bound {a η : ℝ} (ha : 0 < a) (ha1 : a ≤ 1)
    (haη : a ≤ η) {n : ℕ} (hn : 1 ≤ n) :
    |dampedChebyshevError η n| / ((n : ℝ) * ((n : ℝ) + 1)) ≤
      ((2 / a) * (1 + 1 / (1 - a / 2) + 1 / (a / 2))) *
        (n : ℝ) ^ (-1 - a / 2) := by
  have hα : 0 < a / 2 := by linarith
  have hα1 : a / 2 < 1 := by linarith
  have hclass := logWeight_mem_dampedClass ha (scalar_uniform_class haη)
  simp only [one_mul] at hclass
  have hp := abs_weightCenteredPrefix_le_of_dampedClass hα hα1 hclass hn
  rw [dampedChebyshevError_eq_neg_logPrefix (ha.trans_le haη), abs_neg]
  set C := (2 / a) * (1 + 1 / (1 - a / 2) + 1 / (a / 2))
  have hden : 0 < 1 - a / 2 := by linarith
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have he : (n : ℝ) ^ (1 - a / 2) =
      (n : ℝ) ^ (-1 - a / 2) * ((n : ℝ) * n) := by
    calc
      _ = (n : ℝ) ^ ((-1 - a / 2) + 2) := by congr 1; ring
      _ = _ := by rw [Real.rpow_add hn0, Real.rpow_two]; ring
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) * ((n : ℝ) + 1))).mpr
  calc
    _ ≤ C * (n : ℝ) ^ (1 - a / 2) := hp
    _ = C * (n : ℝ) ^ (-1 - a / 2) * ((n : ℝ) * n) := by rw [he]; ring
    _ ≤ C * (n : ℝ) ^ (-1 - a / 2) * ((n : ℝ) * ((n : ℝ) + 1)) := by
      gcongr
      linarith

/-- Absolute scalar tangent work has a horizon-free bound on every positive
damping half-line. This is an L¹ statement, not a critical L² estimate. -/
theorem exists_uniform_pronic_tangent_l1_bound {a : ℝ} (ha : 0 < a) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ η : ℝ, a ≤ η → ∀ T : ℕ,
      (∑ n ∈ Icc 1 T, |dampedChebyshevError η n| /
        ((n : ℝ) * ((n : ℝ) + 1))) ≤ K := by
  let b : ℝ := min a 1
  have hb : 0 < b := lt_min ha zero_lt_one
  have hb1 : b ≤ 1 := min_le_right _ _
  let C : ℝ := (2 / b) * (1 + 1 / (1 - b / 2) + 1 / (b / 2))
  have hden : 0 < 1 - b / 2 := by linarith
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hs : Summable (fun n : ℕ => C * (n : ℝ) ^ (-1 - b / 2)) :=
    (Real.summable_nat_rpow.mpr (by linarith : -1 - b / 2 < -1)).mul_left C
  refine ⟨∑' n : ℕ, C * (n : ℝ) ^ (-1 - b / 2),
    tsum_nonneg (fun n => mul_nonneg hC (Real.rpow_nonneg (Nat.cast_nonneg _) _)), ?_⟩
  intro η haη T
  calc
    _ ≤ ∑ n ∈ Icc 1 T, C * (n : ℝ) ^ (-1 - b / 2) := by
      apply sum_le_sum
      intro n hn
      exact scalar_cell_bound hb hb1 ((min_le_left a 1).trans haη) (mem_Icc.mp hn).1
    _ ≤ _ := hs.sum_le_tsum _ (fun n _ =>
      mul_nonneg hC (Real.rpow_nonneg (Nat.cast_nonneg _) _))

/-- The signed scalar moment is paid by the same absolute first-moment bound. -/
theorem exists_uniform_scalar_damping_work_bound {a : ℝ} (ha : 0 < a) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ η : ℝ, a ≤ η → ∀ T : ℕ,
      |∑ n ∈ Icc 1 T, dampedChebyshevError η n /
        ((n : ℝ) * ((n : ℝ) + 1))| ≤ K := by
  obtain ⟨K, hK, h⟩ := exists_uniform_pronic_tangent_l1_bound ha
  refine ⟨K, hK, fun η hη T => (abs_sum_le_sum_abs _ _).trans ?_⟩
  calc
    _ = ∑ n ∈ Icc 1 T, |dampedChebyshevError η n| /
        ((n : ℝ) * ((n : ℝ) + 1)) := by
      apply sum_congr rfl
      intro n _
      rw [abs_div, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ) * ((n : ℝ) + 1))]
    _ ≤ K := h η hη T

end
end GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy
