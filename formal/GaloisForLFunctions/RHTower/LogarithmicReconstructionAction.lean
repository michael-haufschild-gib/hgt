import GaloisForLFunctions.RHTower.LogarithmicMobiusReconstruction

/-!
# The finite stationary action of arithmetic reconstruction

For an arbitrary source, the quadratic reconstruction action is stationary
at the actual Möbius coefficients. Its exact error is the quadratic form
of the coefficient perturbation. The form is signed; stationarity alone
does not supply a bound on its value.
-/

noncomputable section
open scoped BigOperators

namespace RHTower

theorem logarithmicWeightedDilation_add_coeff (a b : ℕ → ℝ) (f : ℝ → ℝ) (T : ℝ) :
    logarithmicWeightedDilation (fun n => a n + b n) f T =
      logarithmicWeightedDilation a f T + logarithmicWeightedDilation b f T := by
  simp only [logarithmicWeightedDilation, add_mul, Finset.sum_add_distrib]

theorem logarithmicWeightedDilation_add_profile (a : ℕ → ℝ) (f g : ℝ → ℝ) (T : ℝ) :
    logarithmicWeightedDilation a (fun t => f t + g t) T =
      logarithmicWeightedDilation a f T + logarithmicWeightedDilation a g T := by
  simp only [logarithmicWeightedDilation, mul_add, Finset.sum_add_distrib]

theorem logarithmicWeightedDilation_const_mul_coeff (c : ℝ) (a : ℕ → ℝ)
    (f : ℝ → ℝ) (T : ℝ) :
    logarithmicWeightedDilation (fun n => c * a n) f T =
      c * logarithmicWeightedDilation a f T := by
  simp only [logarithmicWeightedDilation, Finset.mul_sum, mul_assoc]

theorem logarithmicWeightedDilation_const_mul_profile (c : ℝ) (a : ℕ → ℝ)
    (f : ℝ → ℝ) (T : ℝ) :
    logarithmicWeightedDilation a (fun t => c * f t) T =
      c * logarithmicWeightedDilation a f T := by
  simp only [logarithmicWeightedDilation, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _
  ring

theorem logarithmicWeightedDilation_comm (a b : ℕ → ℝ) (f : ℝ → ℝ) (T : ℝ) :
    logarithmicWeightedDilation a (logarithmicWeightedDilation b f) T =
      logarithmicWeightedDilation b (logarithmicWeightedDilation a f) T := by
  rw [logarithmicWeightedDilation_comp, logarithmicWeightedDilation_comp]
  congr 1
  funext n
  rw [Nat.sum_divisorsAntidiagonal (fun d e => a d * b e),
    Nat.sum_divisorsAntidiagonal' (fun d e => b d * a e)]
  apply Finset.sum_congr rfl
  intro d _
  exact mul_comm _ _

theorem logarithmicWeightedDilation_mobiusInverse_dilationSum
    (a : ℕ → ℝ) (f : ℝ → ℝ) (T : ℝ) :
    logarithmicWeightedDilation a (logarithmicMobiusInverse (logarithmicDilationSum f)) T =
      logarithmicWeightedDilation a f T := by
  unfold logarithmicWeightedDilation
  apply Finset.sum_congr rfl
  intro n hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
  have hlog : Real.log n ≤ T := (Real.log_le_iff_le_exp hnpos).mpr
    ((Nat.le_floor_iff (Real.exp_pos T).le).mp (Finset.mem_Icc.mp hn).2)
  rw [logarithmicMobiusInverse_dilationSum f (sub_nonneg.mpr hlog)]

def logarithmicReconstructionAction (a : ℕ → ℝ) (f : ℝ → ℝ) (T : ℝ) : ℝ :=
  2 * logarithmicWeightedDilation a f T -
    logarithmicWeightedDilation a (logarithmicWeightedDilation a (logarithmicDilationSum f)) T

/-- Exact completion at the actual inverse, for every source and perturbation. -/
theorem logarithmicReconstructionAction_mobius_add (v : ℕ → ℝ) (f : ℝ → ℝ) (T : ℝ) :
    logarithmicReconstructionAction (fun n => (ArithmeticFunction.moebius n : ℝ) + v n) f T =
      logarithmicMobiusInverse f T -
        logarithmicWeightedDilation v (logarithmicWeightedDilation v (logarithmicDilationSum f)) T := by
  let mu := fun n => (ArithmeticFunction.moebius n : ℝ)
  have hm : logarithmicWeightedDilation mu
      (logarithmicWeightedDilation mu (logarithmicDilationSum f)) T =
        logarithmicMobiusInverse f T :=
    logarithmicWeightedDilation_mobiusInverse_dilationSum mu f T
  have hv : logarithmicWeightedDilation v
      (logarithmicWeightedDilation mu (logarithmicDilationSum f)) T =
        logarithmicWeightedDilation v f T :=
    logarithmicWeightedDilation_mobiusInverse_dilationSum v f T
  have hmv : logarithmicWeightedDilation mu
      (logarithmicWeightedDilation v (logarithmicDilationSum f)) T =
        logarithmicWeightedDilation v f T := by
    rw [logarithmicWeightedDilation_comm, hv]
  have hp : logarithmicWeightedDilation (fun n => mu n + v n) (logarithmicDilationSum f) =
      fun t => logarithmicWeightedDilation mu (logarithmicDilationSum f) t +
        logarithmicWeightedDilation v (logarithmicDilationSum f) t :=
    funext (logarithmicWeightedDilation_add_coeff mu v (logarithmicDilationSum f))
  change logarithmicReconstructionAction (fun n => mu n + v n) f T = _
  unfold logarithmicReconstructionAction
  rw [hp, logarithmicWeightedDilation_add_coeff, logarithmicWeightedDilation_add_coeff,
    logarithmicWeightedDilation_add_profile, logarithmicWeightedDilation_add_profile,
    hm, hv, hmv]
  change 2 * (logarithmicMobiusInverse f T + logarithmicWeightedDilation v f T) -
    (logarithmicMobiusInverse f T + logarithmicWeightedDilation v f T +
      (logarithmicWeightedDilation v f T +
        logarithmicWeightedDilation v (logarithmicWeightedDilation v (logarithmicDilationSum f)) T)) = _
  ring

theorem logarithmicReconstructionAction_mobius_line (v : ℕ → ℝ) (f : ℝ → ℝ) (T z : ℝ) :
    logarithmicReconstructionAction
      (fun n => (ArithmeticFunction.moebius n : ℝ) + z * v n) f T =
        logarithmicMobiusInverse f T - z ^ 2 *
          logarithmicWeightedDilation v (logarithmicWeightedDilation v (logarithmicDilationSum f)) T := by
  rw [logarithmicReconstructionAction_mobius_add]
  have hp : logarithmicWeightedDilation (fun n => z * v n) (logarithmicDilationSum f) =
      fun t => z * logarithmicWeightedDilation v (logarithmicDilationSum f) t :=
    funext (logarithmicWeightedDilation_const_mul_coeff z v (logarithmicDilationSum f))
  rw [hp, logarithmicWeightedDilation_const_mul_coeff,
    logarithmicWeightedDilation_const_mul_profile]
  ring

end RHTower
