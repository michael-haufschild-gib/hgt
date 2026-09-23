import GaloisForLFunctions.HTGeometry.GaussBonnetCoexistenceAKernelExpansion
import GaloisForLFunctions.HTGeometry.GaussBonnetCoexistenceAKernelMomentLimits

/-!
# Every critical Taylor coefficient of the actual logarithmic kernel

Finite polynomials converge monotonically from below to the actual
kernel. Each remainder is exactly a positive weighted moment times the
next even power. Its normalized critical limit gives an explicit rational
coefficient at every order.
-/
noncomputable section
open Real Filter
open scoped Topology BigOperators
namespace GaloisForLFunctions.HTGeometry

def egbCoexistenceAKernelTaylor (τ : ℝ) (n : ℕ) : ℝ :=
  3 * egbCoexistenceAKernelMomentPartialSum τ 0 (n + 1) - 1
def egbCoexistenceAKernelTaylorCoefficient (n : ℕ) : ℝ :=
  12 * ((n : ℝ) + 2) / ((2 * (n : ℝ) + 3) * (2 * (n : ℝ) + 5))

theorem egbCoexistenceAKernelTaylorCoefficient_formula (n : ℕ) :
    3 * egbCoexistenceAKernelMomentCoefficient (n + 1) = egbCoexistenceAKernelTaylorCoefficient n := by
  unfold egbCoexistenceAKernelMomentCoefficient egbCoexistenceAKernelTaylorCoefficient
  push_cast
  field_simp
  ring

theorem egbCoexistenceAKernelTaylorCoefficient_pos (n : ℕ) : 0 < egbCoexistenceAKernelTaylorCoefficient n := by
  unfold egbCoexistenceAKernelTaylorCoefficient
  positivity

theorem egbCoexistenceAKernelTaylor_zero (τ : ℝ) : egbCoexistenceAKernelTaylor τ 0 = 3 := by
  norm_num [egbCoexistenceAKernelTaylor, egbCoexistenceAKernelMomentPartialSum, egbCoexistenceAKernelMomentCoefficient]

/-- Full remainder after every even-order polynomial, not an asymptotic formal series. -/
theorem egbCoexistenceAKernelTaylor_exact_remainder (τ : ℝ) (n : ℕ) :
    egbCoexistenceALogKernel τ - egbCoexistenceAKernelTaylor τ n =
      3 * egbCoexistenceASymmetricRatio τ ^ (2 * (n + 1)) * egbCoexistenceAKernelMoment τ (n + 1) := by
  have h := egbCoexistenceAKernelMoment_exact_remainder τ 0 (n + 1)
  simp only [Nat.zero_add] at h
  rw [egbCoexistenceAKernelMoment_zero]
  unfold egbCoexistenceAKernelTaylor
  linear_combination 3 * h

theorem egbCoexistenceAKernelTaylor_strict_lower_bound (τ : ℝ) (n : ℕ) :
    egbCoexistenceAKernelTaylor τ n < egbCoexistenceALogKernel τ := by
  have h := egbCoexistenceAKernelMomentPartialSum_strict_lower_bound τ 0 (n + 1)
  rw [egbCoexistenceAKernelMoment_zero]
  unfold egbCoexistenceAKernelTaylor
  linarith

theorem egbCoexistenceAKernelTaylor_strict_step (τ : ℝ) (n : ℕ) :
    egbCoexistenceAKernelTaylor τ n < egbCoexistenceAKernelTaylor τ (n + 1) := by
  have h := egbCoexistenceAKernelMomentPartialSum_strict_step τ 0 (n + 1)
  unfold egbCoexistenceAKernelTaylor
  linarith

theorem egbCoexistenceAKernelTaylor_remainder_bounds (τ : ℝ) (n : ℕ) :
    egbCoexistenceAKernelTaylorCoefficient n * egbCoexistenceASymmetricRatio τ ^ (2 * (n + 1)) ≤
      egbCoexistenceALogKernel τ - egbCoexistenceAKernelTaylor τ n ∧
    egbCoexistenceALogKernel τ - egbCoexistenceAKernelTaylor τ n ≤
      egbCoexistenceAKernelTaylorCoefficient n * egbCoexistenceASymmetricRatio τ ^ (2 * (n + 1)) /
        (1 - egbCoexistenceASymmetricRatio τ ^ (2 : ℕ)) := by
  rw [egbCoexistenceAKernelTaylor_exact_remainder, ← egbCoexistenceAKernelTaylorCoefficient_formula]
  have hd := (egbCoexistenceASymmetricRatio_bounds τ).1
  have hp : 0 ≤ 3 * egbCoexistenceASymmetricRatio τ ^ (2 * (n + 1)) := by positivity
  have hlo := mul_le_mul_of_nonneg_left (egbCoexistenceAKernelMoment_bounds τ (n + 1)).1 hp
  have hhi := mul_le_mul_of_nonneg_left (egbCoexistenceAKernelMoment_bounds τ (n + 1)).2 hp
  constructor
  · nlinarith only [hlo]
  · calc
      _ ≤ 3 * egbCoexistenceASymmetricRatio τ ^ (2 * (n + 1)) *
          (egbCoexistenceAKernelMomentCoefficient (n + 1) / (1 - egbCoexistenceASymmetricRatio τ ^ (2 : ℕ))) := hhi
      _ = _ := by ring

theorem egbCoexistenceAKernelTaylor_normalized_remainder (τ : ℝ) (n : ℕ) :
    (egbCoexistenceALogKernel τ - egbCoexistenceAKernelTaylor τ n) / egbCoexistenceASymmetricRatio τ ^ (2 * (n + 1)) =
      3 * egbCoexistenceAKernelMoment τ (n + 1) := by
  have hd := (egbCoexistenceASymmetricRatio_bounds τ).1
  rw [egbCoexistenceAKernelTaylor_exact_remainder]
  field_simp

theorem egbCoexistenceAKernelTaylor_remainder_critical_limit (n : ℕ) :
    Tendsto (fun τ => (egbCoexistenceALogKernel τ - egbCoexistenceAKernelTaylor τ n) /
      egbCoexistenceASymmetricRatio τ ^ (2 * (n + 1))) atBot (𝓝 (egbCoexistenceAKernelTaylorCoefficient n)) := by
  simp only [egbCoexistenceAKernelTaylor_normalized_remainder]
  have h := (tendsto_const_nhds (x := (3 : ℝ))).mul (egbCoexistenceAKernelMoment_critical_limit (n + 1))
  rwa [egbCoexistenceAKernelTaylorCoefficient_formula] at h

theorem egbCoexistenceAKernelTaylor_tendsto (τ : ℝ) :
    Tendsto (egbCoexistenceAKernelTaylor τ) atTop (𝓝 (egbCoexistenceALogKernel τ)) := by
  have h := ((tendsto_const_nhds (x := (3 : ℝ))).mul
    ((egbCoexistenceAKernelMomentPartialSum_tendsto τ 0).comp (tendsto_add_atTop_nat 1))).sub
      (tendsto_const_nhds (x := (1 : ℝ)))
  rw [← egbCoexistenceAKernelMoment_zero] at h
  change Tendsto (fun n => 3 * egbCoexistenceAKernelMomentPartialSum τ 0 (n + 1) - 1) atTop (𝓝 (egbCoexistenceALogKernel τ))
  simpa only [Function.comp_def] using h

theorem egbCoexistenceALogKernel_series (τ : ℝ) :
    egbCoexistenceALogKernel τ = 3 *
      (∑' n : ℕ, egbCoexistenceAKernelMomentCoefficient n * egbCoexistenceASymmetricRatio τ ^ (2 * n)) - 1 := by
  rw [egbCoexistenceAKernelMoment_zero, ← egbCoexistenceAKernelMoment_tsum τ 0]
  simp only [Nat.zero_add]

end GaloisForLFunctions.HTGeometry
