import GaloisForLFunctions.HTGeometry.GaussBonnetCoexistenceAKernelMoments
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# Exact finite expansions and convergent positive series of kernel moments

Iterating the resolvent recurrence gives every finite partial sum with
its exact positive remainder. Geometric bounds prove convergence of all
these moment series. The expansion is an identity for the actual kernel,
with no numerical truncation or assumed analytic continuation.
-/
noncomputable section
open Real Filter
open scoped Topology BigOperators
namespace GaloisForLFunctions.HTGeometry

def egbCoexistenceAKernelMomentPartialSum (τ : ℝ) (j n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range n, egbCoexistenceAKernelMomentCoefficient (j + k) * egbCoexistenceASymmetricRatio τ ^ (2 * k)

theorem egbCoexistenceAKernelMomentCoefficient_upper_bound (n : ℕ) :
    egbCoexistenceAKernelMomentCoefficient n ≤ (4 : ℝ) / 3 := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have h₁ : (1 : ℝ) / (2 * (n : ℝ) + 1) ≤ 1 := by
    apply (div_le_iff₀ (by positivity)).2
    linarith
  have h₂ : (1 : ℝ) / (2 * (n : ℝ) + 3) ≤ 1 / 3 := by
    apply (div_le_div_iff₀ (by positivity) (by norm_num)).2
    linarith
  unfold egbCoexistenceAKernelMomentCoefficient
  linarith

theorem egbCoexistenceAKernelMomentPartialSum_succ (τ : ℝ) (j n : ℕ) :
    egbCoexistenceAKernelMomentPartialSum τ j (n + 1) = egbCoexistenceAKernelMomentPartialSum τ j n +
      egbCoexistenceAKernelMomentCoefficient (j + n) * egbCoexistenceASymmetricRatio τ ^ (2 * n) := by
  unfold egbCoexistenceAKernelMomentPartialSum
  rw [Finset.sum_range_succ]

/-- An exact identity for every starting moment and every finite expansion order. -/
theorem egbCoexistenceAKernelMoment_finite_expansion (τ : ℝ) (j n : ℕ) :
    egbCoexistenceAKernelMoment τ j = egbCoexistenceAKernelMomentPartialSum τ j n +
      egbCoexistenceASymmetricRatio τ ^ (2 * n) * egbCoexistenceAKernelMoment τ (j + n) := by
  induction n with
  | zero => simp [egbCoexistenceAKernelMomentPartialSum]
  | succ n ih =>
    have h := egbCoexistenceAKernelMoment_recurrence τ (j + n)
    have hm : egbCoexistenceAKernelMoment τ (j + n) = egbCoexistenceAKernelMomentCoefficient (j + n) +
        egbCoexistenceASymmetricRatio τ ^ 2 * egbCoexistenceAKernelMoment τ (j + n + 1) := by linarith
    rw [egbCoexistenceAKernelMomentPartialSum_succ, ih, hm]
    rw [show j + (n + 1) = j + n + 1 by omega, show 2 * (n + 1) = 2 * n + 2 by omega, pow_add]
    ring

theorem egbCoexistenceAKernelMoment_exact_remainder (τ : ℝ) (j n : ℕ) :
    egbCoexistenceAKernelMoment τ j - egbCoexistenceAKernelMomentPartialSum τ j n =
      egbCoexistenceASymmetricRatio τ ^ (2 * n) * egbCoexistenceAKernelMoment τ (j + n) := by
  linarith [egbCoexistenceAKernelMoment_finite_expansion τ j n]

theorem egbCoexistenceAKernelMoment_remainder_bounds (τ : ℝ) (j n : ℕ) :
    egbCoexistenceASymmetricRatio τ ^ (2 * n) * egbCoexistenceAKernelMomentCoefficient (j + n) ≤
      egbCoexistenceAKernelMoment τ j - egbCoexistenceAKernelMomentPartialSum τ j n ∧
    egbCoexistenceAKernelMoment τ j - egbCoexistenceAKernelMomentPartialSum τ j n ≤
      egbCoexistenceASymmetricRatio τ ^ (2 * n) * egbCoexistenceAKernelMomentCoefficient (j + n) /
        (1 - egbCoexistenceASymmetricRatio τ ^ 2) := by
  rw [egbCoexistenceAKernelMoment_exact_remainder]
  have hd := (egbCoexistenceASymmetricRatio_bounds τ).1
  have hp : 0 ≤ egbCoexistenceASymmetricRatio τ ^ (2 * n) := pow_nonneg hd.le _
  constructor
  · exact mul_le_mul_of_nonneg_left (egbCoexistenceAKernelMoment_bounds τ (j + n)).1 hp
  · have h := mul_le_mul_of_nonneg_left (egbCoexistenceAKernelMoment_bounds τ (j + n)).2 hp
    simpa only [mul_div_assoc] using h

theorem egbCoexistenceAKernelMomentPartialSum_strict_lower_bound (τ : ℝ) (j n : ℕ) :
    egbCoexistenceAKernelMomentPartialSum τ j n < egbCoexistenceAKernelMoment τ j := by
  have h := egbCoexistenceAKernelMoment_exact_remainder τ j n
  have hd := (egbCoexistenceASymmetricRatio_bounds τ).1
  have hm := egbCoexistenceAKernelMoment_pos τ (j + n)
  have hp : 0 < egbCoexistenceASymmetricRatio τ ^ (2 * n) * egbCoexistenceAKernelMoment τ (j + n) := by positivity
  linarith

theorem egbCoexistenceAKernelMomentPartialSum_strict_step (τ : ℝ) (j n : ℕ) :
    egbCoexistenceAKernelMomentPartialSum τ j n < egbCoexistenceAKernelMomentPartialSum τ j (n + 1) := by
  rw [egbCoexistenceAKernelMomentPartialSum_succ]
  have hd := (egbCoexistenceASymmetricRatio_bounds τ).1
  have hc := egbCoexistenceAKernelMomentCoefficient_pos (j + n)
  have hp : 0 < egbCoexistenceAKernelMomentCoefficient (j + n) * egbCoexistenceASymmetricRatio τ ^ (2 * n) := by positivity
  linarith

theorem egbCoexistenceAKernelMoment_remainder_geometric_bound (τ : ℝ) (j n : ℕ) :
    0 ≤ egbCoexistenceAKernelMoment τ j - egbCoexistenceAKernelMomentPartialSum τ j n ∧
    egbCoexistenceAKernelMoment τ j - egbCoexistenceAKernelMomentPartialSum τ j n ≤
      ((4 : ℝ) / 3 / (1 - egbCoexistenceASymmetricRatio τ ^ 2)) * egbCoexistenceASymmetricRatio τ ^ (2 * n) := by
  have hd := egbCoexistenceASymmetricRatio_bounds τ
  have hden : 0 < 1 - egbCoexistenceASymmetricRatio τ ^ 2 := by nlinarith [hd.1, hd.2]
  have hp : 0 ≤ egbCoexistenceASymmetricRatio τ ^ (2 * n) := pow_nonneg hd.1.le _
  constructor
  · exact (sub_pos.mpr (egbCoexistenceAKernelMomentPartialSum_strict_lower_bound τ j n)).le
  · calc
      _ ≤ egbCoexistenceASymmetricRatio τ ^ (2 * n) * egbCoexistenceAKernelMomentCoefficient (j + n) /
          (1 - egbCoexistenceASymmetricRatio τ ^ 2) := (egbCoexistenceAKernelMoment_remainder_bounds τ j n).2
      _ ≤ egbCoexistenceASymmetricRatio τ ^ (2 * n) * ((4 : ℝ) / 3) /
          (1 - egbCoexistenceASymmetricRatio τ ^ 2) :=
        (div_le_div_iff_of_pos_right hden).2 (mul_le_mul_of_nonneg_left (egbCoexistenceAKernelMomentCoefficient_upper_bound (j + n)) hp)
      _ = _ := by ring

theorem egbCoexistenceASymmetricRatio_power_limit (τ : ℝ) :
    Tendsto (fun n : ℕ => egbCoexistenceASymmetricRatio τ ^ (2 * n)) atTop (𝓝 0) := by
  have hd := egbCoexistenceASymmetricRatio_bounds τ
  have hs : egbCoexistenceASymmetricRatio τ ^ 2 < 1 := by nlinarith [hd.1, hd.2]
  have h := tendsto_pow_atTop_nhds_zero_of_lt_one (sq_nonneg (egbCoexistenceASymmetricRatio τ)) hs
  simpa only [pow_mul] using h

theorem egbCoexistenceAKernelMoment_remainder_vanishes (τ : ℝ) (j : ℕ) :
    Tendsto (fun n : ℕ => egbCoexistenceAKernelMoment τ j - egbCoexistenceAKernelMomentPartialSum τ j n) atTop (𝓝 0) := by
  have hu : Tendsto (fun n : ℕ => ((4 : ℝ) / 3 / (1 - egbCoexistenceASymmetricRatio τ ^ 2)) *
      egbCoexistenceASymmetricRatio τ ^ (2 * n)) atTop (𝓝 0) := by
    simpa only [mul_zero] using (tendsto_const_nhds (x := ((4 : ℝ) / 3 / (1 - egbCoexistenceASymmetricRatio τ ^ 2)))).mul
      (egbCoexistenceASymmetricRatio_power_limit τ)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hu
    (fun n => (egbCoexistenceAKernelMoment_remainder_geometric_bound τ j n).1)
      (fun n => (egbCoexistenceAKernelMoment_remainder_geometric_bound τ j n).2)

theorem egbCoexistenceAKernelMomentPartialSum_tendsto (τ : ℝ) (j : ℕ) :
    Tendsto (egbCoexistenceAKernelMomentPartialSum τ j) atTop (𝓝 (egbCoexistenceAKernelMoment τ j)) := by
  have h := (tendsto_const_nhds (x := egbCoexistenceAKernelMoment τ j)).sub (egbCoexistenceAKernelMoment_remainder_vanishes τ j)
  have he : (fun n => egbCoexistenceAKernelMoment τ j -
      (egbCoexistenceAKernelMoment τ j - egbCoexistenceAKernelMomentPartialSum τ j n)) =
        egbCoexistenceAKernelMomentPartialSum τ j := by funext n; ring
  rw [he] at h
  simpa only [sub_zero] using h

theorem egbCoexistenceAKernelMoment_hasSum (τ : ℝ) (j : ℕ) :
    HasSum (fun n : ℕ => egbCoexistenceAKernelMomentCoefficient (j + n) * egbCoexistenceASymmetricRatio τ ^ (2 * n))
      (egbCoexistenceAKernelMoment τ j) := by
  have hn : ∀ n : ℕ, 0 ≤ egbCoexistenceAKernelMomentCoefficient (j + n) * egbCoexistenceASymmetricRatio τ ^ (2 * n) := by
    intro n
    have hd := (egbCoexistenceASymmetricRatio_bounds τ).1
    have hc := egbCoexistenceAKernelMomentCoefficient_pos (j + n)
    positivity
  exact (hasSum_iff_tendsto_nat_of_nonneg hn _).2 (egbCoexistenceAKernelMomentPartialSum_tendsto τ j)

theorem egbCoexistenceAKernelMoment_tsum (τ : ℝ) (j : ℕ) :
    (∑' n : ℕ, egbCoexistenceAKernelMomentCoefficient (j + n) * egbCoexistenceASymmetricRatio τ ^ (2 * n)) =
      egbCoexistenceAKernelMoment τ j := (egbCoexistenceAKernelMoment_hasSum τ j).tsum_eq

end GaloisForLFunctions.HTGeometry
