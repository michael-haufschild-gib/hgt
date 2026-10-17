import GaloisForLFunctions.BiScaleUncertainty.IntegerHatTraceExtension
import GaloisForLFunctions.RHTower.AutocorrelationChainSineCertificate

/-!
# Exact finite sine packets in the infinite trace space

Finite interval data are actual ℓ² vectors. The sine recurrence gives their
exact adjacent pairing, while alternating signs reverse that pairing and
preserve mass. These packets attain the two Dirichlet path constants.
-/

noncomputable section
open scoped RealInnerProductSpace

namespace GaloisForLFunctions.BiScaleUncertainty.SobolevShear
set_option autoImplicit false

def intervalTraceData (a n : ℕ) (x : ℕ → ℝ) : TraceData :=
  ∑ j ∈ Finset.range n, lp.single 2 (a + j) (x j)

theorem intervalTraceData_at (a n i : ℕ) (x : ℕ → ℝ) :
    intervalTraceData a n x (a + i) = if i < n then x i else 0 := by
  classical
  have he (j : ℕ) : (lp.single 2 (a+j) (x j) : TraceData) (a+i) =
      if i = j then x j else 0 := by
    by_cases hij : i = j
    · subst j
      simp [lp.single_apply]
    · simp [lp.single_apply, hij]
  simp only [intervalTraceData, lp.coeFn_sum, Finset.sum_apply, he]
  simp

theorem intervalTraceData_inner (a n : ℕ) (x : ℕ → ℝ) (v : TraceData) :
    ⟪intervalTraceData a n x, v⟫ = ∑ j ∈ Finset.range n, x j * v (a + j) := by
  simp only [intervalTraceData, sum_inner, lp.inner_single_left, Real.inner_apply]

theorem intervalTraceData_norm_sq (a n : ℕ) (x : ℕ → ℝ) :
    ‖intervalTraceData a n x‖ ^ 2 = ∑ j ∈ Finset.range n, (x j) ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, intervalTraceData_inner]
  apply Finset.sum_congr rfl
  intro j hj
  rw [intervalTraceData_at, if_pos (Finset.mem_range.mp hj)]
  ring

theorem intervalTraceData_adjacent (a n : ℕ) (x : ℕ → ℝ) (hx : x n = 0) :
    (∑' k, intervalTraceData a n x k * intervalTraceData a n x (k+1)) =
      ∑ j ∈ Finset.range n, x j * x (j+1) := by
  rw [(hasSum_adjacentTraceProduct _).tsum_eq]
  have hi := (sequenceRightShift ℝ).toContinuousLinearMap.adjoint_inner_left
    (intervalTraceData a n x) (intervalTraceData a n x)
  change ⟪sequenceLeftShift ℝ (intervalTraceData a n x), intervalTraceData a n x⟫ =
    ⟪intervalTraceData a n x, sequenceRightShift ℝ (intervalTraceData a n x)⟫ at hi
  rw [← hi, real_inner_comm, intervalTraceData_inner]
  apply Finset.sum_congr rfl
  intro j hj
  rw [sequenceLeftShift_apply, Nat.add_assoc, intervalTraceData_at]
  have hjn := Finset.mem_range.mp hj
  by_cases hnext : j + 1 < n
  · rw [if_pos hnext]
  · have he : j + 1 = n := by omega
    simp [he, hx]

theorem intervalTraceData_off (a n k : ℕ) (x : ℕ → ℝ)
    (hk : ∀ j < n, k ≠ a+j) : intervalTraceData a n x k = 0 := by
  simp only [intervalTraceData, lp.coeFn_sum, Finset.sum_apply]
  apply Finset.sum_eq_zero
  intro j hj
  simp [lp.single_apply, Pi.single_eq_of_ne (hk j (Finset.mem_range.mp hj))]

def pathSineValue (n j : ℕ) : ℝ := RHTower.autocorrelationSineWeight n (j + 1)

theorem pathSineValue_end (n : ℕ) : pathSineValue n n = 0 :=
  RHTower.autocorrelationSineWeight_end n

theorem pathSineValue_first_pos (n : ℕ) (hn : 0 < n) : 0 < pathSineValue n 0 :=
  RHTower.autocorrelationSineWeight_pos (by omega) hn

theorem pathSineValue_adjacent (n : ℕ) :
    (∑ j ∈ Finset.range n, pathSineValue n j * pathSineValue n (j+1)) =
      Real.cos (Real.pi / ((n : ℝ)+1)) * ∑ j ∈ Finset.range n, (pathSineValue n j)^2 := by
  let w := RHTower.autocorrelationSineWeight n
  let f : ℕ → ℝ := fun j => w j * w (j+1)
  have h0 : f 0 = 0 := by simp [f, w, RHTower.autocorrelationSineWeight_zero]
  have hn : f n = 0 := by simp [f, w, RHTower.autocorrelationSineWeight_end]
  have hshift : (∑ j ∈ Finset.range n, f (j+1)) = ∑ j ∈ Finset.range n, f j := by
    have h1 := Finset.sum_range_succ' f n
    have h2 := Finset.sum_range_succ f n
    rw [h0, add_zero] at h1
    rw [hn, add_zero] at h2
    exact h1.symm.trans h2
  have he (j : ℕ) : f j + f (j+1) =
      (2 * Real.cos (Real.pi / ((n : ℝ)+1))) * (pathSineValue n j)^2 := by
    have hr := RHTower.autocorrelationSineWeight_recurrence n
      (show 0 < j+1 by omega)
    simp only [Nat.add_sub_cancel] at hr
    dsimp only [f, w, pathSineValue]
    calc
      _ = RHTower.autocorrelationSineWeight n (j+1) *
          (RHTower.autocorrelationSineWeight n j +
            RHTower.autocorrelationSineWeight n (j+1+1)) := by ring
      _ = _ := by rw [hr]; ring
  have hs : (∑ j ∈ Finset.range n, (f j + f (j+1))) =
      ∑ j ∈ Finset.range n,
        (2 * Real.cos (Real.pi / ((n : ℝ)+1))) * (pathSineValue n j)^2 :=
    Finset.sum_congr rfl (fun j _ => he j)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← hshift] at hs
  change (∑ j ∈ Finset.range n, pathSineValue n j * pathSineValue n (j+1)) = _
  change (∑ j ∈ Finset.range n, pathSineValue n j * pathSineValue n (j+1)) +
    (∑ j ∈ Finset.range n, pathSineValue n j * pathSineValue n (j+1)) = _ at hs
  linarith only [hs]

def alternatingPathSineValue (n j : ℕ) : ℝ := (-1 : ℝ)^j * pathSineValue n j

theorem alternatingPathSineValue_sq (n j : ℕ) :
    (alternatingPathSineValue n j)^2 = (pathSineValue n j)^2 := by
  unfold alternatingPathSineValue
  rw [mul_pow, ← pow_mul, Nat.mul_comm j 2, pow_mul]
  norm_num

theorem alternatingPathSineValue_adjacent_term (n j : ℕ) :
    alternatingPathSineValue n j * alternatingPathSineValue n (j+1) =
      -(pathSineValue n j * pathSineValue n (j+1)) := by
  have hs : ((-1 : ℝ)^j)^2 = 1 := by rw [← pow_mul, Nat.mul_comm j 2, pow_mul]; simp
  simp only [alternatingPathSineValue, pow_succ]
  calc
    _ = -(((-1 : ℝ)^j)^2 * (pathSineValue n j * pathSineValue n (j+1))) := by ring
    _ = _ := by rw [hs]; ring

theorem alternatingPathSineValue_end (n : ℕ) : alternatingPathSineValue n n = 0 := by
  simp [alternatingPathSineValue, pathSineValue_end]

theorem alternatingPathSineValue_adjacent (n : ℕ) :
    (∑ j ∈ Finset.range n, alternatingPathSineValue n j * alternatingPathSineValue n (j+1)) =
      -(Real.cos (Real.pi / ((n : ℝ)+1)) * ∑ j ∈ Finset.range n, (pathSineValue n j)^2) := by
  simp only [alternatingPathSineValue_adjacent_term, Finset.sum_neg_distrib,
    pathSineValue_adjacent]

end GaloisForLFunctions.BiScaleUncertainty.SobolevShear
