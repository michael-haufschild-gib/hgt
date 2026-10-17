import GaloisForLFunctions.BiScaleUncertainty.CoprimeSobolevInterpolation
import GaloisForLFunctions.BiScaleUncertainty.SobolevLogarithmicTransport

/-!
# Sharp coprime trace coercivity for actual logarithmic Sobolev states

Every finite divisor trace has an explicitly constructed L2 velocity and locally
absolutely continuous logarithmic primitive. Its weighted derivative energy is
exactly twice its squared trace norm. An unconditional square completion measures
the energy of every competitor, including its trace error and interpolation
defect. The same rough-state space supports the nonlinear additive shear bound.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators NNReal Topology

namespace GaloisForLFunctions.BiScaleUncertainty.SobolevShear
set_option autoImplicit false

theorem energy_add (q : Velocity) (a b c : ℝ) :
    energy q a b + energy q b c = energy q a c :=
  intervalIntegral.integral_add_adjacent_intervals
    (integrable_velocity_sq q).intervalIntegrable (integrable_velocity_sq q).intervalIntegrable

theorem divisorTrace_next (v : ℕ → ℝ) (d N : ℕ) : divisorTrace v d N (N+1) = 0 := by
  simp [divisorTrace]

theorem divisorTrace_shifted_discrete_energy (v : ℕ → ℝ) (d N : ℕ) :
    (∑ j ∈ Finset.range N, (addDiff (divisorTrace v d N) (j+1))^2) =
      2 * ∑ j ∈ Finset.range N, (divisorTrace v d N j)^2 := by
  have h := telescope_addDiff (fun j => (addDiff (divisorTrace v d N) j)^2) 0 N
  simp only [zero_add, addDiff, divisorTrace_zero, divisorTrace_one,
    divisorTrace_end, divisorTrace_next, sub_self, zero_pow (by norm_num : 2 ≠ 0),
    Finset.sum_sub_distrib] at h
  have he := divisorTrace_discrete_energy v d N
  unfold addDiff at he ⊢
  linarith

/-- A positive physical window contains all energy of the constructed coprime state. -/
theorem divisorVelocity_energy_positive_window (v : ℕ → ℝ) (d N : ℕ) :
    energy (divisorVelocity v d N) 1 (N+1) =
      2 * ∑ j ∈ Finset.range N, (divisorTrace v d N j)^2 := by
  have h₁ := energy_add (divisorVelocity v d N) 0 1 (N+1)
  have h₂ := energy_add (divisorVelocity v d N) 0 N (N+1)
  have h₃ := energy_stepVelocity_tail (addDiff (divisorTrace v d N)) N
  change energy (divisorVelocity v d N) N (N+1) = 0 at h₃
  rw [divisorVelocity_energy_first_cell] at h₁
  rw [h₃, divisorVelocity_energy] at h₂
  linarith

theorem log_divisorVelocity_trace (v : ℕ → ℝ) (d N : ℕ) (m : Fin N) :
    logPrimitive (divisorVelocity v d N) (Real.log (m+1)) =
      divisorTrace v d N (m+1) := by
  rw [logPrimitive, Real.exp_log (by positivity : (0 : ℝ) < m+1)]
  simpa using divisorVelocity_trace v d N ⟨m+1, by omega⟩

/-- The sharp coefficient two is attained by an actual rough logarithmic state. -/
theorem log_divisorVelocity_energy (v : ℕ → ℝ) (d N : ℕ) :
    (∫ x in (0 : ℝ)..Real.log (N+1),
      Real.exp (-x)*(deriv (logPrimitive (divisorVelocity v d N)) x)^2) =
      2 * ∑ j ∈ Finset.range N, (divisorTrace v d N j)^2 := by
  rw [log_energy_eq, Real.exp_zero, Real.exp_log (by positivity : (0 : ℝ) < N+1),
    divisorVelocity_energy_positive_window]

/-- Prescribed slopes need not agree with the competitor: the trace error is explicit. -/
theorem prescribed_trace_energy_decomposition (q : Velocity) (s : ℕ → ℝ)
    (a : ℝ) (N : ℕ) :
    energy q a (a+N) =
      (∑ j ∈ Finset.range N, (s j)^2) +
      2 * (∑ j ∈ Finset.range N,
        s j*(primitive q (a+(j+1))-primitive q (a+j)-s j)) +
      ∑ j ∈ Finset.range N, ∫ t in (a+j)..(a+(j+1)), (q t-s j)^2 := by
  have hd (j : ℕ) : (∫ t in (a+j)..(a+(j+1)), (q t-s j)^2) =
      energy q (a+j) (a+(j+1)) - (s j)^2 -
        2*(s j*(primitive q (a+(j+1))-primitive q (a+j)-s j)) := by
    have h := integral_scaled_deviation_sq q (a+j) (a+(j+1)) 1 (s j)
    simp only [one_mul, one_pow] at h
    rw [h]
    ring
  simp_rw [hd]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  have hs := sum_cell_energy q a 1 N
  simp only [one_mul] at hs
  rw [hs]
  ring

/-- Sharp lower bound with a signed trace-error correction; no matching-trace premise. -/
theorem prescribed_trace_energy_lower (q : Velocity) (s : ℕ → ℝ)
    (a : ℝ) (N : ℕ) :
    (∑ j ∈ Finset.range N, (s j)^2) +
      2 * (∑ j ∈ Finset.range N,
        s j*(primitive q (a+(j+1))-primitive q (a+j)-s j)) ≤ energy q a (a+N) := by
  rw [prescribed_trace_energy_decomposition q s a N]
  apply le_add_of_nonneg_right
  apply Finset.sum_nonneg
  intro j _
  exact intervalIntegral.integral_nonneg_of_forall (by linarith) (fun t => sq_nonneg (q t-s j))

/-- Exact coprime coercivity, including trace mismatch and the nonnegative excess energy. -/
theorem coprime_trace_energy_decomposition (q : Velocity) (v : ℕ → ℝ) (d N : ℕ) :
    energy q 0 N =
      2 * (∑ j ∈ Finset.range N, (divisorTrace v d N j)^2) +
      2 * (∑ j ∈ Finset.range N, addDiff (divisorTrace v d N) j *
        (primitive q (j+1)-primitive q j-addDiff (divisorTrace v d N) j)) +
      ∑ j ∈ Finset.range N, ∫ t in (j : ℝ)..(j+1),
        (q t-addDiff (divisorTrace v d N) j)^2 := by
  have h := prescribed_trace_energy_decomposition q (addDiff (divisorTrace v d N)) 0 N
  simpa only [zero_add, divisorTrace_discrete_energy] using h

/-- The same exact coercivity on the positive physical window of logarithmic states. -/
theorem log_coprime_trace_energy_decomposition (q : Velocity) (v : ℕ → ℝ) (d N : ℕ) :
    (∫ x in (0 : ℝ)..Real.log (N+1), Real.exp (-x)*(deriv (logPrimitive q) x)^2) =
      2 * (∑ j ∈ Finset.range N, (divisorTrace v d N j)^2) +
      2 * (∑ j ∈ Finset.range N, addDiff (divisorTrace v d N) (j+1) *
        (primitive q (1+(j+1))-primitive q (1+j)-addDiff (divisorTrace v d N) (j+1))) +
      ∑ j ∈ Finset.range N, ∫ t in (1+(j : ℝ))..(1+(j+1)),
        (q t-addDiff (divisorTrace v d N) (j+1))^2 := by
  rw [log_energy_eq, Real.exp_zero, Real.exp_log (by positivity : (0 : ℝ) < N+1)]
  have h := prescribed_trace_energy_decomposition q
    (fun j => addDiff (divisorTrace v d N) (j+1)) 1 N
  rw [divisorTrace_shifted_discrete_energy, add_comm (1 : ℝ) (N : ℝ)] at h
  exact h

/-- Dropping only the nonnegative interpolation defect gives a corrected coercive bound. -/
theorem log_coprime_trace_energy_lower (q : Velocity) (v : ℕ → ℝ) (d N : ℕ) :
    2 * (∑ j ∈ Finset.range N, (divisorTrace v d N j)^2) +
      2 * (∑ j ∈ Finset.range N, addDiff (divisorTrace v d N) (j+1) *
        (primitive q (1+(j+1))-primitive q (1+j)-addDiff (divisorTrace v d N) (j+1))) ≤
      ∫ x in (0 : ℝ)..Real.log (N+1), Real.exp (-x)*(deriv (logPrimitive q) x)^2 := by
  rw [log_coprime_trace_energy_decomposition q v d N]
  apply le_add_of_nonneg_right
  apply Finset.sum_nonneg
  intro j _
  exact intervalIntegral.integral_nonneg_of_forall (by linarith)
    (fun t => sq_nonneg (q t-addDiff (divisorTrace v d N) (j+1)))

/-- Nonlinear additive shear control holds for arbitrary L2 physical velocities. -/
theorem log_shear_increment_sq_le (q : Velocity) (x : ℝ) (b : ℝ≥0) :
    (logPrimitive q (ContinuumShear.shear b x)-logPrimitive q x)^2 ≤
      (b : ℝ) * ∫ y in x..ContinuumShear.shear b x,
        Real.exp (-y)*(deriv (logPrimitive q) y)^2 := by
  rw [log_energy_eq]
  simp only [logPrimitive, ContinuumShear.exp_shear]
  exact increment_sq_le_energy q (Real.exp x) b

end GaloisForLFunctions.BiScaleUncertainty.SobolevShear
