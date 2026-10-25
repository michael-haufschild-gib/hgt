import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Order
import Mathlib.Topology.Instances.Matrix
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Finite-dimensional unitary translations with affine covariance

Conjugacy preserves trace. A continuous unitary family fixed at the origin and covariant with
an invertible expanding dilation must therefore have maximal trace everywhere, hence be the
identity. Nontrivial unitary translations require an infinite-dimensional carrier.
-/

noncomputable section

open Filter Topology
open scoped Matrix ComplexOrder

namespace GaloisForLFunctions.BiarithmeticGeometry

private theorem unitaryMatrix_eq_one_of_trace {n : ℕ} (U : Matrix (Fin n) (Fin n) ℂ)
    (hU : Uᴴ * U = 1) (htrace : U.trace = (1 : Matrix (Fin n) (Fin n) ℂ).trace) : U = 1 := by
  apply sub_eq_zero.mp
  apply Matrix.trace_conjTranspose_mul_self_eq_zero_iff.mp
  have hexpand : (U - 1)ᴴ * (U - 1) = Uᴴ * U - Uᴴ - U + 1 := by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one]
    noncomm_ring
  rw [hexpand, hU, Matrix.trace_add, Matrix.trace_sub, Matrix.trace_sub,
    Matrix.trace_conjTranspose, htrace]
  simp [Matrix.trace_one]

private theorem trace_eq_of_affine_covariance {n : ℕ}
    (U : ℝ → Matrix (Fin n) (Fin n) ℂ) (D : (Matrix (Fin n) (Fin n) ℂ)ˣ)
    (p : ℝ) (hp : 0 < p)
    (hcov : ∀ t, (D : Matrix (Fin n) (Fin n) ℂ) * U t =
      U (p * t) * (D : Matrix (Fin n) (Fin n) ℂ)) (t : ℝ) :
    (U (t / p)).trace = (U t).trace := by
  have h (s : ℝ) : (U s).trace = (U (p * s)).trace := by
    calc
      _ = Matrix.trace ((↑D⁻¹ : Matrix (Fin n) (Fin n) ℂ) * (↑D * U s)) := by
        rw [← mul_assoc, Units.inv_mul, one_mul]
      _ = Matrix.trace ((↑D * U s) * (↑D⁻¹ : Matrix (Fin n) (Fin n) ℂ)) :=
        Matrix.trace_mul_comm _ _
      _ = Matrix.trace ((U (p * s) * ↑D) * (↑D⁻¹ : Matrix (Fin n) (Fin n) ℂ)) := by
        rw [hcov]
      _ = _ := by rw [mul_assoc, Units.mul_inv, mul_one]
  simpa only [mul_div_cancel₀ t hp.ne'] using h (t / p)

/-- A finite-dimensional continuous unitary family with invertible dilation covariance is
trivial. The conclusion needs no extra translation group law. -/
theorem finite_affine_unitary_rigidity {n : ℕ}
    (U : ℝ → Matrix (Fin n) (Fin n) ℂ)
    (hcontinuous : Continuous U) (hzero : U 0 = 1)
    (hunitary : ∀ t, (U t)ᴴ * U t = 1)
    (D : (Matrix (Fin n) (Fin n) ℂ)ˣ) (p : ℝ) (hp : 1 < p)
    (hcov : ∀ t, (D : Matrix (Fin n) (Fin n) ℂ) * U t =
      U (p * t) * (D : Matrix (Fin n) (Fin n) ℂ)) :
    ∀ t, U t = 1 := by
  intro t
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  apply unitaryMatrix_eq_one_of_trace _ (hunitary t)
  have htrace (k : ℕ) : (U ((1 / p : ℝ) ^ k * t)).trace = (U t).trace := by
    induction k with
    | zero => simp
    | succ k ih =>
      have heq : (1 / p : ℝ) ^ (k + 1) * t = ((1 / p : ℝ) ^ k * t) / p := by
        rw [pow_succ]
        ring
      rw [heq, trace_eq_of_affine_covariance U D p hp0 hcov, ih]
  have hsmall : |(1 / p : ℝ)| < 1 := by
    rw [abs_of_pos (one_div_pos.mpr hp0)]
    exact (div_lt_one hp0).mpr hp
  have hscale : Tendsto (fun k : ℕ => (1 / p : ℝ) ^ k * t) atTop (𝓝 0) := by
    simpa only [zero_mul] using
      (tendsto_pow_atTop_nhds_zero_of_abs_lt_one hsmall).mul_const t
  have hlimit : Tendsto (fun k : ℕ => (U ((1 / p : ℝ) ^ k * t)).trace) atTop
      (𝓝 ((U 0).trace)) := by
    apply tendsto_finsetSum
    intro i _
    exact ((continuous_apply i).comp ((continuous_apply i).comp hcontinuous)).continuousAt.tendsto.comp hscale
  simp only [htrace, hzero] at hlimit
  exact tendsto_nhds_unique tendsto_const_nhds hlimit

end GaloisForLFunctions.BiarithmeticGeometry
