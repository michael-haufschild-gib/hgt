import GaloisForLFunctions.HTGeometry.StaticGaussianCrossingMemoryLaw
import Mathlib.Tactic

/-!
# Exponential-memory transport curvature: correction and lag repair

For a two-mode pencil `c A + s B`, exponential causal reconstruction rotates and attenuates
the two coefficient coordinates.  Direct commutator algebra gives two conclusions relevant to
arXiv:2608.09607.

* The commutator of two reconstructed histories is attenuated by `1 / (1 + x²)` and generally
  remains nonzero at zero memory.  It is not created by memory.
* The paper's signed `x / (1 + x²)` law belongs instead to the present-versus-memory lag
  commutator.  This lag curvature vanishes exactly at zero memory whenever the two source modes
  do not commute.

The pure memory-defect commutator is also classified.  Its coefficient is the even response
`x² / (1 + x²)`, so it detects the neutral grade but erases orientation.  The lag curvature is
the stronger survivor because it retains the sign of `x`.
-/

open scoped Matrix
open Matrix

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- A two-mode transport pencil at scalar phase coordinates `(c,s)`. -/
def twoModeTransportPencil {N : Type*} [Fintype N]
    (A B : Matrix N N ℂ) (c s : ℂ) : Matrix N N ℂ :=
  c • A + s • B

/-- Exponential-memory reconstruction of a two-mode pencil, in dimensionless memory grade `x`. -/
def exponentialMemoryTransportPencil {N : Type*} [Fintype N]
    (A B : Matrix N N ℂ) (x : ℝ) (c s : ℂ) : Matrix N N ℂ :=
  ((c + (x : ℂ) * s) / (1 + (x : ℂ) ^ (2 : ℕ))) • A +
    ((s - (x : ℂ) * c) / (1 + (x : ℂ) ^ (2 : ℕ))) • B

/-- Pure memory contribution after subtracting the instantaneous pencil. -/
def exponentialMemoryTransportDefect {N : Type*} [Fintype N]
    (A B : Matrix N N ℂ) (x : ℝ) (c s : ℂ) : Matrix N N ℂ :=
  exponentialMemoryTransportPencil A B x c s - twoModeTransportPencil A B c s

/-- Present-versus-memory mismatch curvature. -/
def exponentialMemoryLagCurvature {N : Type*} [Fintype N]
    (A B : Matrix N N ℂ) (x : ℝ) (c s : ℂ) : Matrix N N ℂ :=
  matrixCommutator (exponentialMemoryTransportPencil A B x c s)
    (twoModeTransportPencil A B c s)

/-- The commutator of two linear combinations is their coefficient determinant times the source
commutator. -/
theorem matrixCommutator_twoModeTransportPencil
    {N : Type*} [Fintype N]
    (A B : Matrix N N ℂ) (a b c d : ℂ) :
    matrixCommutator (twoModeTransportPencil A B a b)
        (twoModeTransportPencil A B c d) =
      (a * d - b * c) • matrixCommutator A B := by
  simp only [matrixCommutator, twoModeTransportPencil, Matrix.add_mul,
    Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul]
  module

theorem complex_one_add_real_sq_ne_zero (x : ℝ) :
    (1 + (x : ℂ) ^ (2 : ℕ)) ≠ 0 := by
  exact_mod_cast (show (1 + x ^ (2 : ℕ) : ℝ) ≠ 0 by positivity)

/-- Real signed response carried by the present-versus-memory lag. -/
def exponentialMemoryLagResponse (x : ℝ) : ℝ :=
  x / (1 + x ^ (2 : ℕ))

/-- The repaired memory response is uniformly bounded, so the physical probe adds no large-grade
amplification. -/
theorem abs_exponentialMemoryLagResponse_le_half (x : ℝ) :
    |exponentialMemoryLagResponse x| ≤ 1 / 2 := by
  rw [exponentialMemoryLagResponse, abs_div,
    abs_of_pos (by positivity : 0 < 1 + x ^ (2 : ℕ))]
  rw [div_le_iff₀ (by positivity : 0 < 1 + x ^ (2 : ℕ))]
  nlinarith [sq_nonneg (|x| - 1), sq_abs x]

theorem exponentialMemoryLagResponse_neg (x : ℝ) :
    exponentialMemoryLagResponse (-x) = -exponentialMemoryLagResponse x := by
  rw [exponentialMemoryLagResponse, exponentialMemoryLagResponse]
  ring

theorem exponentialMemoryLagResponse_eq_zero_iff (x : ℝ) :
    exponentialMemoryLagResponse x = 0 ↔ x = 0 := by
  constructor
  · intro h
    exact (div_eq_zero_iff.mp h).resolve_right (by positivity)
  · rintro rfl
    simp [exponentialMemoryLagResponse]

/-- Correct two-time law: exponential reconstruction attenuates existing noncommutativity by
`1 / (1+x²)`; it does not create the commutator. -/
theorem matrixCommutator_exponentialMemoryTransportPencil
    {N : Type*} [Fintype N]
    (A B : Matrix N N ℂ) (x : ℝ) (c₁ s₁ c₂ s₂ : ℂ) :
    matrixCommutator (exponentialMemoryTransportPencil A B x c₁ s₁)
        (exponentialMemoryTransportPencil A B x c₂ s₂) =
      ((c₁ * s₂ - s₁ * c₂) / (1 + (x : ℂ) ^ (2 : ℕ))) •
        matrixCommutator A B := by
  change matrixCommutator
      (twoModeTransportPencil A B
        ((c₁ + (x : ℂ) * s₁) / (1 + (x : ℂ) ^ (2 : ℕ)))
        ((s₁ - (x : ℂ) * c₁) / (1 + (x : ℂ) ^ (2 : ℕ))))
      (twoModeTransportPencil A B
        ((c₂ + (x : ℂ) * s₂) / (1 + (x : ℂ) ^ (2 : ℕ)))
        ((s₂ - (x : ℂ) * c₂) / (1 + (x : ℂ) ^ (2 : ℕ)))) = _
  rw [matrixCommutator_twoModeTransportPencil]
  congr 1
  field_simp [complex_one_add_real_sq_ne_zero x]
  ring

/-- Exact repair of the paper's signed response: `x/(1+x²)` is the coefficient of the
present-versus-memory lag curvature, not the two-time reconstructed curvature. -/
theorem exponentialMemoryLagCurvature_eq
    {N : Type*} [Fintype N]
    (A B : Matrix N N ℂ) (x : ℝ) (c s : ℂ) :
    exponentialMemoryLagCurvature A B x c s =
      (((x : ℂ) * (c ^ (2 : ℕ) + s ^ (2 : ℕ))) / (1 + (x : ℂ) ^ (2 : ℕ))) •
        matrixCommutator A B := by
  change matrixCommutator
      (twoModeTransportPencil A B
        ((c + (x : ℂ) * s) / (1 + (x : ℂ) ^ (2 : ℕ)))
        ((s - (x : ℂ) * c) / (1 + (x : ℂ) ^ (2 : ℕ))))
      (twoModeTransportPencil A B c s) = _
  rw [matrixCommutator_twoModeTransportPencil]
  congr 1
  field_simp [complex_one_add_real_sq_ne_zero x]
  ring

theorem exponentialMemoryLagCurvature_axis_eq
    {N : Type*} [Fintype N]
    (A B : Matrix N N ℂ) (x : ℝ) :
    exponentialMemoryLagCurvature A B x 1 0 =
      ((x : ℂ) / (1 + (x : ℂ) ^ (2 : ℕ))) • matrixCommutator A B := by
  simpa using exponentialMemoryLagCurvature_eq A B x 1 0

/-- For noncommuting modes the repaired signed curvature has exactly the neutral radical. -/
theorem exponentialMemoryLagCurvature_axis_eq_zero_iff
    {N : Type*} [Fintype N]
    (A B : Matrix N N ℂ) (hAB : matrixCommutator A B ≠ 0) (x : ℝ) :
    exponentialMemoryLagCurvature A B x 1 0 = 0 ↔ x = 0 := by
  rw [exponentialMemoryLagCurvature_axis_eq]
  constructor
  · intro h
    have hscalar : (x : ℂ) / (1 + (x : ℂ) ^ (2 : ℕ)) = 0 :=
      (smul_eq_zero.mp h).resolve_right hAB
    have hxC : (x : ℂ) = 0 :=
      (div_eq_zero_iff.mp hscalar).resolve_right (complex_one_add_real_sq_ne_zero x)
    exact_mod_cast hxC
  · rintro rfl
    simp

/-- A linear reporter can consume the repaired curvature without losing its neutral radical
exactly when it sees the underlying mode commutator.  This is the route-neutral interface: a
physical source law must provide reporter annihilation, while coefficient faithfulness is the
separate non-erasure obligation. -/
theorem exponentialMemoryLagCurvature_axis_reporter_eq_zero_iff
    {N V : Type*} [Fintype N] [AddCommMonoid V] [Module ℂ V]
    (A B : Matrix N N ℂ) (reporter : Matrix N N ℂ →ₗ[ℂ] V)
    (hfaithful : reporter (matrixCommutator A B) ≠ 0) (x : ℝ) :
    reporter (exponentialMemoryLagCurvature A B x 1 0) = 0 ↔ x = 0 := by
  rw [exponentialMemoryLagCurvature_axis_eq, LinearMap.map_smul]
  constructor
  · intro h
    have hscalar : (x : ℂ) / (1 + (x : ℂ) ^ (2 : ℕ)) = 0 :=
      (smul_eq_zero.mp h).resolve_right hfaithful
    have hxC : (x : ℂ) = 0 :=
      (div_eq_zero_iff.mp hscalar).resolve_right (complex_one_add_real_sq_ne_zero x)
    exact_mod_cast hxC
  · rintro rfl
    simp

/-- Faithful reporter flatness lifts from a scalar or quotient observation to actual lag
curvature flatness. -/
theorem exponentialMemoryLagCurvature_axis_eq_zero_of_reporter_eq_zero
    {N V : Type*} [Fintype N] [AddCommMonoid V] [Module ℂ V]
    (A B : Matrix N N ℂ) (reporter : Matrix N N ℂ →ₗ[ℂ] V)
    (hfaithful : reporter (matrixCommutator A B) ≠ 0) {x : ℝ}
    (hflat : reporter (exponentialMemoryLagCurvature A B x 1 0) = 0) :
    exponentialMemoryLagCurvature A B x 1 0 = 0 := by
  rw [exponentialMemoryLagCurvature_axis_eq_zero_iff A B]
  · exact (exponentialMemoryLagCurvature_axis_reporter_eq_zero_iff
      A B reporter hfaithful x).mp hflat
  · intro hAB
    apply hfaithful
    rw [hAB]
    exact reporter.map_zero

/-- The pure memory defect is another two-mode pencil. -/
theorem exponentialMemoryTransportDefect_eq_twoModeTransportPencil
    {N : Type*} [Fintype N]
    (A B : Matrix N N ℂ) (x : ℝ) (c s : ℂ) :
    exponentialMemoryTransportDefect A B x c s =
      twoModeTransportPencil A B
        (((-(x : ℂ) ^ (2 : ℕ)) * c + (x : ℂ) * s) / (1 + (x : ℂ) ^ (2 : ℕ)))
        ((-(x : ℂ) * c - (x : ℂ) ^ (2 : ℕ) * s) / (1 + (x : ℂ) ^ (2 : ℕ))) := by
  ext i j
  simp only [exponentialMemoryTransportDefect, exponentialMemoryTransportPencil,
    twoModeTransportPencil, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply,
    smul_eq_mul]
  field_simp [complex_one_add_real_sq_ne_zero x]
  ring

/-- Pure defect-defect curvature carries the even response `x²/(1+x²)` and therefore loses the
orientation retained by lag curvature. -/
theorem matrixCommutator_exponentialMemoryTransportDefect
    {N : Type*} [Fintype N]
    (A B : Matrix N N ℂ) (x : ℝ) (c₁ s₁ c₂ s₂ : ℂ) :
    matrixCommutator (exponentialMemoryTransportDefect A B x c₁ s₁)
        (exponentialMemoryTransportDefect A B x c₂ s₂) =
      (((x : ℂ) ^ (2 : ℕ) * (c₁ * s₂ - s₁ * c₂)) /
          (1 + (x : ℂ) ^ (2 : ℕ))) • matrixCommutator A B := by
  rw [exponentialMemoryTransportDefect_eq_twoModeTransportPencil,
    exponentialMemoryTransportDefect_eq_twoModeTransportPencil,
    matrixCommutator_twoModeTransportPencil]
  congr 1
  field_simp [complex_one_add_real_sq_ne_zero x]
  ring

theorem matrixCommutator_exponentialMemoryTransportPencil_axes
    {N : Type*} [Fintype N]
    (A B : Matrix N N ℂ) (x : ℝ) :
    matrixCommutator (exponentialMemoryTransportPencil A B x 1 0)
        (exponentialMemoryTransportPencil A B x 0 1) =
      ((1 : ℂ) / (1 + (x : ℂ) ^ (2 : ℕ))) • matrixCommutator A B := by
  simpa using matrixCommutator_exponentialMemoryTransportPencil A B x 1 0 0 1

theorem matrixCommutator_exponentialMemoryTransportDefect_axes
    {N : Type*} [Fintype N]
    (A B : Matrix N N ℂ) (x : ℝ) :
    matrixCommutator (exponentialMemoryTransportDefect A B x 1 0)
        (exponentialMemoryTransportDefect A B x 0 1) =
      (((x : ℂ) ^ (2 : ℕ) / (1 + (x : ℂ) ^ (2 : ℕ)))) • matrixCommutator A B := by
  simpa using matrixCommutator_exponentialMemoryTransportDefect A B x 1 0 0 1

/-- At zero memory the reconstructed two-time curvature is the original mode commutator, not zero. -/
theorem matrixCommutator_exponentialMemoryTransportPencil_zero
    {N : Type*} [Fintype N]
    (A B : Matrix N N ℂ) :
    matrixCommutator (exponentialMemoryTransportPencil A B 0 1 0)
        (exponentialMemoryTransportPencil A B 0 0 1) =
      matrixCommutator A B := by
  simpa using matrixCommutator_exponentialMemoryTransportPencil_axes A B 0

theorem matrixCommutator_exponentialMemoryTransportDefect_axes_eq_zero_iff
    {N : Type*} [Fintype N]
    (A B : Matrix N N ℂ) (hAB : matrixCommutator A B ≠ 0) (x : ℝ) :
    matrixCommutator (exponentialMemoryTransportDefect A B x 1 0)
        (exponentialMemoryTransportDefect A B x 0 1) = 0 ↔ x = 0 := by
  rw [matrixCommutator_exponentialMemoryTransportDefect_axes]
  constructor
  · intro h
    have hscalar : ((x : ℂ) ^ (2 : ℕ) / (1 + (x : ℂ) ^ (2 : ℕ))) = 0 :=
      (smul_eq_zero.mp h).resolve_right hAB
    have hxC : (x : ℂ) = 0 := by
      have hxSq : (x : ℂ) ^ (2 : ℕ) = 0 :=
        (div_eq_zero_iff.mp hscalar).resolve_right (complex_one_add_real_sq_ne_zero x)
      have hxMul : (x : ℂ) * (x : ℂ) = 0 := by simpa [pow_two] using hxSq
      exact (mul_eq_zero.mp hxMul).elim id id
    exact_mod_cast hxC
  · rintro rfl
    simp

end

end GaloisForLFunctions.HTGeometry
