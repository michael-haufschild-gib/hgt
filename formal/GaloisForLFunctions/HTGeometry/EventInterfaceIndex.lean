import GaloisForLFunctions.HTGeometry.RepresentationFracture

/-!
# Event interface index

This file proves the exact finite-dimensional survivor exposed by the matter-to-observable
representation fracture.

On a ten-dimensional complex carrier, a source involution of trace `2` has a four-dimensional
negative projection. Any linear map intertwining that source involution with the identity kills
the projection. Its kernel therefore has dimension at least four, its range has dimension at most
six, and its cokernel has dimension at least four. At maximal rank six, kernel and cokernel both
have dimension exactly four.

The theorem is pure linear algebra. It does not identify either four-dimensional space with a
Higgs carrier or spacetime, construct a nonlinear event, or derive dynamics.
-/

open Matrix

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- An intertwiner from an involution to the identity kills the involution's negative projection. -/
theorem involutionProjection_range_le_intertwiner_ker
    {n : Type*} [Fintype n] [DecidableEq n]
    (A T : Matrix n n ℂ) (hT : T * A = T) :
    LinearMap.range (involutionProjection A).toLin' ≤ LinearMap.ker T.toLin' := by
  have hTP : T * involutionProjection A = 0 := by
    simp only [involutionProjection, Matrix.mul_smul, Matrix.mul_sub, mul_one, hT, sub_self,
      smul_zero]
  rw [LinearMap.range_le_ker_iff, ← Matrix.toLin'_mul, hTP]
  simp

/-- On a ten-carrier, trace two forces at least four directions into the kernel. -/
theorem four_le_finrank_ker_of_trace_two_intertwines_identity
    (A T : Matrix (Fin 10) (Fin 10) ℂ)
    (hA : A * A = 1) (htrace : Matrix.trace A = 2) (hT : T * A = T) :
    4 ≤ Module.finrank ℂ (LinearMap.ker T.toLin') := by
  have hformula := involution_trace_eq_card_sub_two_mul_finrank A hA
  have hrC :
      (Module.finrank ℂ (LinearMap.range (involutionProjection A).toLin') : ℂ) = 4 := by
    rw [htrace] at hformula
    norm_num at hformula ⊢
    linear_combination hformula / 2
  have hr :
      Module.finrank ℂ (LinearMap.range (involutionProjection A).toLin') = 4 := by
    exact_mod_cast hrC
  rw [← hr]
  exact Submodule.finrank_mono
    (involutionProjection_range_le_intertwiner_ker A T hT)

/-- The image of a trace-two-to-identity intertwiner on ten directions has rank at most six. -/
theorem finrank_range_le_six_of_trace_two_intertwines_identity
    (A T : Matrix (Fin 10) (Fin 10) ℂ)
    (hA : A * A = 1) (htrace : Matrix.trace A = 2) (hT : T * A = T) :
    Module.finrank ℂ (LinearMap.range T.toLin') ≤ 6 := by
  have hker := four_le_finrank_ker_of_trace_two_intertwines_identity A T hA htrace hT
  have hrankNullity := LinearMap.finrank_range_add_finrank_ker T.toLin'
  simp only [Module.finrank_pi, Fintype.card_fin] at hrankNullity
  omega

/-- The cokernel of a trace-two-to-identity intertwiner has dimension at least four. -/
theorem four_le_finrank_coker_of_trace_two_intertwines_identity
    (A T : Matrix (Fin 10) (Fin 10) ℂ)
    (hA : A * A = 1) (htrace : Matrix.trace A = 2) (hT : T * A = T) :
    4 ≤ Module.finrank ℂ ((Fin 10 → ℂ) ⧸ LinearMap.range T.toLin') := by
  have hrange := finrank_range_le_six_of_trace_two_intertwines_identity A T hA htrace hT
  have hcoker := Submodule.finrank_quotient_add_finrank (LinearMap.range T.toLin')
  simp only [Module.finrank_pi, Fintype.card_fin] at hcoker
  omega

/-- A map of rank six between ten-carriers has four-dimensional kernel and cokernel. -/
theorem rank_six_map_has_four_kernel_and_cokernel
    (T : Matrix (Fin 10) (Fin 10) ℂ)
    (hrange : Module.finrank ℂ (LinearMap.range T.toLin') = 6) :
    Module.finrank ℂ (LinearMap.ker T.toLin') = 4 ∧
      Module.finrank ℂ ((Fin 10 → ℂ) ⧸ LinearMap.range T.toLin') = 4 := by
  constructor
  · have hrankNullity := LinearMap.finrank_range_add_finrank_ker T.toLin'
    simp only [Module.finrank_pi, Fintype.card_fin, hrange] at hrankNullity
    omega
  · have hcoker := Submodule.finrank_quotient_add_finrank (LinearMap.range T.toLin')
    simp only [Module.finrank_pi, Fintype.card_fin, hrange] at hcoker
    omega

end GaloisForLFunctions.HTGeometry
