import GaloisForLFunctions.HTGeometry.SuperPoincareAlgebra
import GaloisForLFunctions.HTGeometry.ExteriorEulerIdentity
import GaloisForLFunctions.HTGeometry.FreeGradedCommutativeAlgebra
import Mathlib.Data.Real.Basic

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- Two exterior generators are zero-momentum supercharges. -/
def exteriorGeneratorD1N2
    {M : Type*} [AddCommGroup M] [Module ℝ M] (a b : M) :
    SuperPoincare.D1N2 (ExteriorAlgebra ℝ M) where
  supercharge0 := ExteriorAlgebra.ι ℝ a
  supercharge1 := ExteriorAlgebra.ι ℝ b
  momentum := 0
  supercharge0_sq := ExteriorAlgebra.ι_sq_zero a
  supercharge1_sq := ExteriorAlgebra.ι_sq_zero b
  mixed_anticommutator := ExteriorAlgebra.ι_mul_ι_add_swap_eq_zero a b

/-- Degree-one free graded-commutative generators are zero-momentum supercharges. -/
def freeDegreeOneGeneratorD1N2
    {G : Type*} (x y : G) :
    SuperPoincare.D1N2 (HTGeometry.DeningerFreeGCA ℝ G (fun _ => 1)) where
  supercharge0 := HTGeometry.deningerGCAι ℝ (fun _ : G => 1) x
  supercharge1 := HTGeometry.deningerGCAι ℝ (fun _ : G => 1) y
  momentum := 0
  supercharge0_sq := HTGeometry.deningerGCA_sq_zero
    ℝ (fun _ : G => 1) (by exact odd_one)
  supercharge1_sq := HTGeometry.deningerGCA_sq_zero
    ℝ (fun _ : G => 1) (by exact odd_one)
  mixed_anticommutator := by
    rw [HTGeometry.deningerGCA_anticomm_degreeOne
      ℝ (fun _ : G => 1) (x := x) (y := y) rfl rfl]
    exact neg_add_cancel _

end GaloisForLFunctions.HTGeometry
