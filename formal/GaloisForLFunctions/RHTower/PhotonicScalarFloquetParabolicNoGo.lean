import GaloisForLFunctions.HTGeometry.PhotonicTimeCrystalComplexModulation
import GaloisForLFunctions.RHTower.PhotonicParabolicReturn

/-!
# Scalar photonic Floquet sources cannot realize the PTR transfer

## PTR proof-chain position

PTR needs a physical time-crystal/Maxwell source producing the non-scalar
parabolic transfer `photonicParabolic`, before its zeta-return receiver applies.
The literal complex-modulation PTC corpus supplies a scalar Floquet multiplier
`pcmFloquetMultiplier`.  This module proves that no scalar two-channel transfer
can be converted to the PTR parabolic transfer by an invertible frame.

The no-go closes the scalar-multiplier physical-source class, not coupled or
multi-tone Floquet dynamics.  Its positive survivor is exact: a viable PTR
source must contain a genuinely non-scalar two-channel coupling, in addition to
the prime-dependent data forced by `DeningerPhotonicParabolicJetBridge`.
-/

open Complex Matrix
open scoped Matrix
open GaloisForLFunctions.HTGeometry

namespace RHTower

/-- A scalar two-channel transfer commutes with every two-channel frame. -/
theorem scalar_two_by_two_commutes (μ : ℂ) (C : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix.scalar (Fin 2) μ * C = C * Matrix.scalar (Fin 2) μ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.scalar] <;> ring

/--
No scalar two-channel transfer admits an invertible frame intertwining it with
the non-scalar PTR parabolic transfer.
-/
theorem not_exists_scalar_parabolic_frame (μ : ℂ) :
    ¬ ∃ C B : Matrix (Fin 2) (Fin 2) ℂ,
      B * C = 1 ∧ C * B = 1 ∧
      Matrix.scalar (Fin 2) μ * C = C * photonicParabolic := by
  rintro ⟨C, B, hBC, hCB, hrealize⟩
  have hC : C * Matrix.scalar (Fin 2) μ = C * photonicParabolic :=
    (scalar_two_by_two_commutes _ _).symm.trans hrealize
  have hscalar : Matrix.scalar (Fin 2) μ = photonicParabolic := by
    calc
      Matrix.scalar (Fin 2) μ = 1 * Matrix.scalar (Fin 2) μ := by simp
      _ = (B * C) * Matrix.scalar (Fin 2) μ := by rw [hBC]
      _ = B * (C * Matrix.scalar (Fin 2) μ) := by rw [Matrix.mul_assoc]
      _ = B * (C * photonicParabolic) := by rw [hC]
      _ = (B * C) * photonicParabolic := by rw [Matrix.mul_assoc]
      _ = photonicParabolic := by rw [hBC, one_mul]
  have hentry := congrFun (congrFun hscalar (0 : Fin 2)) (1 : Fin 2)
  norm_num [Matrix.scalar, photonicParabolic, photonicUpper] at hentry

/-- The literal scalar complex-modulation PTC multiplier is therefore not a PTR source. -/
theorem not_exists_pcmFloquetMultiplier_parabolic_frame
    (principal b T : ℝ) :
    ¬ ∃ C B : Matrix (Fin 2) (Fin 2) ℂ,
      B * C = 1 ∧ C * B = 1 ∧
      Matrix.scalar (Fin 2) (pcmFloquetMultiplier principal b T) * C =
        C * photonicParabolic :=
  not_exists_scalar_parabolic_frame (pcmFloquetMultiplier principal b T)

end RHTower
