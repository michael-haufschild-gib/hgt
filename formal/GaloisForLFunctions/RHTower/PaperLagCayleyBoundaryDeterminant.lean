import GaloisForLFunctions.RHTower.PaperLagCayleyRelativeDeterminant
import GaloisForLFunctions.RHTower.PaperLagCayleyCriticalResidue

/-! # The Fredholm determinant detects the lag boundary charge

Changing the zeroth source curvature leaves the critical logarithmic residue
unchanged. The full actual relative determinant nevertheless determines that
change injectively through a single Cayley factor.
-/

namespace RHTower.PaperLagCayley
noncomputable section
open GaloisForLFunctions GaloisForLFunctions.HTGeometry HilbertSchmidt
open _root_.Complex ContinuousLinearMap

def boundaryRelativeDefect (δ : ℝ) : Space →L[ℂ] Space :=
  perturbedObservable δ circleCoordinate * arithmeticOperator.adjoint - 1

def boundaryDeterminant (δ : ℝ) : ℂ :=
  fredholmDetOp (lpBasis ℕ) (boundaryRelativeDefect δ)

private def boundaryCoefficient (δ : ℝ) (n : ℕ) : ℂ :=
  (perturbedPhase δ n : ℂ) / arithmeticPhase n - 1

private theorem boundaryCoefficient_bound (δ : ℝ) (n : ℕ) :
    ‖boundaryCoefficient δ n‖ ≤ 2 := by
  have h := norm_sub_le ((perturbedPhase δ n : ℂ) / arithmeticPhase n) 1
  simpa only [boundaryCoefficient, norm_div, Circle.norm_coe, div_one, norm_one,
    one_add_one_eq_two] using h

private theorem boundaryCoefficient_summable (δ : ℝ) :
    Summable (fun n => ‖boundaryCoefficient δ n‖) := by
  have hs := summable_phase_discrepancy.update 0 ‖boundaryCoefficient δ 0‖
  refine hs.congr fun n => ?_
  by_cases hn : n = 0
  · subst n
    simp
  · rw [Function.update_of_ne hn]
    simpa only [boundaryCoefficient, perturbedPhase_ne_zero_index δ hn, relativePhase] using
      (norm_relativePhase_sub_one n).symm

private theorem boundaryRelativeDefect_diagonal (δ : ℝ) :
    boundaryRelativeDefect δ =
      lpDiagonalCLM (boundaryCoefficient δ) (by norm_num) (boundaryCoefficient_bound δ) := by
  ext x n
  change (perturbedPhase δ n : ℂ) * (arithmeticOperator.adjoint x n) - x n =
    ((perturbedPhase δ n : ℂ) / arithmeticPhase n - 1) * x n
  rw [arithmeticOperator_adjoint_apply]
  rw [div_eq_mul_inv]
  ring

theorem boundaryRelativeDefect_traceClass (δ : ℝ) :
    MemSchattenClass 1 (boundaryRelativeDefect δ) := by
  rw [boundaryRelativeDefect_diagonal, memSchattenClass_lpDiagonalCLM_iff _ _ _ zero_lt_one]
  simpa only [Real.rpow_one] using boundaryCoefficient_summable δ

theorem boundaryDeterminant_factor (δ : ℝ) :
    boundaryDeterminant δ =
      realCayley (source 0 + δ) / realCayley (source 0) *
        fredholmDetOp (lpBasis ℕ) (relativeOperator - 1) := by
  let q := realCayley (source 0 + δ) / realCayley (source 0)
  have hp := (hasProd_ite_eq (0 : ℕ) q).mul (hasProd_relativePhase_tail 0)
  have hp' : HasProd (fun n => 1 + boundaryCoefficient δ n)
      (q * Complex.exp ((relativeAngleTail 0 : ℂ) * I)) := by
    refine hp.congr_fun fun n => ?_
    rw [Nat.add_zero]
    by_cases hn : n = 0
    · subst n
      simp only [boundaryCoefficient, ← add_sub_assoc, add_sub_cancel_left]
      change realCayley (source 0 + δ) / (arithmeticPhase 0 : ℂ) =
        (realCayley (source 0 + δ) / realCayley (source 0)) *
          (realCayley (source 0) / (arithmeticPhase 0 : ℂ))
      have hn : realCayley (source 0) ≠ 0 := Circle.coe_ne_zero (phase 0)
      field_simp [hn, Circle.coe_ne_zero]
    · rw [if_neg hn, one_mul]
      simp only [boundaryCoefficient, perturbedPhase_ne_zero_index δ hn,
        ← add_sub_assoc, add_sub_cancel_left, relativePhase]
  rw [boundaryDeterminant, boundaryRelativeDefect_diagonal,
    fredholmDetOp_lpDiagonalCLM_of_hasProd _ _ _ (boundaryCoefficient_summable δ) hp',
    fredholmDetOp_relativeOperator_sub_one]
  rfl

theorem boundaryDeterminant_injective : Function.Injective boundaryDeterminant := by
  intro δ ε he
  rw [boundaryDeterminant_factor, boundaryDeterminant_factor] at he
  have hn : fredholmDetOp (lpBasis ℕ) (relativeOperator - 1) ≠ 0 := by
    rw [← relativeDefect_zero]
    exact fredholmDetOp_relativeDefect_ne_zero 0
  have hq := mul_right_cancel₀ hn he
  have hc : realCayley (source 0) ≠ 0 := Circle.coe_ne_zero (phase 0)
  have h := injective_realCayley ((div_left_inj' hc).mp hq)
  exact add_left_cancel h

theorem boundaryDeterminant_eq_iff (δ ε : ℝ) :
    boundaryDeterminant δ = boundaryDeterminant ε ↔ δ = ε :=
  boundaryDeterminant_injective.eq_iff

theorem boundary_determinant_separates_constant_critical_residue :
    Function.Injective boundaryDeterminant ∧ ∀ δ : ℝ,
      HasSchattenLogResidue (1 / 2)
        (perturbedObservable δ circleCoordinate - arithmeticOperator) (1 / Real.sqrt 6) :=
  ⟨boundaryDeterminant_injective, perturbed_difference_hasSchattenLogResidue_half⟩

end
end RHTower.PaperLagCayley
