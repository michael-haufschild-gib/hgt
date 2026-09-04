import GaloisForLFunctions.HTGeometry.OperatorExponentialCommutator
import GaloisForLFunctions.HTGeometry.SchattenCubicTriangle

open NormedSpace

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open RHTower ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [Nontrivial H]

/-- Exponentiation of a skew-adjoint generator is contractive in the exact Schatten-three norm
of its commutator with a fixed operator. -/
theorem schattenNorm_three_commutator_exp_le
    (P X : H →L[ℂ] H) (hX : X ∈ skewAdjoint (H →L[ℂ] H))
    (hC : MemSchattenClass 3 (P * X - X * P))
    (hKcpt : IsCompactOperator
      (P * exp X - exp X * P : H →L[ℂ] H)) :
    schattenNorm 3 (P * exp X - exp X * P) ≤
      schattenNorm 3 (P * X - X * P) := by
  let _ : NormedAlgebra ℚ (H →L[ℂ] H) := .restrictScalars ℚ ℂ _
  let C : H →L[ℂ] H := P * X - X * P
  let F : ℝ → H →L[ℂ] H := fun t =>
    exp ((1 - t) • X) * C * exp (t • X)
  have hF : Continuous F := by
    dsimp only [F, C]
    fun_prop
  have hCcpt : IsCompactOperator C := hC.isCompactOperator (by norm_num)
  have hFcpt : ∀ t, IsCompactOperator (F t) := by
    intro t
    have hright := hCcpt.comp_clm (exp (t • X))
    have hboth := hright.clm_comp (exp ((1 - t) • X))
    change IsCompactOperator (fun x =>
      exp ((1 - t) • X) (C (exp (t • X) x)))
    exact hboth
  have hsv : ∀ t i, singVal (F t) i ≤ singVal C i := by
    intro t i
    have hLunit : exp ((1 - t) • X) ∈ unitary (H →L[ℂ] H) :=
      NormedSpace.exp_mem_unitary_of_mem_skewAdjoint
        (skewAdjoint.smul_mem (1 - t) hX)
    have hRunit : exp (t • X) ∈ unitary (H →L[ℂ] H) :=
      NormedSpace.exp_mem_unitary_of_mem_skewAdjoint
        (skewAdjoint.smul_mem t hX)
    have hLnorm : ‖exp ((1 - t) • X)‖ = 1 := by
      have h := CStarRing.norm_mem_unitary_mul (1 : H →L[ℂ] H) hLunit
      simpa using h
    have hRnorm : ‖exp (t • X)‖ = 1 := by
      have h := CStarRing.norm_mul_mem_unitary (1 : H →L[ℂ] H) hRunit
      simpa using h
    have hF_eq : F t = exp ((1 - t) • X) ∘L (C ∘L exp (t • X)) := by
      ext x
      rfl
    rw [← approxNumber_eq_singVal (hFcpt t), ← approxNumber_eq_singVal hCcpt]
    rw [hF_eq]
    calc
      approxNumber (exp ((1 - t) • X) ∘L (C ∘L exp (t • X))) i ≤
          ‖exp ((1 - t) • X)‖ * approxNumber (C ∘L exp (t • X)) i :=
        approxNumber_comp_le_left (exp ((1 - t) • X)) (C ∘L exp (t • X)) i
      _ ≤ ‖exp ((1 - t) • X)‖ *
          (approxNumber C i * ‖exp (t • X)‖) := by
        exact mul_le_mul_of_nonneg_left
          (approxNumber_comp_le_right C (exp (t • X)) i) (norm_nonneg _)
      _ = approxNumber C i := by rw [hLnorm, hRnorm, one_mul, mul_one]
  have hIntegralCpt : IsCompactOperator
      (((∫ t : ℝ in 0..1, F t) : H →L[ℂ] H)) := by
    rw [← commutator_exp_eq_intervalIntegral_duhamel P X]
    exact hKcpt
  have hbound := schattenNorm_three_intervalIntegral_le_of_singVal_le
    F C hF hFcpt hC hsv hIntegralCpt
  rw [← commutator_exp_eq_intervalIntegral_duhamel P X] at hbound
  exact hbound

end

end GaloisForLFunctions.HTGeometry
