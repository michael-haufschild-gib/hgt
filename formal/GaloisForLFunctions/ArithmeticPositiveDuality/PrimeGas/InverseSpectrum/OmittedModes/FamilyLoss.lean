import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.OmittedModes.FamilyProjection
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.OmittedModes.OrthogonalTrace

/-! # Fourth-trace loss of a finite orthogonal family of missing modes -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open ContinuousLinearMap InnerProductSpace

variable {r : ℕ} {v : Fin r → Gas}

theorem family_square (hn : ∀ i, v i ≠ 0) (ho : ∀ i j, i ≠ j → inner ℂ (v i) (v j) = 0) :
    (projected (omitFamily v))^2 = squareHeat.val-∑ i, lineCorrection (v i) := by
  rw [projected_square]
  apply ContinuousLinearMap.ext
  intro x
  change criticalOperator ((familySpan v)ᗮ.starProjection (criticalOperator x)) =
    criticalOperator (criticalOperator x)-(∑ i, lineCorrection (v i)) x
  rw [Submodule.starProjection_orthogonal',sub_apply,one_apply_eq_self,family_projection_apply hn ho,
    map_sub,map_sum,sum_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul,lineCorrection_eq]
  change (inner ℂ (v i) (criticalOperator x)/((‖v i‖^2:ℝ):ℂ)) • criticalOperator (v i) =
    ((‖v i‖^2:ℝ):ℂ)⁻¹ • (inner ℂ (criticalOperator (v i)) x • criticalOperator (v i))
  rw [smul_smul,div_eq_inv_mul,← adjoint_inner_left criticalOperator x (v i),
    show adjoint criticalOperator = criticalOperator from critical_isPositive.isSelfAdjoint.star_eq]

/-- If the directions and their heated images are orthogonal, their fourth-trace losses add. -/
theorem traceLoss_family (hn : ∀ i, v i ≠ 0) (ho : ∀ i j, i ≠ j → inner ℂ (v i) (v j) = 0)
    (hD : ∀ i j, i ≠ j → inner ℂ (criticalOperator (v i)) (criticalOperator (v j)) = 0) :
    traceLoss (projected (omitFamily v)) = ∑ i, lineLoss (v i) := by
  have ht := orthogonal_trace_sum v hD Finset.univ
  have hs (i : Fin r) : squareHeat.val-lineCorrection (v i) = (projected (omitLine (v i)))^2 :=
    sub_sub_cancel _ _
  have hA : opTrace (squareHeat.val^2) = riemannZeta 2 := critical_fourth_trace
  have hc (i : Fin r) :
      (opTrace ((squareHeat.val-lineCorrection (v i))^2)-opTrace (squareHeat.val^2)).re =
        -(lineLoss (v i)) := by
    rw [Complex.sub_re,hA,hs,← pow_mul,← traceLoss_omitLine,traceLoss,neg_sub]
  rw [traceLoss,show (4:ℕ) = 2*2 from rfl,pow_mul,family_square hn ho,ht,Complex.add_re,Complex.re_sum]
  simp only [hc,Finset.sum_neg_distrib]
  rw [hA]
  abel

#print axioms family_square
#print axioms traceLoss_family

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
