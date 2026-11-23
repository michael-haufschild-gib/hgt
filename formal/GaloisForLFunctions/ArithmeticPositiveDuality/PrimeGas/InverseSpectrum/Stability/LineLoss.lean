import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing.MissingDirection
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing.RankCorrection
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.Stability.TraceBound

/-! # Two energy moments determine the trace cost of omitting a line -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open ContinuousLinearMap InnerProductSpace
open scoped InnerProductSpace

/-- The fourth-trace deficit for a line through an arbitrary wave. -/
def lineLoss (v : Gas) : ℝ :=
  2*‖squareHeat.val v‖^2/‖v‖^2-(‖criticalOperator v‖^2/‖v‖^2)^2

private theorem projected_gram (P : Projection) :
    star (projected P)*projected P = star (P.val*criticalOperator)*(P.val*criticalOperator) := by
  rw [(projected_positive P).isSelfAdjoint.star_eq,← pow_two,projected_square,star_mul,
    critical_isPositive.isSelfAdjoint.star_eq,P.property.isSelfAdjoint.star_eq,mul_assoc,
    ← mul_assoc P.val,P.property.isIdempotentElem.eq]

private theorem gram_norm {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (T : H →L[ℂ] H) (x : H) : (inner ℂ x ((star T*T) x)).re = ‖T x‖^2 := by
  change (inner ℂ x ((adjoint T) (T x))).re = _
  rw [adjoint_inner_right]
  exact inner_self_eq_norm_sq (𝕜 := ℂ) (T x)

/-- The modulus of the projected heat and the projected heat itself have the same norm on every input. -/
theorem projected_norm (P : Projection) (x : Gas) : ‖projected P x‖ = ‖P.val (criticalOperator x)‖ := by
  apply (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp
  exact ((gram_norm (projected P) x).symm.trans
    (congrArg (fun A : GasOp => (inner ℂ x (A x)).re) (projected_gram P))).trans (gram_norm _ x)

private theorem projected_complement {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (v f : H) :
    (ℂ ∙ v)ᗮ.starProjection f = f - (inner ℂ v f / ((‖v‖^2:ℝ):ℂ)) • v := by
  simp only [Submodule.starProjection_orthogonal',sub_apply,one_apply_eq_self,
    Submodule.starProjection_singleton,RCLike.ofReal_eq_complex_ofReal]

theorem line_square (v : Gas) :
    projected (omitLine v)^2 = squareHeat.val-((‖v‖^2:ℝ):ℂ)⁻¹ •
      rankOne ℂ (criticalOperator v) (criticalOperator v) := by
  rw [projected_square]
  apply ContinuousLinearMap.ext
  intro x
  change criticalOperator ((ℂ ∙ v)ᗮ.starProjection (criticalOperator x)) =
    criticalOperator (criticalOperator x) -
      ((‖v‖^2:ℝ):ℂ)⁻¹ • ((inner ℂ (criticalOperator v) x) • criticalOperator v)
  rw [projected_complement,map_sub,map_smul,smul_smul,div_eq_inv_mul,
    ← adjoint_inner_left criticalOperator x v,show adjoint criticalOperator = criticalOperator from
      critical_isPositive.isSelfAdjoint.star_eq]

private theorem norm_reading {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (x : H) :
    inner ℂ x x = ((‖x‖^2:ℝ):ℂ) := by
  rw [Complex.ofReal_pow]
  exact inner_self_eq_norm_sq_to_K x

private theorem square_reading (x : Gas) :
    inner ℂ x (squareHeat.val x) = ((‖criticalOperator x‖^2:ℝ):ℂ) := by
  change inner ℂ x (criticalOperator (criticalOperator x)) = _
  have h := adjoint_inner_left criticalOperator (criticalOperator x) x
  rw [show adjoint criticalOperator = criticalOperator from critical_isPositive.isSelfAdjoint.star_eq] at h
  exact h.symm.trans (norm_reading _)

/-- The formula holds even when the proposed omission fails to conserve. -/
theorem traceLoss_omitLine (v : Gas) : traceLoss (projected (omitLine v)) = lineLoss v := by
  have ht : opTrace (projected (omitLine v)^4) = riemannZeta 2 - (lineLoss v : ℂ) := by
    rw [show (4:ℕ) = 2*2 from rfl,pow_mul,line_square,rank_one_trace_square squareHeat,
      square_reading,norm_reading]
    change opTrace ((criticalOperator^2)^2)-2*_*(↑(‖squareHeat.val v‖^2):ℂ)+_ = _
    rw [critical_fourth_trace,lineLoss]
    push_cast
    simp only [div_eq_mul_inv]
    ring
  rw [traceLoss,ht,Complex.sub_re,Complex.ofReal_re,sub_sub_cancel]

/-- The loss varies continuously at every nonzero omitted wave. -/
theorem continuousAt_lineLoss {v : Gas} (hv : v ≠ 0) : ContinuousAt lineLoss v := by
  have hn : ‖v‖^2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr hv)
  exact ((continuousAt_const.mul (squareHeat.val.continuous.continuousAt.norm.pow 2)).div
    (continuousAt_id.norm.pow 2) hn).sub (((criticalOperator.continuous.continuousAt.norm.pow 2).div
      (continuousAt_id.norm.pow 2) hn).pow 2)

#print axioms projected_norm
#print axioms line_square
#print axioms traceLoss_omitLine
#print axioms continuousAt_lineLoss

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
