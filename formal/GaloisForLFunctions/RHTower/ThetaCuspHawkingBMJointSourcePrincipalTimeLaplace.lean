import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMJointSourcePrincipalTimeResponse
/-! Norm-convergent transforms of the constructed causal principal evolutions. -/
open MeasureTheory Set Filter GaloisForLFunctions.HTGeometry
namespace RHTower.D4BMJointSource
noncomputable section

/-- Each genuine response has a nonempty explicit right Laplace half-plane. -/
theorem principalTimeResponse_laplace_integrable (q : XiZeroCopy) (branch : Bool) (a : ℂ)
    (i : Fin 3) (w : ℂ) (hw : principalResponseGrowth q i < w.re) :
    IntegrableOn (fun τ : ℝ => Complex.exp (-w*(τ:ℂ)) • principalTimeResponse q branch a i τ) (Ioi 0) := by
  have he := (integrableOn_exp_mul_Ioi (by linarith : -w.re+principalResponseGrowth q i < 0) 0).const_mul
    (principalResponseSize q branch a i)
  apply he.mono' (((by fun_prop : Continuous (fun τ : ℝ => Complex.exp (-w*(τ:ℂ)))).smul
    (principalTimeResponse_continuous q branch a i)).aestronglyMeasurable)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with τ hτ
  change ‖Complex.exp (-w*(τ:ℂ)) • principalTimeResponse q branch a i τ‖ ≤
    principalResponseSize q branch a i*Real.exp ((-w.re+principalResponseGrowth q i)*τ)
  rw [norm_smul,Complex.norm_exp]
  have hr : (-w*(τ:ℂ)).re = -w.re*τ := by simp
  rw [hr]
  calc
    _ ≤ Real.exp (-w.re*τ)*(principalResponseSize q branch a i*
        Real.exp (principalResponseGrowth q i*|τ|)) :=
      mul_le_mul_of_nonneg_left (principalTimeResponse_bound q branch a i τ) (Real.exp_pos _).le
    _ = principalResponseSize q branch a i*Real.exp ((-w.re+principalResponseGrowth q i)*τ) := by
      rw [abs_of_pos hτ,mul_left_comm,← Real.exp_add]
      congr 2
      ring

/-- The transform is one Bochner integral of the constructed time family, not an assumed response. -/
def principalTimeLaplace (q : XiZeroCopy) (branch : Bool) (a : ℂ) (i : Fin 3) (w : ℂ) : FourierRealL2 :=
  ∫ τ in Ioi (0:ℝ), Complex.exp (-w*(τ:ℂ)) • principalTimeResponse q branch a i τ

/-- The original spatial odd constraint survives the norm-convergent response transform. -/
theorem principalTimeLaplace_reflection (q : XiZeroCopy) (branch : Bool) (a : ℂ)
    (i : Fin 3) (w : ℂ) (hw : principalResponseGrowth q i < w.re) :
    l2Reflection (principalTimeLaplace q branch a i w) = -principalTimeLaplace q branch a i w := by
  unfold principalTimeLaplace
  rw [← l2Reflection.integral_comp_comm (principalTimeResponse_laplace_integrable q branch a i w hw),
    ← integral_neg]
  apply integral_congr_ae
  filter_upwards [] with τ
  rw [map_smul,principalTimeResponse_reflection,smul_neg]

end
end RHTower.D4BMJointSource
