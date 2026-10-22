import GaloisForLFunctions.RHTower.Deninger.DeningerMeyerGlobalXiSynthesis

/-! # Actual Gaussian source regularization preserves every original class

The inverse multiplier is used only in the entire division identity. No
inverse Gaussian operator on the original source topology is asserted.
-/

noncomputable section
open Complex Set

namespace RHTower
open scoped DeningerMeyerNaturalTopology

theorem deningerMeyer_entireXiDivision_of_boundary (g : DeningerMeyerStrongLogTarget)
    (hg : (Submodule.Quotient.mk g : DeningerMeyerStrongLogCohomology) = 0) :
    ∃ H : ℂ → ℂ, Differentiable ℂ H ∧
      ∀ s, deningerMeyerStrongLogMellin g s = xi s*H s := by
  obtain ⟨f, hf⟩ := (Submodule.Quotient.mk_eq_zero
    (LinearMap.range deningerMeyerStrongLogSumLM)).mp hg
  obtain ⟨F, hF⟩ := deningerMeyerCenteredMellin_boundary_mem_XiRange f
  let H : ℂ → ℂ := fun s => F (-I*(s-1/2))
  refine ⟨H, F.property.comp (by fun_prop), ?_⟩
  intro s
  have hc : 1/2+I*(-I*(s-1/2)) = s := by
    ring_nf
    rw [I_sq]
    ring
  have he := congrArg (fun A : DeningerCompactOpenEntire => A (-I*(s-1/2))) hF
  change XiC (-I*(s-1/2))*H s =
    deningerMeyerStrongLogMellin (deningerMeyerStrongLogSumLM f) (1/2+I*(-I*(s-1/2))) at he
  rw [XiC, mul_comm (-I*(s-1/2)) I, hc, hf] at he
  exact he.symm

theorem deningerMeyer_boundary_of_entireXiDivision (g : DeningerMeyerStrongLogTarget)
    {H : ℂ → ℂ} (hH : Differentiable ℂ H)
    (hdiv : ∀ s, deningerMeyerStrongLogMellin g s = xi s*H s) :
    (Submodule.Quotient.mk g : DeningerMeyerStrongLogCohomology) = 0 := by
  apply (Submodule.Quotient.mk_eq_zero (LinearMap.range deningerMeyerStrongLogSumLM)).mpr
  exact deningerMeyerXiDivision_has_cap g hH hdiv

/-- Gaussian regularization has trivial kernel on the whole original quotient. -/
theorem deningerMeyer_gaussian_boundary_iff (g : DeningerMeyerStrongLogTarget)
    {ε : ℝ} (hε : 0 < ε) :
    (Submodule.Quotient.mk (deningerMeyerInverseMellinSource
      (deningerGaussianMellinRegularization ε (deningerMeyerStrongLogMellin g))
      (deningerMeyerStrongLogMellin_gaussianRegular g hε)) : DeningerMeyerStrongLogCohomology) = 0 ↔
    (Submodule.Quotient.mk g : DeningerMeyerStrongLogCohomology) = 0 := by
  let G := deningerMeyerInverseMellinSource
    (deningerGaussianMellinRegularization ε (deningerMeyerStrongLogMellin g))
    (deningerMeyerStrongLogMellin_gaussianRegular g hε)
  have hM (s : ℂ) : deningerMeyerStrongLogMellin G s =
      exp ((ε:ℂ)*s^2)*deningerMeyerStrongLogMellin g s :=
    deningerMeyerInverseMellinSource_mellin _ s
  constructor
  · intro hG
    obtain ⟨H, hH, hdiv⟩ := deningerMeyer_entireXiDivision_of_boundary G hG
    let E : ℂ → ℂ := fun s => exp ((ε:ℂ)*s^2)
    have hE : Differentiable ℂ E := by dsimp [E]; fun_prop
    apply deningerMeyer_boundary_of_entireXiDivision g
      (hH.div hE (fun s => exp_ne_zero _))
    intro s
    have he : E s*deningerMeyerStrongLogMellin g s = xi s*H s := (hM s).symm.trans (hdiv s)
    change deningerMeyerStrongLogMellin g s = xi s*(H s/E s)
    rw [← mul_div_assoc]
    exact (eq_div_iff (show E s ≠ 0 from exp_ne_zero _)).mpr ((mul_comm _ _).trans he)
  · intro hg
    obtain ⟨H, hH, hdiv⟩ := deningerMeyer_entireXiDivision_of_boundary g hg
    have he : Differentiable ℂ (fun s : ℂ => exp ((ε:ℂ)*s^2)) := by fun_prop
    apply deningerMeyer_boundary_of_entireXiDivision G (he.mul hH)
    intro s
    rw [hM, hdiv]
    dsimp only [Pi.mul_apply]
    ring

end RHTower
