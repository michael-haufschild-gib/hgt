import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMConformalLaplacian
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMChartCoordinates

/-!
The original Mobius derivative and height law imply covariance of the actual hyperbolic Laplacian. Smooth invariant fields therefore have invariant Laplacians.
-/

open Complex Set Filter Topology UpperHalfPlane ModularGroup
open GaloisForLFunctions.HTGeometry
open scoped MatrixGroups ContDiff
namespace RHTower.D4BMModularCore
noncomputable section

/-- The actual hyperbolic chart Laplacian is covariant under the original modular Möbius action. -/
theorem chartLaplacian_modular_pullback (A : SL(2,ℤ)) (f : UpperHalfPlane → ℂ)
    (hf : ChartSmooth f) (z : UpperHalfPlane) :
    chartLaplacian (fun w => f (A • w)) z = chartLaplacian f (A • z) := by
  let G : ℂ → ℂ := fun w => ((A • ofComplex w : UpperHalfPlane):ℂ)
  have hdet : 0 < (A : GL (Fin 2) ℝ).val.det := by
    change 0 < (A : GL (Fin 2) ℝ).det.val
    simp
  have hG : ContDiffAt ℂ 2 G (z:ℂ) :=
    (UpperHalfPlane.analyticAt_smul (g := (A : GL (Fin 2) ℝ)) hdet z).contDiffAt
  have hF : ContDiffAt ℝ 2 (f ∘ ofComplex) (G (z:ℂ)) := by
    have h := (contDiffAt_infty.mp (hf (A • z))) 2
    norm_num at h
    simpa only [G,ofComplex_apply,sl_moeb] using h
  have hc := planarLaplacian_holomorphic_comp hF hG
  have hfun : (f ∘ ofComplex) ∘ G = (fun w : UpperHalfPlane => f (A • w)) ∘ ofComplex := by
    funext w
    simp only [G,Function.comp_apply,ofComplex_apply]
  rw [hfun] at hc
  have hd : deriv G (z:ℂ) = 1/(denom A z)^2 := by
    have hdetone : (A : GL (Fin 2) ℝ).val.det = 1 :=
      (Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) A).det_coe
    simpa only [G,hdetone,Complex.ofReal_one,sl_moeb] using
      UpperHalfPlane.deriv_smul (g := (A : GL (Fin 2) ℝ)) hdet z
  simp only [G,ofComplex_apply] at hc
  unfold chartLaplacian
  rw [hc,hd,← mul_assoc]
  congr 1
  rw [ModularGroup.im_smul_eq_div_normSq,Complex.ofReal_div,div_pow,
    Complex.normSq_div,Complex.normSq_one,map_pow]
  simp only [Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_pow]
  ring

/-- The actual Laplacian of a smooth modular scalar is itself modular invariant. -/
theorem chartLaplacian_invariant (f : UpperHalfPlane → ℂ) (hf : ChartSmooth f)
    (hi : ∀ γ : PSL2Z, ∀ z, f (γ • z) = f z) (γ : PSL2Z) (z : UpperHalfPlane) :
    chartLaplacian f (γ • z) = chartLaplacian f z := by
  induction γ using QuotientGroup.induction_on with
  | H A =>
    rw [PSL2Z_mk_smul,← chartLaplacian_modular_pullback A f hf z]
    have he : (fun w : UpperHalfPlane => f (A • w)) = f := by
      funext w
      simpa only [PSL2Z_mk_smul] using hi (QuotientGroup.mk A) w
    rw [he]

end
end RHTower.D4BMModularCore
