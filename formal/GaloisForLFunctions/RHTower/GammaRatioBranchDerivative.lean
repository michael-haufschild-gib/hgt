import GaloisForLFunctions.RHTower.SuzukiGammaStripBranch
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv

/-!
# The logarithmic derivative of the Gamma ratio and of its branch

The transport ratio `Γ(1+iz)/Γ(1−iz)` has the logarithmic derivative

`i(ψ(1+iz) + ψ(1−iz))`,

since `logDeriv Γ = ψ` and the two inner affine maps contribute the constant derivatives `±i`, whose
signs cancel against the quotient.  A holomorphic square root of the ratio therefore has exactly half
of it: differentiating `E² = Γ(1+iz)/Γ(1−iz)` on the open strip gives `2EE'` on the left, and
dividing by `2E`, which is nonvanishing there,

`E'(z) = E(z)·(i/2)(ψ(1+iz) + ψ(1−iz))`.

This is the only place the branch is differentiated, and it is what turns the square-root
normalisation into the half-symbol of the phase generator.
-/

open Complex

noncomputable section

namespace GaloisForLFunctions.RHTower

theorem hasDerivAt_Gamma {s : ℂ} (hs : ∀ m : ℕ, s ≠ -(m : ℂ)) :
    HasDerivAt Complex.Gamma (Complex.digamma s * Complex.Gamma s) s := by
  have hd := (Complex.differentiableAt_Gamma s hs).hasDerivAt
  have hne := Complex.Gamma_ne_zero hs
  have hlog : Complex.digamma s = deriv Complex.Gamma s / Complex.Gamma s := by
    rw [Complex.digamma_def, logDeriv_apply]
  have heq : Complex.digamma s * Complex.Gamma s = deriv Complex.Gamma s := by
    rw [hlog]
    exact div_mul_cancel₀ _ hne
  rw [heq]
  exact hd

/-- **The Gamma ratio has the digamma logarithmic derivative.** -/
theorem hasDerivAt_gammaRatio {z : ℂ} (hz : z ∈ imStrip (-1) 1) :
    HasDerivAt gammaRatio
      (gammaRatio z * (Complex.I *
        (Complex.digamma (1 + Complex.I * z) + Complex.digamma (1 - Complex.I * z)))) z := by
  obtain ⟨hp1, hp2⟩ := gammaArg_ne_pole hz
  have hlin1 : HasDerivAt (fun w : ℂ => 1 + Complex.I * w) Complex.I z := by
    simpa using ((hasDerivAt_id z).const_mul Complex.I).const_add 1
  have hlin2 : HasDerivAt (fun w : ℂ => 1 - Complex.I * w) (-Complex.I) z := by
    simpa using ((hasDerivAt_id z).const_mul Complex.I).const_sub 1
  have hg1 : HasDerivAt (fun w : ℂ => Complex.Gamma (1 + Complex.I * w))
      (Complex.digamma (1 + Complex.I * z) * Complex.Gamma (1 + Complex.I * z) * Complex.I) z :=
    (hasDerivAt_Gamma hp1).comp z hlin1
  have hg2 : HasDerivAt (fun w : ℂ => Complex.Gamma (1 - Complex.I * w))
      (Complex.digamma (1 - Complex.I * z) * Complex.Gamma (1 - Complex.I * z) * (-Complex.I)) z :=
    (hasDerivAt_Gamma hp2).comp z hlin2
  have hne2 : Complex.Gamma (1 - Complex.I * z) ≠ 0 := Complex.Gamma_ne_zero hp2
  have hdiv := hg1.div hg2 hne2
  have hfun : ((fun w : ℂ => Complex.Gamma (1 + Complex.I * w)) /
      fun w : ℂ => Complex.Gamma (1 - Complex.I * w)) = gammaRatio := by
    funext w
    rw [Pi.div_apply, gammaRatio]
  rw [hfun] at hdiv
  refine hdiv.congr_deriv ?_
  rw [gammaRatio]
  field_simp
  ring

/-- **The branch has half the logarithmic derivative.** -/
theorem hasDerivAt_gammaRatioSqrt {E : ℂ → ℂ}
    (hEdiff : DifferentiableOn ℂ E (imStrip (-1) 1))
    (hE : ∀ z ∈ imStrip (-1) 1, E z ^ (2 : ℕ) = gammaRatio z)
    (hEne : ∀ z ∈ imStrip (-1) 1, E z ≠ 0)
    {z : ℂ} (hz : z ∈ imStrip (-1) 1) :
    HasDerivAt E
      (E z * (Complex.I / 2 *
        (Complex.digamma (1 + Complex.I * z) + Complex.digamma (1 - Complex.I * z)))) z := by
  have hopen := isOpen_imStrip (-1 : ℝ) 1
  have hnhds : imStrip (-1 : ℝ) 1 ∈ nhds z := hopen.mem_nhds hz
  have hEat : DifferentiableAt ℂ E z :=
    (hEdiff.differentiableAt hnhds)
  have hsq : HasDerivAt (fun w => E w ^ (2 : ℕ)) (2 * E z * deriv E z) z := by
    have h := (hEat.hasDerivAt.pow 2)
    refine h.congr_deriv ?_
    ring
  have hcong : (fun w => E w ^ (2 : ℕ)) =ᶠ[nhds z] gammaRatio := by
    filter_upwards [hnhds] with w hw
    exact hE w hw
  have hR := hsq.congr_of_eventuallyEq hcong.symm
  have hR2 := hasDerivAt_gammaRatio hz
  have hEq : 2 * E z * deriv E z
      = gammaRatio z * (Complex.I *
        (Complex.digamma (1 + Complex.I * z) + Complex.digamma (1 - Complex.I * z))) :=
    hR.unique hR2
  have hgz : gammaRatio z = E z ^ (2 : ℕ) := (hE z hz).symm
  have hEz : E z ≠ 0 := hEne z hz
  have hval : deriv E z
      = E z * (Complex.I / 2 *
        (Complex.digamma (1 + Complex.I * z) + Complex.digamma (1 - Complex.I * z))) := by
    rw [hgz] at hEq
    field_simp at hEq ⊢
    linear_combination hEq
  rw [← hval]
  exact hEat.hasDerivAt

end GaloisForLFunctions.RHTower
