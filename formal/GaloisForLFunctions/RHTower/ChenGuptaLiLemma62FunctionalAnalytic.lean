import GaloisForLFunctions.RHTower.ChenGuptaLiLemma62ReflectedEuler

/-!
# Chen--Gupta--Li Lemma 6.2: analytic primitive functional factor

This proves that the primitive functional-equation multiplier is holomorphic
on the finite reflected-contour displacement strip.  Reciprocal Gamma is used
in its entire form, so the strip crossing through a trivial Gamma zero creates
no pole.
-/

open Complex MeasureTheory Filter Set Asymptotics LSeries
open scoped Topology LSeries.notation BigOperators

namespace RHTower

noncomputable section

private theorem cglLemma62GammaR_differentiableAt_of_positive_re {z : ℂ} (hz : 0 < z.re) :
    DifferentiableAt ℂ Gammaℝ z := by
  have hinv : AnalyticAt ℂ (fun w : ℂ => (Gammaℝ w)⁻¹) z :=
    (differentiable_Gammaℝ_inv.differentiableOn.analyticOnNhd isOpen_univ) z (Set.mem_univ z)
  have h := hinv.differentiableAt.inv (inv_ne_zero (Gammaℝ_ne_zero_of_re_pos hz))
  have heq : (fun w : ℂ => (Gammaℝ w)⁻¹)⁻¹ = Gammaℝ := by
    ext w
    simp
  rwa [heq] at h

private theorem cglLemma62GammaFactor_differentiableAt_of_positive_re
    {n : ℕ} [NeZero n] (χ : DirichletCharacter ℂ n) {z : ℂ} (hz : 0 < z.re) :
    DifferentiableAt ℂ (DirichletCharacter.gammaFactor χ) z := by
  rcases χ.even_or_odd with heven | hodd
  · have hfun : DirichletCharacter.gammaFactor χ = Gammaℝ := by
      funext w
      exact heven.gammaFactor_def w
    rw [hfun]
    exact cglLemma62GammaR_differentiableAt_of_positive_re hz
  · have hfun : DirichletCharacter.gammaFactor χ = fun w : ℂ => Gammaℝ (w + 1) := by
      funext w
      exact hodd.gammaFactor_def w
    rw [hfun]
    have harg : 0 < (z + 1).re := by
      simp only [add_re, one_re]
      linarith
    exact (cglLemma62GammaR_differentiableAt_of_positive_re harg).comp z
      (differentiableAt_id.add (differentiableAt_const _))

private theorem cglLemma62GammaFactor_inv_differentiable
    {n : ℕ} [NeZero n] (χ : DirichletCharacter ℂ n) :
    Differentiable ℂ (fun z : ℂ => (DirichletCharacter.gammaFactor χ z)⁻¹) := by
  rcases χ.even_or_odd with heven | hodd
  · have hfun : (fun z : ℂ => (DirichletCharacter.gammaFactor χ z)⁻¹) =
        fun z : ℂ => (Gammaℝ z)⁻¹ := by
      funext z
      rw [heven.gammaFactor_def]
    rw [hfun]
    exact differentiable_Gammaℝ_inv
  · have hfun : (fun z : ℂ => (DirichletCharacter.gammaFactor χ z)⁻¹) =
        fun z : ℂ => (Gammaℝ (z + 1))⁻¹ := by
      funext z
      rw [hodd.gammaFactor_def]
    rw [hfun]
    exact differentiable_Gammaℝ_inv.comp
      (differentiable_id.add (differentiable_const _))

/-- CGL's primitive functional-equation multiplier is holomorphic on the
whole strip used to move the finite reflected Dirichlet polynomial. -/
theorem cglLemma62PrimitiveFunctionalFactor_differentiableOn
    (P : CGLLemma62PrimitiveCharacter) :
    DifferentiableOn ℂ (cglLemma62PrimitiveFunctionalFactor P)
      (GaloisForLFunctions.HTGeometry.verticalStrip (-1) (1 / 2)) := by
  letI : NeZero P.modulus.value := ⟨Nat.ne_of_gt P.modulus.positive⟩
  intro z hz
  have hqpos : 0 < (P.modulus.value : ℝ) := by exact_mod_cast P.modulus.positive
  have hexp : DifferentiableAt ℂ (fun z : ℂ => (1 / 2 : ℂ) - z) z :=
    (differentiableAt_const _).sub differentiableAt_id
  have hqpow : DifferentiableAt ℂ
      (fun z : ℂ => (P.modulus.value : ℂ) ^ ((1 / 2 : ℂ) - z)) z := by
    exact DifferentiableAt.cpow (differentiableAt_const _) hexp
      (Complex.ofReal_mem_slitPlane.mpr hqpos)
  have hright : 0 < ((1 : ℂ) - z).re := by
    simp only [sub_re, one_re]
    linarith [hz.2]
  have hgamma : DifferentiableAt ℂ
      (fun z : ℂ => P.character⁻¹.gammaFactor (1 - z)) z := by
    exact (cglLemma62GammaFactor_differentiableAt_of_positive_re P.character⁻¹ hright).comp z
      ((differentiableAt_const _).sub differentiableAt_id)
  have hinv : DifferentiableAt ℂ
      (fun z : ℂ => (P.character.gammaFactor z)⁻¹) z :=
    cglLemma62GammaFactor_inv_differentiable P.character z
  unfold cglLemma62PrimitiveFunctionalFactor
  rw [div_eq_mul_inv]
  exact ((hqpow.mul (differentiableAt_const _)).mul hgamma).mul hinv |>.differentiableWithinAt

/-- A certified point in the left half-plane used by CGL's tail displacement. -/
structure CGLLemma62LeftFunctionalPoint where
  value : ℂ
  upper : value.re ≤ -1

/-- CGL's primitive functional multiplier is holomorphic at every certified
left-tail point.  The numerator Gamma factor has positive real part there,
and the denominator is represented by the entire reciprocal Gamma factor. -/
theorem cglLemma62PrimitiveFunctionalFactor_differentiableAt_left
    (P : CGLLemma62PrimitiveCharacter) (z : CGLLemma62LeftFunctionalPoint) :
    DifferentiableAt ℂ (cglLemma62PrimitiveFunctionalFactor P) z.value := by
  letI : NeZero P.modulus.value := ⟨Nat.ne_of_gt P.modulus.positive⟩
  have hqpos : 0 < (P.modulus.value : ℝ) := by exact_mod_cast P.modulus.positive
  have hexp : DifferentiableAt ℂ (fun w : ℂ => (1 / 2 : ℂ) - w) z.value :=
    (differentiableAt_const _).sub differentiableAt_id
  have hqpow : DifferentiableAt ℂ
      (fun w : ℂ => (P.modulus.value : ℂ) ^ ((1 / 2 : ℂ) - w)) z.value := by
    exact DifferentiableAt.cpow (differentiableAt_const _) hexp
      (Complex.ofReal_mem_slitPlane.mpr hqpos)
  have hright : 0 < ((1 : ℂ) - z.value).re := by
    simp only [sub_re, one_re]
    linarith [z.upper]
  have hgamma : DifferentiableAt ℂ
      (fun w : ℂ => P.character⁻¹.gammaFactor (1 - w)) z.value := by
    exact (cglLemma62GammaFactor_differentiableAt_of_positive_re P.character⁻¹ hright).comp z.value
      ((differentiableAt_const _).sub differentiableAt_id)
  have hinv : DifferentiableAt ℂ
      (fun w : ℂ => (P.character.gammaFactor w)⁻¹) z.value :=
    cglLemma62GammaFactor_inv_differentiable P.character z.value
  unfold cglLemma62PrimitiveFunctionalFactor
  rw [div_eq_mul_inv]
  exact ((hqpow.mul (differentiableAt_const _)).mul hgamma).mul hinv

end

end RHTower
