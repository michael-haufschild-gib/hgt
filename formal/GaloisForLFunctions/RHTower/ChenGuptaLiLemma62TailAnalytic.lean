import GaloisForLFunctions.RHTower.ChenGuptaLiLemma62TailContour

open Complex MeasureTheory Filter Set Asymptotics LSeries
open scoped Topology LSeries.notation BigOperators

namespace RHTower

noncomputable section

private theorem cglLemma62_ambient_inverse_nonprincipal (B : CGLLemma62InducedCharacter) :
    B.character⁻¹ ≠ 1 := by
  intro h
  apply B.nonprincipal
  calc
    B.character = (B.character⁻¹)⁻¹ := (inv_inv _).symm
    _ = (1 : DirichletCharacter ℂ B.ambient.value)⁻¹ := congrArg Inv.inv h
    _ = 1 := inv_one

/-- The analytically continued reflected tail integrand is holomorphic in every
closed strip used to move the `m > M` contour from `Re(s) = -1` to `Re(s) = -2k`. -/
theorem cglLemma62TailContourIntegrand_differentiableOn (w : CGLRealSmoothBump)
    (N : CGLPositiveLength) (B : CGLLemma62InducedCharacter) (t : ℝ) (M k : ℕ) :
    DifferentiableOn ℂ (cglLemma62TailContourIntegrand w N B t M)
      (GaloisForLFunctions.HTGeometry.verticalStrip (-2 * (k : ℝ)) (-1)) := by
  intro s hs
  have hH : DifferentiableWithinAt ℂ (cglLemma62MellinTransform w)
      (GaloisForLFunctions.HTGeometry.verticalStrip (-2 * (k : ℝ)) (-1)) s :=
    (cglLemma62_mellinTransform_analyticOnNhd w s (mem_univ s)).differentiableAt.differentiableWithinAt
  have hNne : (N.value : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt N.positive)
  have hN : DifferentiableWithinAt ℂ (fun z : ℂ => (N.value : ℂ) ^ z)
      (GaloisForLFunctions.HTGeometry.verticalStrip (-2 * (k : ℝ)) (-1)) s :=
    (differentiableAt_id.const_cpow (Or.inl hNne)).differentiableWithinAt
  have hdshift : DifferentiableWithinAt ℂ (fun z : ℂ => z - (t : ℂ) * I)
      (GaloisForLFunctions.HTGeometry.verticalStrip (-2 * (k : ℝ)) (-1)) s :=
    (differentiableAt_id.sub (differentiableAt_const _)).differentiableWithinAt
  let z : CGLLemma62LeftFunctionalPoint := ⟨s - (t : ℂ) * I, by
    simp
    linarith [hs.2]⟩
  have hP : DifferentiableWithinAt ℂ (fun w : ℂ =>
      cglLemma62PrimitiveFunctionalFactor B.primitive (w - (t : ℂ) * I))
      (GaloisForLFunctions.HTGeometry.verticalStrip (-2 * (k : ℝ)) (-1)) s := by
    simpa only [Function.comp_def] using
      DifferentiableAt.comp_differentiableWithinAt
        s (cglLemma62PrimitiveFunctionalFactor_differentiableAt_left B.primitive z) hdshift
  let e : CGLLemma62LeftEulerPoint := ⟨s - (t : ℂ) * I, by
    simp
    linarith [hs.2]⟩
  have hE : DifferentiableWithinAt ℂ (fun w : ℂ => cglLemma62EulerCorrectionAt B
      (w - (t : ℂ) * I)) (GaloisForLFunctions.HTGeometry.verticalStrip (-2 * (k : ℝ)) (-1)) s := by
    simpa only [Function.comp_def] using
      DifferentiableAt.comp_differentiableWithinAt
        s (cglLemma62EulerCorrectionAt_differentiableAt_left B e) hdshift
  have hinner : DifferentiableAt ℂ (fun z : ℂ => 1 - z + (t : ℂ) * I) s :=
    ((differentiableAt_const _).sub differentiableAt_id).add (differentiableAt_const _)
  have hL : DifferentiableWithinAt ℂ (fun z : ℂ =>
      DirichletCharacter.LFunction B.character⁻¹ (1 - z + (t : ℂ) * I))
      (GaloisForLFunctions.HTGeometry.verticalStrip (-2 * (k : ℝ)) (-1)) s :=
    ((DirichletCharacter.differentiable_LFunction (cglLemma62_ambient_inverse_nonprincipal B)
      (1 - s + (t : ℂ) * I)).comp s hinner).differentiableWithinAt
  have hD : DifferentiableWithinAt ℂ (fun z : ℂ =>
      cglLemma62DirichletHead B.character⁻¹ M (1 - z + (t : ℂ) * I))
      (GaloisForLFunctions.HTGeometry.verticalStrip (-2 * (k : ℝ)) (-1)) s := by
    simpa only [Function.comp_def] using
      ((cglLemma62DirichletHead_differentiable B.character⁻¹ M
        (1 - s + (t : ℂ) * I)).comp s hinner).differentiableWithinAt
  unfold cglLemma62TailContourIntegrand
  exact (((hH.mul hN).mul hP).mul hE).mul (hL.sub hD)

end

end RHTower
