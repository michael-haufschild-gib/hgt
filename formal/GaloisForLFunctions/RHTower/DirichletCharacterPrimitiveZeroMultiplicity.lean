import GaloisForLFunctions.RHTower.DirichletCharacterPrimitiveEulerProduct
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

/-!
# Primitive-conductor transport of Dirichlet `L`-zero multiplicities

The global change-level identity factors an imprimitive nonprincipal Dirichlet
`L`-function into its canonical primitive-conductor `L`-function times a
finite omitted-prime Euler product.  This file proves that product analytic
and nonvanishing throughout the positive half-plane, so the analytic order at
every such point is exactly preserved.

This is the multiplicity-level input required before comparing zero divisors
or zero-density counts across primitive conductor reduction.
-/

open Complex LSeries DirichletCharacter

noncomputable section

namespace RHTower

open scoped Topology

/-- A nonprincipal Dirichlet character indexed by its literal positive
modulus.  This avoids introducing a caller-supplied nonprincipality premise
when the canonical primitive conductor is not syntactically a successor. -/
structure CGLNonprincipalCharacterAtModulus (N : ℕ) [NeZero N] where
  character : DirichletCharacter ℂ N
  nonprincipal : character ≠ 1

private theorem cglPrimitiveEulerProduct_analyticAt
    (n : ℕ) (χ : NonprincipalDirichletCharacter n) (s : ℂ) :
    AnalyticAt ℂ (cglPrimitiveEulerProduct n χ) s := by
  unfold cglPrimitiveEulerProduct
  apply Finset.analyticAt_fun_prod
  intro p hp
  apply AnalyticAt.sub
  · exact analyticAt_const
  · apply AnalyticAt.mul
    · exact analyticAt_const
    · apply AnalyticAt.cpow analyticAt_const analyticAt_id.neg
      exact Complex.natCast_mem_slitPlane.mpr
        (Nat.prime_of_mem_primeFactors hp).ne_zero

private theorem cglPrimitiveLFunction_analyticAt
    (n : ℕ) (χ : NonprincipalDirichletCharacter n) (s : ℂ) :
    AnalyticAt ℂ (cglPrimitiveLFunction n χ) s := by
  unfold cglPrimitiveLFunction
  letI : NeZero (cglPrimitiveCharacterReduction n χ).conductor :=
    ⟨Nat.ne_of_gt (cglPrimitiveCharacterReduction n χ).conductor_pos⟩
  exact (DirichletCharacter.differentiable_LFunction
    (cglPrimitiveCharacterReduction n χ).nonprincipal).analyticAt s

/-- In the positive half-plane, canonical primitive-conductor reduction
preserves the analytic order of every nonprincipal Dirichlet `L`-function. -/
theorem cglPrimitiveLFunction_analyticOrderAt_eq_input
    (n : ℕ) (χ : NonprincipalDirichletCharacter n) (s : CGLPositiveRealPartPoint) :
    analyticOrderAt (cglPrimitiveLFunction n χ) s.1 =
      analyticOrderAt (DirichletCharacter.LFunction χ.1) s.1 := by
  have hinput : DirichletCharacter.LFunction χ.1 =
      fun w => cglPrimitiveLFunction n χ w * cglPrimitiveEulerProduct n χ w := by
    funext w
    exact cglPrimitiveLFunction_changeLevel n χ w
  rw [hinput]
  change analyticOrderAt (cglPrimitiveLFunction n χ) s.1 =
    analyticOrderAt ((cglPrimitiveLFunction n χ) *
      (cglPrimitiveEulerProduct n χ)) s.1
  rw [analyticOrderAt_mul
    (cglPrimitiveLFunction_analyticAt n χ s.1)
    (cglPrimitiveEulerProduct_analyticAt n χ s.1),
    (cglPrimitiveEulerProduct_analyticAt n χ s.1).analyticOrderAt_eq_zero.mpr
      (cglPrimitiveEulerProduct_ne_zero n χ s), add_zero]

private theorem cglGammaR_analyticAt {s : ℂ} (hs : 0 < s.re) :
    AnalyticAt ℂ Gammaℝ s := by
  have hinv : AnalyticAt ℂ (fun w : ℂ => (Gammaℝ w)⁻¹) s :=
    (differentiable_Gammaℝ_inv.differentiableOn.analyticOnNhd isOpen_univ) s (Set.mem_univ s)
  have h := hinv.inv (inv_ne_zero (Gammaℝ_ne_zero_of_re_pos hs))
  have heq : (fun w : ℂ => (Gammaℝ w)⁻¹)⁻¹ = Gammaℝ := by
    ext w
    simp
  rwa [heq] at h

private theorem cglGammaFactor_ne_zero
    {N : ℕ} [NeZero N] (η : DirichletCharacter ℂ N) (s : CGLPositiveRealPartPoint) :
    DirichletCharacter.gammaFactor η s.1 ≠ 0 := by
  rcases η.even_or_odd with hη | hη
  · rw [hη.gammaFactor_def]
    exact Gammaℝ_ne_zero_of_re_pos s.2
  · rw [hη.gammaFactor_def]
    apply Gammaℝ_ne_zero_of_re_pos
    change 0 < s.1.re + 1
    linarith [s.2]

private theorem cglGammaFactor_analyticAt
    {N : ℕ} [NeZero N] (η : DirichletCharacter ℂ N) (s : CGLPositiveRealPartPoint) :
    AnalyticAt ℂ (DirichletCharacter.gammaFactor η) s.1 := by
  rcases η.even_or_odd with hη | hη
  · have hfun : DirichletCharacter.gammaFactor η = Gammaℝ := by
      funext w
      exact hη.gammaFactor_def w
    rw [hfun]
    exact cglGammaR_analyticAt s.2
  · have hfun : DirichletCharacter.gammaFactor η = fun w => Gammaℝ (w + 1) := by
      funext w
      exact hη.gammaFactor_def w
    rw [hfun]
    have hpos : 0 < (s.1 + 1).re := by
      simp only [add_re, one_re]
      linarith [s.2]
    have hshift : AnalyticAt ℂ (fun w : ℂ => w + 1) s.1 :=
      analyticAt_id.add (analyticAt_const : AnalyticAt ℂ (fun _ : ℂ => (1 : ℂ)) s.1)
    have hcomp := AnalyticAt.comp (g := Gammaℝ) (f := fun w : ℂ => w + 1) (x := s.1)
      (cglGammaR_analyticAt hpos) hshift
    simpa only [Function.comp_def] using hcomp

private theorem cglLFunction_analyticAt
    {N : ℕ} [NeZero N] (η : CGLNonprincipalCharacterAtModulus N) (s : ℂ) :
    AnalyticAt ℂ (DirichletCharacter.LFunction η.character) s :=
  (DirichletCharacter.differentiable_LFunction η.nonprincipal).analyticAt s

private theorem cglCompletedLFunction_eq_lfunction_mul_gamma
    {N : ℕ} [NeZero N] (η : CGLNonprincipalCharacterAtModulus N)
    (s : CGLPositiveRealPartPoint) :
    DirichletCharacter.completedLFunction η.character s.1 =
      DirichletCharacter.LFunction η.character s.1 *
        DirichletCharacter.gammaFactor η.character s.1 := by
  have hsne : s.1 ≠ 0 := by
    intro hzero
    have hre := congrArg Complex.re hzero
    simp only [zero_re] at hre
    linarith [s.2]
  rw [DirichletCharacter.LFunction_eq_completed_div_gammaFactor η.character s.1 (Or.inl hsne)]
  exact (div_mul_cancel₀ _ (cglGammaFactor_ne_zero η.character s)).symm

/-- In the positive half-plane, completion by the Archimedean Gamma factor
preserves the analytic order of a certified nonprincipal Dirichlet character. -/
theorem cglCompletedLFunction_analyticOrderAt_eq_lfunction
    {N : ℕ} [NeZero N] (η : CGLNonprincipalCharacterAtModulus N)
    (s : CGLPositiveRealPartPoint) :
    analyticOrderAt (DirichletCharacter.completedLFunction η.character) s.1 =
      analyticOrderAt (DirichletCharacter.LFunction η.character) s.1 := by
  have hnear : DirichletCharacter.completedLFunction η.character =ᶠ[𝓝 s.1]
      fun w => DirichletCharacter.LFunction η.character w *
        DirichletCharacter.gammaFactor η.character w := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds s.2] with w hw
    exact cglCompletedLFunction_eq_lfunction_mul_gamma η ⟨w, hw⟩
  rw [analyticOrderAt_congr hnear]
  change analyticOrderAt ((DirichletCharacter.LFunction η.character) *
    (DirichletCharacter.gammaFactor η.character)) s.1 =
      analyticOrderAt (DirichletCharacter.LFunction η.character) s.1
  rw [analyticOrderAt_mul (cglLFunction_analyticAt η s.1)
      (cglGammaFactor_analyticAt η.character s),
    (cglGammaFactor_analyticAt η.character s).analyticOrderAt_eq_zero.mpr
      (cglGammaFactor_ne_zero η.character s), add_zero]

/-- Canonical primitive-conductor reduction preserves the completed Dirichlet
`L`-function's analytic order at every point with positive real part. -/
theorem cglPrimitiveCompletedLFunction_analyticOrderAt_eq_input
    (n : ℕ) (χ : NonprincipalDirichletCharacter n) (s : CGLPositiveRealPartPoint) :
    analyticOrderAt (cglPrimitiveCompletedLFunction n χ) s.1 =
      analyticOrderAt (DirichletCharacter.completedLFunction χ.1) s.1 := by
  unfold cglPrimitiveCompletedLFunction
  letI : NeZero (cglPrimitiveCharacterReduction n χ).conductor :=
    ⟨Nat.ne_of_gt (cglPrimitiveCharacterReduction n χ).conductor_pos⟩
  calc
    analyticOrderAt (DirichletCharacter.completedLFunction
        (cglPrimitiveCharacterReduction n χ).primitiveCharacter) s.1 =
      analyticOrderAt (DirichletCharacter.LFunction
        (cglPrimitiveCharacterReduction n χ).primitiveCharacter) s.1 :=
      cglCompletedLFunction_analyticOrderAt_eq_lfunction
        ⟨(cglPrimitiveCharacterReduction n χ).primitiveCharacter,
          (cglPrimitiveCharacterReduction n χ).nonprincipal⟩ s
    _ = analyticOrderAt (cglPrimitiveLFunction n χ) s.1 := by
      unfold cglPrimitiveLFunction
      rfl
    _ = analyticOrderAt (DirichletCharacter.LFunction χ.1) s.1 :=
      cglPrimitiveLFunction_analyticOrderAt_eq_input n χ s
    _ = analyticOrderAt (DirichletCharacter.completedLFunction χ.1) s.1 :=
      (cglCompletedLFunction_analyticOrderAt_eq_lfunction ⟨χ.1, χ.2⟩ s).symm

end RHTower
