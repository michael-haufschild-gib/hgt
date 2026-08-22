import GaloisForLFunctions.RHTower.ChenGuptaLiLemma62MellinKernel
import GaloisForLFunctions.RHTower.RectangleCauchyFormula

/-!
# Chen--Gupta--Li Lemma 6.2: principal-character residue

The principal branch of CGL's first contour shift has one pole at `s = 1 + it`.
This module makes that local source calculation exact: the literal CGL
integrand is a pole-cleared entire factor divided by `s - (1 + it)`, and a
certified finite rectangle captures precisely its finite Euler-product residue.
-/

open Complex MeasureTheory Filter Set
open scoped Topology

namespace RHTower

noncomputable section

/-- The sole pole of CGL's shifted principal Dirichlet `L`-factor. -/
def cglLemma62PrincipalPole (t : ℝ) : ℂ := 1 + (t : ℂ) * I

/-- The literal principal-character integrand in CGL equation (6.3). -/
def cglLemma62PrincipalContourIntegrand (w : CGLRealSmoothBump) (N : CGLPositiveLength)
    (Q : CGLPositiveModulus) (t : ℝ) (s : ℂ) : ℂ :=
  cglLemma62MellinTransform w s * (N.value : ℂ) ^ s *
    DirichletCharacter.LFunctionTrivChar Q.value (s - (t : ℂ) * I)

/-- Entire numerator obtained by clearing the trivial-character pole. -/
def cglLemma62PrincipalPoleClearedFactor (w : CGLRealSmoothBump) (N : CGLPositiveLength)
    (Q : CGLPositiveModulus) (t : ℝ) (s : ℂ) : ℂ :=
  cglLemma62MellinTransform w s * (N.value : ℂ) ^ s *
    DirichletCharacter.LFunctionTrivChar₁ Q.value (s - (t : ℂ) * I)

/-- The finite Euler-product coefficient of the CGL principal residue. -/
def cglLemma62PrincipalResidueCoefficient (w : CGLRealSmoothBump) (N : CGLPositiveLength)
    (Q : CGLPositiveModulus) (t : ℝ) : ℂ :=
  cglLemma62MellinTransform w (cglLemma62PrincipalPole t) *
    (N.value : ℂ) ^ (cglLemma62PrincipalPole t) *
      ∏ p ∈ Q.value.primeFactors, (1 - (p : ℂ)⁻¹)

/-- The pole-cleared CGL principal numerator is entire. -/
theorem cglLemma62PrincipalPoleClearedFactor_differentiable (w : CGLRealSmoothBump)
    (N : CGLPositiveLength) (Q : CGLPositiveModulus) (t : ℝ) :
    Differentiable ℂ (cglLemma62PrincipalPoleClearedFactor w N Q t) := by
  letI : NeZero Q.value := ⟨Nat.ne_of_gt Q.positive⟩
  have hH : Differentiable ℂ (cglLemma62MellinTransform w) := fun s =>
    (cglLemma62_mellinTransform_analyticOnNhd w s (mem_univ s)).differentiableAt
  have hpow : Differentiable ℂ (fun s : ℂ => (N.value : ℂ) ^ s) := by
    exact Differentiable.cpow (differentiable_const _) differentiable_id (fun _ =>
      Complex.ofReal_mem_slitPlane.mpr (by exact_mod_cast N.positive))
  have hshift : Differentiable ℂ (fun s : ℂ => s - (t : ℂ) * I) :=
    differentiable_id.sub (differentiable_const _)
  have hL : Differentiable ℂ (fun s : ℂ =>
      DirichletCharacter.LFunctionTrivChar₁ Q.value (s - (t : ℂ) * I)) :=
    (DirichletCharacter.differentiable_LFunctionTrivChar₁ Q.value).comp hshift
  exact (hH.mul hpow).mul hL

/-- Entire analytic form of the pole-cleared CGL principal numerator. -/
theorem cglLemma62PrincipalPoleClearedFactor_analyticOnNhd (w : CGLRealSmoothBump)
    (N : CGLPositiveLength) (Q : CGLPositiveModulus) (t : ℝ) :
    AnalyticOnNhd ℂ (cglLemma62PrincipalPoleClearedFactor w N Q t) univ := by
  intro s _
  exact (cglLemma62PrincipalPoleClearedFactor_differentiable w N Q t).analyticAt s

private theorem cglLemma62PrincipalContourIntegrand_eq_poleCleared_off
    (w : CGLRealSmoothBump) (N : CGLPositiveLength) (Q : CGLPositiveModulus)
    (t : ℝ) (s : ℂ) (hs : s ≠ cglLemma62PrincipalPole t) :
    cglLemma62PrincipalContourIntegrand w N Q t s =
      cglLemma62PrincipalPoleClearedFactor w N Q t s *
        (s - cglLemma62PrincipalPole t)⁻¹ := by
  letI : NeZero Q.value := ⟨Nat.ne_of_gt Q.positive⟩
  have hshift : s - (t : ℂ) * I ≠ 1 := by
    intro h
    apply hs
    unfold cglLemma62PrincipalPole
    calc
      s = (s - (t : ℂ) * I) + (t : ℂ) * I := by ring
      _ = 1 + (t : ℂ) * I := by rw [h]
  unfold cglLemma62PrincipalContourIntegrand cglLemma62PrincipalPoleClearedFactor
  rw [DirichletCharacter.LFunctionTrivChar₁, Function.update_of_ne hshift]
  have hscalar : s - (t : ℂ) * I - 1 = s - cglLemma62PrincipalPole t := by
    unfold cglLemma62PrincipalPole
    ring
  rw [hscalar]
  field_simp [sub_ne_zero.mpr hs]

/-- Evaluating the cleared factor at CGL's sole principal pole gives exactly
the finite Euler product in the paper's residue term. -/
theorem cglLemma62PrincipalPoleClearedFactor_at_pole (w : CGLRealSmoothBump)
    (N : CGLPositiveLength) (Q : CGLPositiveModulus) (t : ℝ) :
    cglLemma62PrincipalPoleClearedFactor w N Q t (cglLemma62PrincipalPole t) =
      cglLemma62PrincipalResidueCoefficient w N Q t := by
  letI : NeZero Q.value := ⟨Nat.ne_of_gt Q.positive⟩
  unfold cglLemma62PrincipalPoleClearedFactor cglLemma62PrincipalResidueCoefficient
  have hpole : cglLemma62PrincipalPole t - (t : ℂ) * I = 1 := by
    unfold cglLemma62PrincipalPole
    ring
  rw [hpole, DirichletCharacter.LFunctionTrivChar₁, Function.update_self]

/-- Away from its unique pole, the principal CGL integrand is holomorphic on
the strip used for the first contour shift. -/
theorem cglLemma62PrincipalContourIntegrand_holomorphicOn_offPole
    (w : CGLRealSmoothBump) (N : CGLPositiveLength) (Q : CGLPositiveModulus)
    (t : ℝ) :
    DifferentiableOn ℂ
      (cglLemma62PrincipalContourIntegrand w N Q t)
      (Set.Icc (-1 : ℝ) 2 ×ℂ Set.univ \ {cglLemma62PrincipalPole t}) := by
  intro s hs
  have hsne : s ≠ cglLemma62PrincipalPole t := by
    simpa using hs.2
  have hfactor :=
    cglLemma62PrincipalPoleClearedFactor_differentiable w N Q t s
  have hden : DifferentiableAt ℂ (fun z : ℂ => z - cglLemma62PrincipalPole t) s :=
    differentiableAt_id.sub (differentiableAt_const _)
  apply (hfactor.mul (hden.inv (sub_ne_zero.mpr hsne))).differentiableWithinAt.congr
  · intro z hz
    have hzne : z ≠ cglLemma62PrincipalPole t := by
      simpa using hz.2
    exact cglLemma62PrincipalContourIntegrand_eq_poleCleared_off w N Q t z hzne
  · exact cglLemma62PrincipalContourIntegrand_eq_poleCleared_off w N Q t s hsne

/-- The CGL principal integrand has a single simple pole, with exactly the
finite Euler-product coefficient used in Lemma 6.2. -/
theorem cglLemma62PrincipalContourIntegrand_simplePoleBigO
    (w : CGLRealSmoothBump) (N : CGLPositiveLength) (Q : CGLPositiveModulus)
    (t : ℝ) :
    (cglLemma62PrincipalContourIntegrand w N Q t - fun s =>
      cglLemma62PrincipalResidueCoefficient w N Q t /
        (s - cglLemma62PrincipalPole t)) =O[𝓝[≠] cglLemma62PrincipalPole t]
      (1 : ℂ → ℂ) := by
  have hsub :
      (fun s : ℂ => cglLemma62PrincipalPoleClearedFactor w N Q t s -
        cglLemma62PrincipalPoleClearedFactor w N Q t
          (cglLemma62PrincipalPole t)) =O[𝓝[≠] cglLemma62PrincipalPole t]
        (fun s : ℂ => s - cglLemma62PrincipalPole t) :=
    (cglLemma62PrincipalPoleClearedFactor_differentiable w N Q t
      (cglLemma62PrincipalPole t)).isBigO_sub.mono nhdsWithin_le_nhds
  have hinv :
      (fun s : ℂ => (s - cglLemma62PrincipalPole t)⁻¹) =O[𝓝[≠]
        cglLemma62PrincipalPole t]
      (fun s : ℂ => (s - cglLemma62PrincipalPole t)⁻¹) :=
    Asymptotics.isBigO_refl _ _
  have hmul := hsub.mul hinv
  refine hmul.congr' ?_ ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hsne : s ≠ cglLemma62PrincipalPole t := by
    simpa using hs
  rw [Pi.sub_apply,
    cglLemma62PrincipalContourIntegrand_eq_poleCleared_off w N Q t s hsne,
    cglLemma62PrincipalPoleClearedFactor_at_pole]
  field_simp [sub_ne_zero.mpr hsne]
  ring
  filter_upwards [self_mem_nhdsWithin] with s hs
  field_simp [sub_ne_zero.mpr (by simpa using hs)]
  rfl

/-- A rectangle certified to contain the unique principal-character pole. -/
structure CGLLemma62PrincipalRectangle (t : ℝ) where
  lower : ℂ
  upper : ℂ
  lower_re_lt_pole : lower.re < (cglLemma62PrincipalPole t).re
  pole_re_lt_upper : (cglLemma62PrincipalPole t).re < upper.re
  lower_im_lt_pole : lower.im < (cglLemma62PrincipalPole t).im
  pole_im_lt_upper : (cglLemma62PrincipalPole t).im < upper.im

private theorem cglLemma62PrincipalRectangle_bottom_ne_pole
    (r : CGLLemma62PrincipalRectangle t) (x : ℝ)
    (_hx : x ∈ uIcc r.lower.re r.upper.re) :
    (x : ℂ) + r.lower.im * I ≠ cglLemma62PrincipalPole t := by
  intro h
  have him := congrArg Complex.im h
  simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, zero_add, mul_one] at him
  linarith [r.lower_im_lt_pole]

private theorem cglLemma62PrincipalRectangle_top_ne_pole
    (r : CGLLemma62PrincipalRectangle t) (x : ℝ)
    (_hx : x ∈ uIcc r.lower.re r.upper.re) :
    (x : ℂ) + r.upper.im * I ≠ cglLemma62PrincipalPole t := by
  intro h
  have him := congrArg Complex.im h
  simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, zero_add, mul_one] at him
  linarith [r.pole_im_lt_upper]

private theorem cglLemma62PrincipalRectangle_right_ne_pole
    (r : CGLLemma62PrincipalRectangle t) (y : ℝ)
    (_hy : y ∈ uIcc r.lower.im r.upper.im) :
    (r.upper.re : ℂ) + y * I ≠ cglLemma62PrincipalPole t := by
  intro h
  have hre := congrArg Complex.re h
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero] at hre
  linarith [r.pole_re_lt_upper]

private theorem cglLemma62PrincipalRectangle_left_ne_pole
    (r : CGLLemma62PrincipalRectangle t) (y : ℝ)
    (_hy : y ∈ uIcc r.lower.im r.upper.im) :
    (r.lower.re : ℂ) + y * I ≠ cglLemma62PrincipalPole t := by
  intro h
  have hre := congrArg Complex.re h
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero] at hre
  linarith [r.lower_re_lt_pole]

/-- **Finite principal contour shift.** The literal CGL contour crosses only
the trivial-character pole, whose coefficient is the exact finite Euler
product from Lemma 6.2. -/
theorem rectIntegral_cglLemma62PrincipalContourIntegrand (w : CGLRealSmoothBump)
    (N : CGLPositiveLength) (Q : CGLPositiveModulus) (t : ℝ)
    (r : CGLLemma62PrincipalRectangle t) :
    rectIntegral (cglLemma62PrincipalContourIntegrand w N Q t) r.lower r.upper =
      2 * Real.pi * I * cglLemma62PrincipalResidueCoefficient w N Q t := by
  calc
    rectIntegral (cglLemma62PrincipalContourIntegrand w N Q t) r.lower r.upper =
        rectIntegral (fun s => cglLemma62PrincipalPoleClearedFactor w N Q t s *
          (s - cglLemma62PrincipalPole t)⁻¹) r.lower r.upper := by
      apply rectIntegral_congr (S := ({cglLemma62PrincipalPole t}ᶜ : Set ℂ))
      · intro s hs
        rw [mem_compl_iff] at hs
        exact cglLemma62PrincipalContourIntegrand_eq_poleCleared_off w N Q t s hs
      · intro x hx
        rw [mem_compl_iff]
        exact cglLemma62PrincipalRectangle_bottom_ne_pole r x hx
      · intro x hx
        rw [mem_compl_iff]
        exact cglLemma62PrincipalRectangle_top_ne_pole r x hx
      · intro y hy
        rw [mem_compl_iff]
        exact cglLemma62PrincipalRectangle_right_ne_pole r y hy
      · intro y hy
        rw [mem_compl_iff]
        exact cglLemma62PrincipalRectangle_left_ne_pole r y hy
    _ = 2 * Real.pi * I *
        cglLemma62PrincipalPoleClearedFactor w N Q t (cglLemma62PrincipalPole t) :=
      rectIntegral_cauchyFormula_entire
        (cglLemma62PrincipalPoleClearedFactor_analyticOnNhd w N Q t)
        r.lower_re_lt_pole r.pole_re_lt_upper r.lower_im_lt_pole r.pole_im_lt_upper
    _ = 2 * Real.pi * I * cglLemma62PrincipalResidueCoefficient w N Q t := by
      rw [cglLemma62PrincipalPoleClearedFactor_at_pole]

end

end RHTower
