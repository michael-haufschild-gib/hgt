import GaloisForLFunctions.RHTower.RectangleCauchyFormula
import GaloisForLFunctions.RHTower.RectangleWeightedCauchyResidue
import GaloisForLFunctions.RHTower.XiGuinandWeilExplicitFormula
import GaloisForLFunctions.RHTower.RectangularWindowAmplitudeAnalytic

/-!
# Contour synthesis for the Xi Guinand--Weil Cauchy algebra

The Guinand--Weil theorem in `XiGuinandWeilExplicitFormula` identifies regularized Cauchy-kernel
values on the centered Xi divisor with the continued prime--archimedean source.  This module proves
the complementary synthesis law: integrating those same kernels against an entire function around
a rectangle recovers the values of that function at the enclosed divisor points.

In particular, the square of the rectangular two-edge transform is entire.  Every finite packet of
its values on the Xi divisor is therefore exactly a contour integral of the same regularized
resolvent kernels that occur in the formal Guinand--Weil formula.  This is the finite-exhaustion
bridge needed before passing from resolvent tests to the rectangular autocorrelation test.
-/

open Complex intervalIntegral Set

namespace RHTower

noncomputable section

private theorem edgePoint_re (x c : ℝ) :
    ((x : ℂ) + (c : ℂ) * I).re = x := by simp

private theorem edgePoint_im (x c : ℝ) :
    ((x : ℂ) + (c : ℂ) * I).im = c := by simp

/-- A regularized Cauchy kernel synthesizes the value of an entire test function at a nonzero
interior point.  Algebraically,
`p⁻¹ - (p-z)⁻¹ = z / (p(z-p))`; hence the integral is Cauchy's formula applied to the entire
function `z ↦ g(z) z/p`. -/
theorem rectIntegral_regularizedCauchySynthesis_entire
    {g : ℂ → ℂ} (hg : AnalyticOnNhd ℂ g Set.univ)
    {p z₁ z₂ : ℂ} (hp0 : p ≠ 0)
    (hre₁ : z₁.re < p.re) (hre₂ : p.re < z₂.re)
    (him₁ : z₁.im < p.im) (him₂ : p.im < z₂.im) :
    rectIntegral (fun z => g z * xiCauchyRegularizedKernel z p) z₁ z₂ =
      2 * Real.pi * I * g p := by
  let F : ℂ → ℂ := fun z => g z * z * p⁻¹
  have hF : AnalyticOnNhd ℂ F Set.univ := by
    intro z hz
    exact ((hg z hz).mul analyticAt_id).mul analyticAt_const
  have hbot : ∀ x : ℝ, ((x : ℂ) + z₁.im * I) ≠ p := by
    intro x h
    have him := congrArg Complex.im h
    rw [edgePoint_im] at him
    linarith
  have htop : ∀ x : ℝ, ((x : ℂ) + z₂.im * I) ≠ p := by
    intro x h
    have him := congrArg Complex.im h
    rw [edgePoint_im] at him
    linarith
  have hright : ∀ y : ℝ, ((z₂.re : ℂ) + y * I) ≠ p := by
    intro y h
    have hre := congrArg Complex.re h
    rw [edgePoint_re] at hre
    linarith
  have hleft : ∀ y : ℝ, ((z₁.re : ℂ) + y * I) ≠ p := by
    intro y h
    have hre := congrArg Complex.re h
    rw [edgePoint_re] at hre
    linarith
  calc
    rectIntegral (fun z => g z * xiCauchyRegularizedKernel z p) z₁ z₂ =
        rectIntegral (fun z => F z * (z - p)⁻¹) z₁ z₂ := by
      apply rectIntegral_congr (S := {z : ℂ | z ≠ p})
      · intro z hz
        dsimp only [F]
        unfold xiCauchyRegularizedKernel
        field_simp [hp0, sub_ne_zero.mpr hz, sub_ne_zero.mpr hz.symm]
        ring
      · intro x _
        exact hbot x
      · intro x _
        exact htop x
      · intro y _
        exact hright y
      · intro y _
        exact hleft y
    _ = 2 * Real.pi * I * F p :=
      rectIntegral_cauchyFormula_entire hF hre₁ hre₂ him₁ him₂
    _ = 2 * Real.pi * I * g p := by
      dsimp only [F]
      field_simp [hp0]

/-- Finite superposition form of regularized Cauchy synthesis.  Every point of the packet is
strictly inside the same rectangle and is nonzero; the boundary integrability hypotheses are
discharged from these geometric facts. -/
theorem rectIntegral_finset_regularizedCauchySynthesis_entire
    {κ : Type*} (t : Finset κ)
    {g : ℂ → ℂ} (hg : AnalyticOnNhd ℂ g Set.univ)
    (p : κ → ℂ) {z₁ z₂ : ℂ}
    (hp0 : ∀ i ∈ t, p i ≠ 0)
    (hin : ∀ i ∈ t,
      z₁.re < (p i).re ∧ (p i).re < z₂.re ∧
      z₁.im < (p i).im ∧ (p i).im < z₂.im) :
    rectIntegral (fun z => ∑ i ∈ t,
        g z * xiCauchyRegularizedKernel z (p i)) z₁ z₂ =
      2 * Real.pi * I * ∑ i ∈ t, g (p i) := by
  classical
  have hgc : Continuous g := by
    rw [continuous_iff_continuousAt]
    intro z
    exact (hg z (Set.mem_univ z)).continuousAt
  have hcont {i : κ} (hi : i ∈ t) {e : ℝ → ℂ} (he : Continuous e)
      (hne : ∀ x, e x ≠ p i) :
      Continuous (fun x => g (e x) * xiCauchyRegularizedKernel (e x) (p i)) := by
    unfold xiCauchyRegularizedKernel
    exact (hgc.comp he).mul
      (continuous_const.sub ((continuous_const.sub he).inv₀
        (fun x => sub_ne_zero.mpr (hne x).symm)))
  have hb : ∀ i ∈ t, IntervalIntegrable
      (fun x : ℝ => g ((x : ℂ) + z₁.im * I) *
        xiCauchyRegularizedKernel ((x : ℂ) + z₁.im * I) (p i))
      MeasureTheory.volume z₁.re z₂.re := by
    intro i hi
    apply Continuous.intervalIntegrable
    apply hcont hi (by fun_prop)
    intro x h
    have him := congrArg Complex.im h
    rw [edgePoint_im] at him
    linarith [(hin i hi).2.2.1]
  have ht : ∀ i ∈ t, IntervalIntegrable
      (fun x : ℝ => g ((x : ℂ) + z₂.im * I) *
        xiCauchyRegularizedKernel ((x : ℂ) + z₂.im * I) (p i))
      MeasureTheory.volume z₁.re z₂.re := by
    intro i hi
    apply Continuous.intervalIntegrable
    apply hcont hi (by fun_prop)
    intro x h
    have him := congrArg Complex.im h
    rw [edgePoint_im] at him
    linarith [(hin i hi).2.2.2]
  have hr : ∀ i ∈ t, IntervalIntegrable
      (fun y : ℝ => g ((z₂.re : ℂ) + y * I) *
        xiCauchyRegularizedKernel ((z₂.re : ℂ) + y * I) (p i))
      MeasureTheory.volume z₁.im z₂.im := by
    intro i hi
    apply Continuous.intervalIntegrable
    apply hcont hi (by fun_prop)
    intro y h
    have hre := congrArg Complex.re h
    rw [edgePoint_re] at hre
    linarith [(hin i hi).2.1]
  have hl : ∀ i ∈ t, IntervalIntegrable
      (fun y : ℝ => g ((z₁.re : ℂ) + y * I) *
        xiCauchyRegularizedKernel ((z₁.re : ℂ) + y * I) (p i))
      MeasureTheory.volume z₁.im z₂.im := by
    intro i hi
    apply Continuous.intervalIntegrable
    apply hcont hi (by fun_prop)
    intro y h
    have hre := congrArg Complex.re h
    rw [edgePoint_re] at hre
    linarith [(hin i hi).1]
  rw [rectIntegral_finsetSum t
    (fun i z => g z * xiCauchyRegularizedKernel z (p i)) z₁ z₂ hb ht hr hl]
  calc
    ∑ i ∈ t, rectIntegral
        (fun z => g z * xiCauchyRegularizedKernel z (p i)) z₁ z₂ =
        ∑ i ∈ t, 2 * Real.pi * I * g (p i) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact rectIntegral_regularizedCauchySynthesis_entire hg (hp0 i hi)
        (hin i hi).1 (hin i hi).2.1 (hin i hi).2.2.1 (hin i hi).2.2.2
    _ = 2 * Real.pi * I * ∑ i ∈ t, g (p i) := by
      rw [Finset.mul_sum]

/-- The bilateral rectangular two-edge transform is entire. -/
theorem rectangularTwoEdgeTransform_differentiable (L a : ℝ) :
    Differentiable ℂ (rectangularTwoEdgeTransform L a) := by
  unfold rectangularTwoEdgeTransform
  have hpos : Differentiable ℂ (fun w : ℂ => Complex.exp ((a : ℂ) * w)) :=
    Complex.differentiable_exp.comp ((differentiable_const _).mul differentiable_id)
  have hneg : Differentiable ℂ (fun w : ℂ => Complex.exp (-(a : ℂ) * w)) :=
    Complex.differentiable_exp.comp ((differentiable_const _).mul differentiable_id)
  have hamp := rectangularWindowAmplitude_differentiable L
  exact (hpos.mul hamp).add (hneg.mul (hamp.comp differentiable_neg))

/-- The squared rectangular Xi test is entire. -/
theorem xiRectangularTwoEdgeTransform_sq_analyticOnNhd (L a : ℝ) :
    AnalyticOnNhd ℂ (fun z => xiRectangularTwoEdgeTransform L a z ^ 2) Set.univ := by
  have hlin : Differentiable ℂ (fun z : ℂ => I * z) :=
    (differentiable_const _).mul differentiable_id
  have hxi : Differentiable ℂ (xiRectangularTwoEdgeTransform L a) := by
    simpa [xiRectangularTwoEdgeTransform] using
      (rectangularTwoEdgeTransform_differentiable L a).comp hlin
  exact (hxi.pow 2).differentiableOn.analyticOnNhd isOpen_univ

/-- **Finite rectangular Xi-value synthesis.**  A finite packet of squared rectangular test
values on the multiplicity-exact Xi divisor is exactly the rectangle contour integral of its
regularized Cauchy superposition.  These are precisely the kernels on which the formal
Guinand--Weil explicit formula is already available. -/
theorem rectIntegral_finset_xiRectangularTwoEdgeKernel_eq
    (t : Finset XiZeroCopy) (L a : ℝ) {z₁ z₂ : ℂ}
    (hin : ∀ q ∈ t,
      z₁.re < (xiSpectralPoint q).re ∧ (xiSpectralPoint q).re < z₂.re ∧
      z₁.im < (xiSpectralPoint q).im ∧ (xiSpectralPoint q).im < z₂.im) :
    rectIntegral (fun z => ∑ q ∈ t,
        xiRectangularTwoEdgeTransform L a z ^ 2 *
          xiCauchyRegularizedKernel z (xiSpectralPoint q)) z₁ z₂ =
      2 * Real.pi * I * ∑ q ∈ t,
        xiRectangularTwoEdgeTransform L a (xiSpectralPoint q) ^ 2 := by
  exact rectIntegral_finset_regularizedCauchySynthesis_entire t
    (xiRectangularTwoEdgeTransform_sq_analyticOnNhd L a) xiSpectralPoint
    (fun q _ => xiSpectralPoint_ne_zero q) hin

/-- **Xi logarithmic-trace contour extraction.**  Given a complete finite factorization of `XiC`
on a neighbourhood of a rectangle, the contour integral of an entire weight against the full Xi
relative resolvent trace is the multiplicity-weighted value sum over the enclosed factors.  The
factorization itself proves that `XiC` is nonzero on the boundary. -/
theorem rectIntegral_xiRelativeResolventTrace_of_factorization
    {κ : Type*} (t : Finset κ) (ρ : κ → ℂ) (m : κ → ℕ)
    {g h : ℂ → ℂ} (hg : AnalyticOnNhd ℂ g Set.univ)
    {z₁ z₂ : ℂ} {U : Set ℂ}
    (hUopen : IsOpen U)
    (hin : ∀ i ∈ t, z₁.re < (ρ i).re ∧ (ρ i).re < z₂.re ∧
      z₁.im < (ρ i).im ∧ (ρ i).im < z₂.im)
    (hsub : (uIcc z₁.re z₂.re ×ℂ uIcc z₁.im z₂.im) ⊆ U)
    (hh : AnalyticOnNhd ℂ h U) (hh0 : ∀ z ∈ U, h z ≠ 0)
    (hfact : ∀ z ∈ U, XiC z = (∏ i ∈ t, (z - ρ i) ^ m i) * h z) :
    rectIntegral (fun z => g z * xiRelativeResolventTrace z) z₁ z₂ =
      2 * Real.pi * I * ∑ i ∈ t, (m i : ℂ) * g (ρ i) := by
  classical
  set S : Set ℂ := {z : ℂ | z ∈ U ∧ ∀ i ∈ t, z ≠ ρ i} with hS
  have hbot : ∀ x ∈ uIcc z₁.re z₂.re, ((x : ℂ) + z₁.im * I) ∈ S := by
    intro x hx
    refine ⟨hsub (Complex.mem_reProdIm.mpr
      ⟨by rw [edgePoint_re]; exact hx,
        by rw [edgePoint_im]; exact left_mem_uIcc⟩), fun i hi he => ?_⟩
    have := congrArg Complex.im he
    rw [edgePoint_im] at this
    linarith [(hin i hi).2.2.1]
  have htop : ∀ x ∈ uIcc z₁.re z₂.re, ((x : ℂ) + z₂.im * I) ∈ S := by
    intro x hx
    refine ⟨hsub (Complex.mem_reProdIm.mpr
      ⟨by rw [edgePoint_re]; exact hx,
        by rw [edgePoint_im]; exact right_mem_uIcc⟩), fun i hi he => ?_⟩
    have := congrArg Complex.im he
    rw [edgePoint_im] at this
    linarith [(hin i hi).2.2.2]
  have hright : ∀ y ∈ uIcc z₁.im z₂.im, ((z₂.re : ℂ) + y * I) ∈ S := by
    intro y hy
    refine ⟨hsub (Complex.mem_reProdIm.mpr
      ⟨by rw [edgePoint_re]; exact right_mem_uIcc,
        by rw [edgePoint_im]; exact hy⟩), fun i hi he => ?_⟩
    have := congrArg Complex.re he
    rw [edgePoint_re] at this
    linarith [(hin i hi).2.1]
  have hleft : ∀ y ∈ uIcc z₁.im z₂.im, ((z₁.re : ℂ) + y * I) ∈ S := by
    intro y hy
    refine ⟨hsub (Complex.mem_reProdIm.mpr
      ⟨by rw [edgePoint_re]; exact left_mem_uIcc,
        by rw [edgePoint_im]; exact hy⟩), fun i hi he => ?_⟩
    have := congrArg Complex.re he
    rw [edgePoint_re] at this
    linarith [(hin i hi).1]
  have hXi0 : ∀ z ∈ S, XiC z ≠ 0 := by
    rintro z ⟨hzU, hzρ⟩
    rw [hfact z hzU]
    exact mul_ne_zero
      (Finset.prod_ne_zero_iff.mpr fun i hi =>
        pow_ne_zero _ (sub_ne_zero.mpr (hzρ i hi)))
      (hh0 z hzU)
  rw [rectIntegral_congr (g₂ := fun z => g z * logDeriv XiC z)
      (fun z hz => by
        change g z * xiRelativeResolventTrace z = g z * logDeriv XiC z
        rw [logDeriv_XiC_eq_relativeResolventTrace (hXi0 z hz)])
      hbot htop hright hleft]
  exact rectIntegral_mul_logDeriv_boxCount t ρ m hg hUopen hin hsub hh hh0 hfact

/-- **Continued prime--archimedean contour extraction.**  On an admissible rectangle boundary,
the continued Guinand--Weil source trace has the same weighted contour values as the Xi logarithmic
derivative.  Thus a finite Xi factorization converts the full source trace directly into the
enclosed multiplicity-weighted entire-test values, without an infinite sum/integral interchange. -/
theorem rectIntegral_continuedPrimeArchSourceRelativeTrace_of_factorization
    {κ : Type*} (t : Finset κ) (ρ : κ → ℂ) (m : κ → ℕ)
    {g h : ℂ → ℂ} (hg : AnalyticOnNhd ℂ g Set.univ)
    {z₁ z₂ : ℂ} {U : Set ℂ}
    (hUopen : IsOpen U)
    (hin : ∀ i ∈ t, z₁.re < (ρ i).re ∧ (ρ i).re < z₂.re ∧
      z₁.im < (ρ i).im ∧ (ρ i).im < z₂.im)
    (hsub : (uIcc z₁.re z₂.re ×ℂ uIcc z₁.im z₂.im) ⊆ U)
    (hh : AnalyticOnNhd ℂ h U) (hh0 : ∀ z ∈ U, h z ≠ 0)
    (hfact : ∀ z ∈ U, XiC z = (∏ i ∈ t, (z - ρ i) ^ m i) * h z)
    (hbot : ∀ x ∈ uIcc z₁.re z₂.re,
      XiExplicitAdmissible ((x : ℂ) + z₁.im * I))
    (htop : ∀ x ∈ uIcc z₁.re z₂.re,
      XiExplicitAdmissible ((x : ℂ) + z₂.im * I))
    (hright : ∀ y ∈ uIcc z₁.im z₂.im,
      XiExplicitAdmissible ((z₂.re : ℂ) + y * I))
    (hleft : ∀ y ∈ uIcc z₁.im z₂.im,
      XiExplicitAdmissible ((z₁.re : ℂ) + y * I)) :
    rectIntegral (fun z => g z * continuedPrimeArchSourceRelativeTrace z) z₁ z₂ =
      2 * Real.pi * I * ∑ i ∈ t, (m i : ℂ) * g (ρ i) := by
  rw [rectIntegral_congr (S := {z : ℂ | XiExplicitAdmissible z})
      (fun z hz => by
        rw [continuedPrimeArchSourceRelativeTrace_eq_xiRelativeResolventTrace
          hz.re_pos hz.ne_one hz.zeta_ne])
      (fun x hx => hbot x hx) (fun x hx => htop x hx)
      (fun y hy => hright y hy) (fun y hy => hleft y hy)]
  exact rectIntegral_xiRelativeResolventTrace_of_factorization
    t ρ m hg hUopen hin hsub hh hh0 hfact

end

end RHTower
