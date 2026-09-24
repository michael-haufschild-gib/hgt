import GaloisForLFunctions.HTGeometry.RectangleResidue

/-!
# The rectangle integral of a double pole

The square of the Cauchy kernel has the single-valued antiderivative `-(z-p)⁻¹`, so its rectangle
boundary integral telescopes to zero: a second-order pole carries no winding.  Consequently a
function whose principal part at an interior point is `A (z-p)^{-2} + B (z-p)^{-1}` has rectangle
integral `2πi B` — only the residue, the first-order coefficient, survives.

This is the missing case in the corpus's rectangle residue calculus, which covers simple poles
only (`rectIntegral_eq_two_pole_residues`, `RectangleIntegral'_eq_sumResiduesIn`).  It is what a
contour shift past the double pole of `ζ²` or of Estermann's zeta consumes.
-/

noncomputable section

namespace RHTower

open Complex intervalIntegral Set

/-- `-(z-p)⁻¹` is an antiderivative of `((z-p)²)⁻¹` off the pole. -/
private theorem hasDerivAt_negInvSub {p z : ℂ} (h : z - p ≠ 0) :
    HasDerivAt (fun w : ℂ => -(w - p)⁻¹) (((z - p) ^ 2)⁻¹) z := by
  have hd : HasDerivAt (fun w : ℂ => (w - p)⁻¹) (-1 / (z - p) ^ 2) z :=
    ((hasDerivAt_id z).sub_const p).inv h
  have hn := hd.neg
  have hval : -(-1 / (z - p) ^ 2) = ((z - p) ^ 2)⁻¹ := by
    field_simp
  rwa [hval] at hn

/-- A horizontal edge integral of the squared Cauchy kernel. -/
private theorem integral_horizontal_sq {p : ℂ} {h a b : ℝ}
    (hne : ∀ x ∈ uIcc a b, ((x : ℂ) + h * I) - p ≠ 0) :
    (∫ x in a..b, (((x : ℂ) + h * I - p) ^ 2)⁻¹)
      = -((b : ℂ) + h * I - p)⁻¹ + ((a : ℂ) + h * I - p)⁻¹ := by
  have hHD : ∀ x ∈ uIcc a b,
      HasDerivAt (fun x : ℝ => -(((x : ℂ) + h * I - p))⁻¹)
        ((((x : ℂ) + h * I - p) ^ 2)⁻¹) x := by
    intro x hx
    have hin : HasDerivAt (fun x : ℝ => (x : ℂ) + (h : ℂ) * I) 1 x := by
      simpa using ((Complex.ofRealCLM.hasDerivAt (x := x)).add_const ((h : ℂ) * I))
    have hout := hasDerivAt_negInvSub (hne x hx)
    have hcomp := hout.comp x hin
    have hfun :
        ((fun w : ℂ => -(w - p)⁻¹) ∘ fun y : ℝ => (y : ℂ) + (h : ℂ) * I) =
        (fun y : ℝ => -(((y : ℂ) + h * I - p))⁻¹) := by
      apply _root_.funext; intro y; rfl
    rw [← hfun]
    simpa only [mul_one] using hcomp
  have hcont : ContinuousOn (fun x : ℝ => (((x : ℂ) + h * I - p) ^ 2)⁻¹) (uIcc a b) :=
    (continuousOn_of_forall_continuousAt (fun x => by fun_prop)).inv₀
      (fun x hx => pow_ne_zero 2 (hne x hx))
  rw [integral_eq_sub_of_hasDerivAt hHD hcont.intervalIntegrable]
  ring

/-- A vertical edge integral of the squared Cauchy kernel, weighted by `I` as in the rectangle
boundary. -/
private theorem integral_vertical_sq {p : ℂ} {v a b : ℝ}
    (hne : ∀ y ∈ uIcc a b, ((v : ℂ) + y * I) - p ≠ 0) :
    I • (∫ y in a..b, (((v : ℂ) + y * I - p) ^ 2)⁻¹)
      = -((v : ℂ) + b * I - p)⁻¹ + ((v : ℂ) + a * I - p)⁻¹ := by
  have hHD : ∀ y ∈ uIcc a b,
      HasDerivAt (fun y : ℝ => -I * -(((v : ℂ) + y * I - p))⁻¹)
        ((((v : ℂ) + y * I - p) ^ 2)⁻¹) y := by
    intro y hy
    have hin : HasDerivAt (fun y : ℝ => (v : ℂ) + (y : ℂ) * I) I y := by
      have hmul : HasDerivAt (fun y : ℝ => (y : ℂ) * I) I y := by
        simpa using (Complex.ofRealCLM.hasDerivAt (x := y)).mul_const I
      simpa using hmul.const_add ((v : ℂ))
    have hout := hasDerivAt_negInvSub (hne y hy)
    have hchain := hout.comp y hin
    have hfun :
        ((fun w : ℂ => -(w - p)⁻¹) ∘ fun z : ℝ => (v : ℂ) + (z : ℂ) * I) =
        (fun z : ℝ => -(((v : ℂ) + z * I - p))⁻¹) := by
      apply _root_.funext; intro z; rfl
    rw [hfun] at hchain
    have hscaled := hchain.const_mul (-I)
    have hval : -I * ((((v : ℂ) + y * I - p) ^ 2)⁻¹ * I)
        = (((v : ℂ) + y * I - p) ^ 2)⁻¹ := by
      have : (-I) * I = (1 : ℂ) := by rw [neg_mul, Complex.I_mul_I, neg_neg]
      calc -I * ((((v : ℂ) + y * I - p) ^ 2)⁻¹ * I)
          = ((-I) * I) * (((v : ℂ) + y * I - p) ^ 2)⁻¹ := by ring
        _ = (((v : ℂ) + y * I - p) ^ 2)⁻¹ := by rw [this, one_mul]
    simpa [hval] using hscaled
  have hcont : ContinuousOn (fun y : ℝ => (((v : ℂ) + y * I - p) ^ 2)⁻¹) (uIcc a b) :=
    (continuousOn_of_forall_continuousAt (fun y => by fun_prop)).inv₀
      (fun y hy => pow_ne_zero 2 (hne y hy))
  rw [integral_eq_sub_of_hasDerivAt hHD hcont.intervalIntegrable, smul_eq_mul]
  field_simp
  ring_nf
  rw [Complex.I_sq]
  ring

/-- **The rectangle integral of a second-order pole vanishes.** -/
theorem rectIntegral_cauchyKernelSq {p z₁ z₂ : ℂ}
    (hre1 : z₁.re < p.re) (hre2 : p.re < z₂.re)
    (him1 : z₁.im < p.im) (him2 : p.im < z₂.im) :
    rectIntegral (fun z => ((z - p) ^ 2)⁻¹) z₁ z₂ = 0 := by
  have hbot : ∀ x ∈ uIcc z₁.re z₂.re, ((x : ℂ) + z₁.im * I) - p ≠ 0 := by
    intro x _ heq
    have him := congrArg Complex.im (sub_eq_zero.mp heq)
    simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, zero_add, mul_one] at him
    linarith
  have htop : ∀ x ∈ uIcc z₁.re z₂.re, ((x : ℂ) + z₂.im * I) - p ≠ 0 := by
    intro x _ heq
    have him := congrArg Complex.im (sub_eq_zero.mp heq)
    simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, zero_add, mul_one] at him
    linarith
  have hright : ∀ y ∈ uIcc z₁.im z₂.im, ((z₂.re : ℂ) + y * I) - p ≠ 0 := by
    intro y _ heq
    have hre := congrArg Complex.re (sub_eq_zero.mp heq)
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero] at hre
    linarith
  have hleft : ∀ y ∈ uIcc z₁.im z₂.im, ((z₁.re : ℂ) + y * I) - p ≠ 0 := by
    intro y _ heq
    have hre := congrArg Complex.re (sub_eq_zero.mp heq)
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero] at hre
    linarith
  rw [rectIntegral, integral_horizontal_sq hbot, integral_horizontal_sq htop,
    integral_vertical_sq hright, integral_vertical_sq hleft]
  ring

/-- **The rectangle residue theorem for a second-order pole.**  Only the first-order coefficient
of the principal part contributes; the second-order term has a single-valued antiderivative and
carries no winding.  The regular part need only be analytic on a neighbourhood of the closed
rectangle. -/
theorem rectIntegral_eq_double_pole_residue_on
    {F R : ℂ → ℂ} {p A B z₁ z₂ : ℂ} {U : Set ℂ}
    (hp1 : z₁.re < p.re) (hp2 : p.re < z₂.re)
    (hp3 : z₁.im < p.im) (hp4 : p.im < z₂.im)
    (hsub : (uIcc z₁.re z₂.re ×ℂ uIcc z₁.im z₂.im) ⊆ U)
    (hR : AnalyticOnNhd ℂ R U)
    (hdecomp : ∀ z, z ≠ p → F z = A * ((z - p) ^ 2)⁻¹ + (B * (z - p)⁻¹ + R z)) :
    rectIntegral F z₁ z₂ = 2 * Real.pi * I * B := by
  have hbot : ∀ x ∈ uIcc z₁.re z₂.re, ((x : ℂ) + z₁.im * I) ≠ p := by
    intro x _ heq
    have him := congrArg Complex.im heq
    simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, zero_add, mul_one] at him
    linarith
  have htop : ∀ x ∈ uIcc z₁.re z₂.re, ((x : ℂ) + z₂.im * I) ≠ p := by
    intro x _ heq
    have him := congrArg Complex.im heq
    simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, zero_add, mul_one] at him
    linarith
  have hright : ∀ y ∈ uIcc z₁.im z₂.im, ((z₂.re : ℂ) + y * I) ≠ p := by
    intro y _ heq
    have hre := congrArg Complex.re heq
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero] at hre
    linarith
  have hleft : ∀ y ∈ uIcc z₁.im z₂.im, ((z₁.re : ℂ) + y * I) ≠ p := by
    intro y _ heq
    have hre := congrArg Complex.re heq
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero] at hre
    linarith
  have hmb : ∀ x ∈ uIcc z₁.re z₂.re,
      ((x : ℂ) + z₁.im * I) ∈ (uIcc z₁.re z₂.re ×ℂ uIcc z₁.im z₂.im) := by
    intro x hx
    refine Complex.mem_reProdIm.mpr ⟨?_, ?_⟩
    · simpa using hx
    · simp
  have hmt : ∀ x ∈ uIcc z₁.re z₂.re,
      ((x : ℂ) + z₂.im * I) ∈ (uIcc z₁.re z₂.re ×ℂ uIcc z₁.im z₂.im) := by
    intro x hx
    refine Complex.mem_reProdIm.mpr ⟨?_, ?_⟩
    · simpa using hx
    · simp
  have hmr : ∀ y ∈ uIcc z₁.im z₂.im,
      ((z₂.re : ℂ) + y * I) ∈ (uIcc z₁.re z₂.re ×ℂ uIcc z₁.im z₂.im) := by
    intro y hy
    refine Complex.mem_reProdIm.mpr ⟨?_, ?_⟩
    · simp
    · simpa using hy
  have hml : ∀ y ∈ uIcc z₁.im z₂.im,
      ((z₁.re : ℂ) + y * I) ∈ (uIcc z₁.re z₂.re ×ℂ uIcc z₁.im z₂.im) := by
    intro y hy
    refine Complex.mem_reProdIm.mpr ⟨?_, ?_⟩
    · simp
    · simpa using hy
  have hkernel : ∀ {a b : ℝ} (pt : ℝ → ℂ), Continuous pt →
      ∀ (c pole : ℂ), (∀ t ∈ uIcc a b, pt t ≠ pole) →
        IntervalIntegrable (fun t => c * (pt t - pole)⁻¹) MeasureTheory.volume a b := by
    intro a b pt hpt c pole hne
    exact (continuousOn_const.mul
      ((hpt.continuousOn.sub continuousOn_const).inv₀
        (fun t ht => sub_ne_zero.mpr (hne t ht)))).intervalIntegrable
  have hkernelSq : ∀ {a b : ℝ} (pt : ℝ → ℂ), Continuous pt →
      ∀ (c pole : ℂ), (∀ t ∈ uIcc a b, pt t ≠ pole) →
        IntervalIntegrable (fun t => c * ((pt t - pole) ^ 2)⁻¹) MeasureTheory.volume a b := by
    intro a b pt hpt c pole hne
    exact (continuousOn_const.mul
      (((hpt.continuousOn.sub continuousOn_const).pow 2).inv₀
        (fun t ht => pow_ne_zero 2 (sub_ne_zero.mpr (hne t ht))))).intervalIntegrable
  have hcontR : ContinuousOn R (uIcc z₁.re z₂.re ×ℂ uIcc z₁.im z₂.im) :=
    (hR.mono hsub).continuousOn
  have hregular : ∀ {a b : ℝ} (pt : ℝ → ℂ), Continuous pt →
      (∀ t ∈ uIcc a b, pt t ∈ (uIcc z₁.re z₂.re ×ℂ uIcc z₁.im z₂.im)) →
        IntervalIntegrable (fun t => R (pt t)) MeasureTheory.volume a b := by
    intro a b pt hpt hmem
    exact (hcontR.comp hpt.continuousOn hmem).intervalIntegrable
  rw [rectIntegral_congr (S := {z : ℂ | z ≠ p})
    (fun z hz => hdecomp z hz) hbot htop hright hleft,
    rectIntegral_add
      (hkernelSq _ (by fun_prop) A p (fun x hx => hbot x hx))
      ((hkernel _ (by fun_prop) B p (fun x hx => hbot x hx)).add
        (hregular _ (by fun_prop) hmb))
      (hkernelSq _ (by fun_prop) A p (fun x hx => htop x hx))
      ((hkernel _ (by fun_prop) B p (fun x hx => htop x hx)).add
        (hregular _ (by fun_prop) hmt))
      (hkernelSq _ (by fun_prop) A p (fun y hy => hright y hy))
      ((hkernel _ (by fun_prop) B p (fun y hy => hright y hy)).add
        (hregular _ (by fun_prop) hmr))
      (hkernelSq _ (by fun_prop) A p (fun y hy => hleft y hy))
      ((hkernel _ (by fun_prop) B p (fun y hy => hleft y hy)).add
        (hregular _ (by fun_prop) hml)),
    rectIntegral_add
      (hkernel _ (by fun_prop) B p (fun x hx => hbot x hx))
      (hregular _ (by fun_prop) hmb)
      (hkernel _ (by fun_prop) B p (fun x hx => htop x hx))
      (hregular _ (by fun_prop) hmt)
      (hkernel _ (by fun_prop) B p (fun y hy => hright y hy))
      (hregular _ (by fun_prop) hmr)
      (hkernel _ (by fun_prop) B p (fun y hy => hleft y hy))
      (hregular _ (by fun_prop) hml),
    rectIntegral_const_mul, rectIntegral_cauchyKernelSq hp1 hp2 hp3 hp4,
    rectIntegral_const_mul, rectIntegral_cauchyKernel hp1 hp2 hp3 hp4,
    rectIntegral_eq_zero_of_analyticOnNhd hsub hR]
  ring

/-- The entire-regular-part form. -/
theorem rectIntegral_eq_double_pole_residue
    {F R : ℂ → ℂ} {p A B z₁ z₂ : ℂ}
    (hp1 : z₁.re < p.re) (hp2 : p.re < z₂.re)
    (hp3 : z₁.im < p.im) (hp4 : p.im < z₂.im)
    (hR : Differentiable ℂ R)
    (hdecomp : ∀ z, z ≠ p → F z = A * ((z - p) ^ 2)⁻¹ + (B * (z - p)⁻¹ + R z)) :
    rectIntegral F z₁ z₂ = 2 * Real.pi * I * B :=
  rectIntegral_eq_double_pole_residue_on hp1 hp2 hp3 hp4 (U := Set.univ)
    (fun _ _ => Set.mem_univ _) (hR.differentiableOn.analyticOnNhd isOpen_univ) hdecomp

end RHTower
