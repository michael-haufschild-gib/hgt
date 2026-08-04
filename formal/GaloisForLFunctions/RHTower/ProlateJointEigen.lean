import GaloisForLFunctions.RHTower.PaleyWienerNorms
import GaloisForLFunctions.RHTower.ProlateBandSymmetric

/-!
# Band eigenfunctions are smooth, and the prolate action preserves them

The commuting theorem is usually read in one direction: a solution of the prolate differential
equation is carried by the band transform to another solution.  The direction the spectral theory needs
is the other one, and it is available from the same identity: if `T Phi = lambda Phi` pointwise then

```text
T (P_c Phi) = P_c (T Phi) = P_c (lambda Phi) = lambda (P_c Phi),
```

so the prolate Sturm–Liouville action maps the pointwise `lambda`-eigenspace of the band transform into
itself.  That is the invariance that will let the finite-dimensional spectral theorem produce a *joint*
eigenfunction — a band eigenfunction that also solves the prolate equation.

For the commuting theorem to apply the eigenfunction must be twice differentiable with continuous
second derivative.  That is free here, from the Paley–Wiener side: the band transform of a continuous
function is the restriction of an entire function, hence `C^∞`, and an eigenfunction is `1/nu` times its
own band transform.

The module also records the `L²` dictionary the spectral step will use: the band class of a continuous
function transports the inner product to the interval integral, and the band operator to the band
transform.
-/

noncomputable section

attribute [local instance] MeasureTheory.Measure.Subtype.measureSpace

namespace GaloisForLFunctions.RHTower

open MeasureTheory Set intervalIntegral FourierTransform

open _root_.RHTower

/-! ## Smoothness of the band transform -/

theorem continuous_bandTransform (c : ℝ) {Φ : ℝ → ℝ} (hΦ : Continuous Φ) :
    Continuous (bandTransform c Φ) := by
  refine continuous_iff_continuousAt.mpr fun x => ?_
  exact (hasDerivAt_bandTransform c hΦ x).differentiableAt.continuousAt

/-- **The band transform is smooth.**  It is the real part of an entire function of the space variable,
by the Paley–Wiener representation of its windowed spectrum. -/
theorem contDiff_bandTransform {c : ℝ} (hc : 0 < c) {Φ : ℝ → ℝ} (hΦ : Continuous Φ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (bandTransform c Φ) := by
  set k : ℝ := c / (2 * Real.pi) with hk
  set F : ℂ → ℂ := HTGeometry.compactFourier (𝓕 (bandTrunc Φ)) (-k) k with hF
  have hentire : Differentiable ℂ F :=
    HTGeometry.differentiable_compactFourier (continuous_fourier_bandTrunc hΦ) (-k) k
  have hcomplex : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F :=
    (hentire.contDiff (n := ((⊤ : ℕ∞) : WithTop ℕ∞))).restrict_scalars ℝ
  have hinner : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun x : ℝ => ((2 * Real.pi * x : ℝ) : ℂ) :=
    Complex.ofRealCLM.contDiff.comp (contDiff_const.mul contDiff_id)
  have hcomp : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      fun x : ℝ => (F ((2 * Real.pi * x : ℝ) : ℂ)).re :=
    Complex.reCLM.contDiff.comp (hcomplex.comp hinner)
  have hfun : bandTransform c Φ = fun x : ℝ => (F ((2 * Real.pi * x : ℝ) : ℂ)).re := by
    funext x
    have hval : ((bandTransform c Φ x : ℝ) : ℂ) = F ((2 * Real.pi * x : ℝ) : ℂ) :=
      bandTransform_eq_compactFourier hc hΦ x
    rw [← hval]
    simp
  rw [hfun]
  exact hcomp

/-- **The eigenfunctions of the band operator are smooth.** -/
theorem contDiff_eigenExtension {c ν : ℝ} (hc : 0 < c) (hν : ν ≠ 0)
    {ψ : RealIntervalL2 (-1 : ℝ) 1} (heig : bandOperatorL2 c ψ = ν • ψ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (eigenExtension c ν ψ) := by
  have hΦ : Continuous (eigenExtension c ν ψ) := continuous_eigenExtension c ν ψ
  have hbt : ∀ x, bandTransform c (eigenExtension c ν ψ) x = ν * eigenExtension c ν ψ x :=
    bandTransform_eigenExtension hν heig
  have hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (bandTransform c (eigenExtension c ν ψ)) :=
    contDiff_bandTransform hc hΦ
  have hscaled : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      fun x => ν⁻¹ * bandTransform c (eigenExtension c ν ψ) x := contDiff_const.mul hsm
  have hfun : eigenExtension c ν ψ
      = fun x => ν⁻¹ * bandTransform c (eigenExtension c ν ψ) x := by
    funext x
    rw [hbt x]
    field_simp
  rw [hfun]
  exact hscaled

/-! ## The prolate action of a scaled function -/

theorem prolateSLAction_const_mul {c : ℝ} (μ : ℝ) {Φ : ℝ → ℝ} (h1 : Differentiable ℝ Φ)
    (h2 : Differentiable ℝ (deriv Φ)) (x : ℝ) :
    prolateSLAction c (fun y => μ * Φ y) x = μ * prolateSLAction c Φ x := by
  have hd1 : deriv (fun y => μ * Φ y) = fun y => μ * deriv Φ y := by
    funext y
    exact deriv_const_mul μ (h1 y)
  have hd2 : (deriv fun y => μ * deriv Φ y) = fun y => μ * deriv (deriv Φ) y := by
    funext y
    exact deriv_const_mul μ (h2 y)
  rw [prolateSLAction, prolateSLAction]
  simp only [hd1, hd2]
  ring

/-! ## The prolate action preserves the pointwise band eigenspace -/

/-- **The prolate action maps band eigenfunctions to band eigenfunctions.**  This is the commuting
theorem read in the spectral direction. -/
theorem bandTransform_prolateSLAction {c lam : ℝ} {Φ : ℝ → ℝ}
    (hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ)
    (heig : ∀ x, bandTransform c Φ x = lam * Φ x) (x : ℝ) :
    bandTransform c (prolateSLAction c Φ) x = lam * prolateSLAction c Φ x := by
  have h1 : Differentiable ℝ Φ := (contDiff_infty_iff_deriv.mp hsm).1
  have hd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (deriv Φ) := (contDiff_infty_iff_deriv.mp hsm).2
  have h2 : Differentiable ℝ (deriv Φ) := (contDiff_infty_iff_deriv.mp hd).1
  have h3 : Continuous (deriv (deriv Φ)) := ((contDiff_infty_iff_deriv.mp hd).2).continuous
  have hcomm := _root_.RHTower.slepian_commutation c x h1 h2 h3
  -- the right side of the commutation is the band transform of the prolate action
  have hright : (∫ y in (-1 : ℝ)..1, sincKernelSmooth c x y * prolateSLAction c Φ y)
      = bandTransform c (prolateSLAction c Φ) x := rfl
  -- the left side is the prolate action of the scaled function
  have hfun : bandTransform c Φ = fun y => lam * Φ y := funext heig
  rw [hright, hfun, prolateSLAction_const_mul lam h1 h2 x] at hcomm
  exact hcomm.symm

/-! ## The `L²` dictionary for continuous test functions -/

/-- The band inner product of two continuous test functions is their interval pairing. -/
theorem inner_bandClass_eq (f g : ℝ → ℝ) (hf : Continuous f) (hg : Continuous g) :
    (inner ℝ (bandClass f hf) (bandClass g hg) : ℝ) = ∫ x in (-1 : ℝ)..1, f x * g x := by
  rw [L2.inner_def]
  have hcongr : (∫ x : ClosedInterval (-1 : ℝ) 1,
      (inner ℝ ((bandClass f hf : RealIntervalL2 (-1 : ℝ) 1) x : ℝ)
        ((bandClass g hg : RealIntervalL2 (-1 : ℝ) 1) x : ℝ) : ℝ) ∂volume)
      = ∫ x : ClosedInterval (-1 : ℝ) 1, f (x : ℝ) * g (x : ℝ) ∂volume := by
    refine integral_congr_ae ?_
    filter_upwards [coeFn_bandClass f hf, coeFn_bandClass g hg] with x h1 h2
    rw [h1, h2]
    simp only [RCLike.inner_apply, starRingEnd_apply, star_trivial]
    ring
  rw [hcongr]
  exact integral_subtype_unit (fun x => f x * g x)

/-- The band operator on the class of a continuous test function is the band transform. -/
theorem bandOperatorL2_bandClass (c : ℝ) (Φ : ℝ → ℝ) (hΦ : Continuous Φ) :
    bandOperatorL2 c (bandClass Φ hΦ)
      = bandClass (bandTransform c Φ) (continuous_bandTransform c hΦ) := by
  rw [Lp.ext_iff]
  filter_upwards [bandOperatorL2_coeFn c (bandClass Φ hΦ),
    coeFn_bandClass (bandTransform c Φ) (continuous_bandTransform c hΦ)] with x h1 h2
  rw [h1, h2]
  have hinner : (∫ y : ClosedInterval (-1 : ℝ) 1, sincKernelSmooth c (x : ℝ) (y : ℝ)
        * ((bandClass Φ hΦ : RealIntervalL2 (-1 : ℝ) 1) y : ℝ) ∂volume)
      = ∫ y : ClosedInterval (-1 : ℝ) 1, sincKernelSmooth c (x : ℝ) (y : ℝ) * Φ (y : ℝ) ∂volume := by
    refine integral_congr_ae ?_
    filter_upwards [coeFn_bandClass Φ hΦ] with y hy
    rw [hy]
  rw [hinner, bandTransform]
  exact integral_subtype_unit (fun y => sincKernelSmooth c (x : ℝ) y * Φ y)

end GaloisForLFunctions.RHTower

end
