import GaloisForLFunctions.RHTower.XiRectangleFold
import GaloisForLFunctions.HTGeometry.ArgumentVariationSignChanges

/-!
# A continuous logarithm of `ζ` along a horizontal line

Off the real axis and away from the divisor, `ζ` has no zeros on a horizontal line, so the integral

`Λ(x) = log ζ(x₀ + iT) + ∫_{x₀}^{x} (ζ'/ζ)(u + iT) du`

is a continuous logarithm of `x ↦ ζ(x + iT)`: the product `ζ(x+iT) e^{−Λ(x)}` has vanishing
derivative and value `1` at `x₀`.  Consequently the integral of `Im (ζ'/ζ)` along the segment is the
increment of `Im Λ`, and the sign-change bound on the argument applies to it.
-/

open Complex Set MeasureTheory intervalIntegral
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower

/-! ## No zeros on a horizontal line -/

theorem zeta_horizontal_ne_zero {T : ℝ} (hT : T ≠ 0)
    (hne : ∀ x : ℝ, xi ((x : ℂ) + (T : ℂ) * I) ≠ 0) (x : ℝ) :
    riemannZeta ((x : ℂ) + (T : ℂ) * I) ≠ 0 := by
  intro hzero
  refine hne x (xi_eq_zero_of_zeta_eq_zero hzero ?_ ?_)
  · rintro ⟨n, hn⟩
    have him := congrArg Complex.im hn
    simp at him
    exact hT him
  · intro h
    have him := congrArg Complex.im h
    simp at him
    exact hT him

theorem continuous_logDeriv_zeta_horizontal {T : ℝ} (hT : T ≠ 0)
    (hne : ∀ x : ℝ, riemannZeta ((x : ℂ) + (T : ℂ) * I) ≠ 0) :
    Continuous fun x : ℝ => logDeriv riemannZeta ((x : ℂ) + (T : ℂ) * I) := by
  refine continuous_iff_continuousAt.mpr fun x => ?_
  have hs1 : ((x : ℂ) + (T : ℂ) * I) ≠ 1 := by
    intro h
    have him := congrArg Complex.im h
    simp at him
    exact hT him
  have hopen : IsOpen {z : ℂ | z ≠ 1} := isOpen_ne
  have hana : AnalyticOnNhd ℂ riemannZeta {z : ℂ | z ≠ 1} :=
    DifferentiableOn.analyticOnNhd
      (fun z hz => (differentiableAt_riemannZeta hz).differentiableWithinAt) hopen
  have hZ : AnalyticAt ℂ riemannZeta ((x : ℂ) + (T : ℂ) * I) := hana _ hs1
  have hquot : AnalyticAt ℂ (fun z => deriv riemannZeta z / riemannZeta z)
      ((x : ℂ) + (T : ℂ) * I) := hZ.deriv.div hZ (hne x)
  have heq : logDeriv riemannZeta = fun z => deriv riemannZeta z / riemannZeta z := by
    funext z
    rw [logDeriv_apply]
  have hpath : ContinuousAt (fun u : ℝ => (u : ℂ) + (T : ℂ) * I) x := by fun_prop
  rw [heq]
  exact ContinuousAt.comp (f := fun u : ℝ => (u : ℂ) + (T : ℂ) * I) hquot.continuousAt hpath

/-! ## The branch -/

/-- The continuous logarithm of `ζ` along the horizontal line at height `T`, anchored at `x₀`. -/
def zetaHorizontalLog (T x₀ x : ℝ) : ℂ :=
  Complex.log (riemannZeta ((x₀ : ℂ) + (T : ℂ) * I))
    + ∫ u in x₀..x, logDeriv riemannZeta ((u : ℂ) + (T : ℂ) * I)

theorem hasDerivAt_zetaHorizontalLog {T : ℝ} (hT : T ≠ 0)
    (hne : ∀ x : ℝ, riemannZeta ((x : ℂ) + (T : ℂ) * I) ≠ 0) (x₀ x : ℝ) :
    HasDerivAt (zetaHorizontalLog T x₀)
      (logDeriv riemannZeta ((x : ℂ) + (T : ℂ) * I)) x := by
  have hc := continuous_logDeriv_zeta_horizontal hT hne
  have hint := intervalIntegral.integral_hasDerivAt_right
    (hc.intervalIntegrable x₀ x) (hc.stronglyMeasurableAtFilter _ _) hc.continuousAt
  exact HasDerivAt.const_add (Complex.log (riemannZeta ((x₀ : ℂ) + (T : ℂ) * I))) hint

theorem exp_zetaHorizontalLog {T : ℝ} (hT : T ≠ 0)
    (hne : ∀ x : ℝ, riemannZeta ((x : ℂ) + (T : ℂ) * I) ≠ 0) (x₀ x : ℝ) :
    Complex.exp (zetaHorizontalLog T x₀ x) = riemannZeta ((x : ℂ) + (T : ℂ) * I) := by
  set G : ℝ → ℂ := fun u => riemannZeta ((u : ℂ) + (T : ℂ) * I)
      * Complex.exp (-zetaHorizontalLog T x₀ u) with hG
  have hs1 : ∀ u : ℝ, ((u : ℂ) + (T : ℂ) * I) ≠ 1 := by
    intro u h
    have him := congrArg Complex.im h
    simp at him
    exact hT him
  have hpath : ∀ u : ℝ, HasDerivAt (fun v : ℝ => (v : ℂ) + (T : ℂ) * I) 1 u := by
    intro u
    have h := (Complex.ofRealCLM.hasDerivAt (x := u)).add_const ((T : ℂ) * I)
    simpa using h
  have hzeta : ∀ u : ℝ, HasDerivAt (fun v : ℝ => riemannZeta ((v : ℂ) + (T : ℂ) * I))
      (deriv riemannZeta ((u : ℂ) + (T : ℂ) * I)) u := by
    intro u
    have hz : HasDerivAt riemannZeta (deriv riemannZeta ((u : ℂ) + (T : ℂ) * I))
        ((u : ℂ) + (T : ℂ) * I) := (differentiableAt_riemannZeta (hs1 u)).hasDerivAt
    have h := (hz.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt u (hpath u)
    simpa [Function.comp_def] using h
  have hderiv : ∀ u : ℝ, HasDerivAt G 0 u := by
    intro u
    have h1 := hzeta u
    have h2 : HasDerivAt (fun v : ℝ => Complex.exp (-zetaHorizontalLog T x₀ v))
        (Complex.exp (-zetaHorizontalLog T x₀ u)
          * (-logDeriv riemannZeta ((u : ℂ) + (T : ℂ) * I))) u :=
      ((hasDerivAt_zetaHorizontalLog hT hne x₀ u).neg).cexp
    have h3 := h1.mul h2
    refine h3.congr_deriv ?_
    have hzne : riemannZeta ((u : ℂ) + (T : ℂ) * I) ≠ 0 := hne u
    rw [logDeriv_apply]
    field_simp
    ring
  have hdiff : Differentiable ℝ G := fun u => (hderiv u).differentiableAt
  have hconst := is_const_of_deriv_eq_zero hdiff (fun u => (hderiv u).deriv) x x₀
  have hval0 : G x₀ = 1 := by
    rw [hG]
    simp only [zetaHorizontalLog, intervalIntegral.integral_same, add_zero]
    rw [Complex.exp_neg, Complex.exp_log (hne x₀)]
    field_simp
    exact div_self (hne x₀)
  rw [hval0] at hconst
  have hexpne : Complex.exp (-zetaHorizontalLog T x₀ x) ≠ 0 := Complex.exp_ne_zero _
  have hGx : riemannZeta ((x : ℂ) + (T : ℂ) * I)
      * Complex.exp (-zetaHorizontalLog T x₀ x) = 1 := hconst
  rw [Complex.exp_neg] at hGx
  field_simp at hGx
  exact hGx.symm

/-! ## The argument increment -/

theorem integral_im_logDeriv_zeta_horizontal {T : ℝ} (hT : T ≠ 0)
    (hne : ∀ x : ℝ, riemannZeta ((x : ℂ) + (T : ℂ) * I) ≠ 0) (x₀ x₁ : ℝ) :
    (∫ u in x₀..x₁, (logDeriv riemannZeta ((u : ℂ) + (T : ℂ) * I)).im)
      = (zetaHorizontalLog T x₀ x₁).im - (zetaHorizontalLog T x₀ x₀).im := by
  have hc := continuous_logDeriv_zeta_horizontal hT hne
  have hdiff : (zetaHorizontalLog T x₀ x₁) - (zetaHorizontalLog T x₀ x₀)
      = ∫ u in x₀..x₁, logDeriv riemannZeta ((u : ℂ) + (T : ℂ) * I) := by
    rw [zetaHorizontalLog, zetaHorizontalLog, intervalIntegral.integral_same]
    ring
  have him : ((zetaHorizontalLog T x₀ x₁) - (zetaHorizontalLog T x₀ x₀)).im
      = (∫ u in x₀..x₁, logDeriv riemannZeta ((u : ℂ) + (T : ℂ) * I)).im := by
    rw [hdiff]
  rw [Complex.sub_im] at him
  rw [him]
  have h := ContinuousLinearMap.intervalIntegral_comp_comm Complex.imCLM
    (hc.intervalIntegrable (μ := MeasureTheory.volume) x₀ x₁)
  simpa using h

/-! ## The Backlund bound on the argument increment -/

theorem continuous_zetaHorizontalLog {T : ℝ} (hT : T ≠ 0)
    (hne : ∀ x : ℝ, riemannZeta ((x : ℂ) + (T : ℂ) * I) ≠ 0) (x₀ : ℝ) :
    Continuous (zetaHorizontalLog T x₀) :=
  continuous_iff_continuousAt.mpr fun x =>
    (hasDerivAt_zetaHorizontalLog hT hne x₀ x).continuousAt

/-- **The argument increment of `ζ` across a horizontal segment is controlled by the sign changes
of its real part.** -/
theorem abs_integral_im_logDeriv_zeta_le {T : ℝ} (hT : T ≠ 0)
    (hne : ∀ x : ℝ, riemannZeta ((x : ℂ) + (T : ℂ) * I) ≠ 0)
    {Z : Finset ℝ}
    (hZ : ∀ x ∈ Ioo (1 / 2 : ℝ) 2, (riemannZeta ((x : ℂ) + (T : ℂ) * I)).re = 0 → x ∈ Z) :
    |∫ u in (1 / 2 : ℝ)..2, (logDeriv riemannZeta ((u : ℂ) + (T : ℂ) * I)).im|
      ≤ (((Z.filter (fun z => z ∈ Ioo (1 / 2 : ℝ) 2)).card : ℝ) + 1) * Real.pi := by
  have hcL : Continuous (zetaHorizontalLog T (1 / 2)) := continuous_zetaHorizontalLog hT hne _
  have hbound := abs_im_sub_le_of_finite_re_zeros (a := (1 / 2 : ℝ)) (b := (2 : ℝ))
    (γ := fun x : ℝ => riemannZeta ((x : ℂ) + (T : ℂ) * I))
    (L := zetaHorizontalLog T (1 / 2)) (by norm_num) hcL.continuousOn
    (fun t _ => exp_zetaHorizontalLog hT hne _ t) Z hZ
  rw [integral_im_logDeriv_zeta_horizontal hT hne]
  exact hbound

end RHTower
