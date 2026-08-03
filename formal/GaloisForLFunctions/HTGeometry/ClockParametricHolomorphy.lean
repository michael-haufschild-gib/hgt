import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import GaloisForLFunctions.HTGeometry.ClockStripCauchyScale

/-!
# Derivatives of a holomorphic family depend continuously on the parameters

The iteration that solves the clock equation integrates, over the two null coordinates, an
expression containing the second derivative in the transverse variable of the previous iterate. For
those integrals to exist the integrand has to be continuous in the parameters, so one needs:

*the derivatives of a family of holomorphic functions depending continuously on parameters depend
continuously on those parameters.*

There is no such statement for `deriv` directly, and none can be proved by differentiating: the
derivative is a limit, and limits do not commute with parameters for free. Cauchy's integral formula
converts it into a statement about an integral, where continuity in a parameter is standard — the
derivative at a point is a contour integral of the function itself, and a contour integral is an
interval integral in the angle.
-/

namespace GaloisForLFunctions.HTGeometry

open Complex Metric intervalIntegral

variable {P : Type*} [TopologicalSpace P]

theorem iteratedDeriv_two (f : ℂ → ℂ) : iteratedDeriv 2 f = deriv (deriv f) := by
  rw [iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_zero]

/-- **Cauchy's formula turns a derivative into a parametric integral.** -/
theorem iteratedDeriv_eq_circleIntegral {R : ℝ} (hR : 0 < R) {z : ℂ} (n : ℕ) {w : ℂ → ℂ}
    (hwc : Continuous w) (hwd : ∀ ζ ∈ ball z R, DifferentiableAt ℂ w ζ) :
    iteratedDeriv n w z
      = (2 * Real.pi * Complex.I / (n.factorial : ℂ))⁻¹
        • ∮ ζ in C(z, R), (1 / (ζ - z) ^ (n + 1)) • w ζ := by
  have hconst : (2 * Real.pi * Complex.I / (n.factorial : ℂ)) ≠ 0 := by
    have h1 : (Real.pi : ℂ) ≠ 0 := by
      exact_mod_cast Real.pi_ne_zero
    have h2 : ((n.factorial : ℂ)) ≠ 0 := by
      exact_mod_cast Nat.factorial_ne_zero n
    simp [h1, h2, Complex.I_ne_zero]
  have h := Complex.circleIntegral_one_div_sub_center_pow_smul_of_differentiable_on_off_countable
    hR n Set.countable_empty hwc.continuousOn (fun ζ hζ => hwd ζ hζ.1)
  rw [h, smul_smul, inv_mul_cancel₀ hconst, one_smul]

/-- **The derivatives of a holomorphic family are continuous in the parameters.** -/
theorem continuous_iteratedDeriv_parametric {R : ℝ} (hR : 0 < R) {z : ℂ} (n : ℕ)
    {W : P → ℂ → ℂ} (hWc : Continuous fun q : P × ℂ => W q.1 q.2)
    (hWd : ∀ p : P, ∀ ζ ∈ ball z R, DifferentiableAt ℂ (W p) ζ) :
    Continuous fun p : P => iteratedDeriv n (W p) z := by
  have hslice : ∀ p : P, Continuous (W p) := fun p =>
    hWc.comp (continuous_const.prodMk continuous_id)
  have hRne : R ≠ 0 := hR.ne'
  -- the integrand of the contour integral, continuous jointly in the parameter and the angle
  have hint : Continuous fun q : P × ℝ =>
      deriv (circleMap z R) q.2
        • ((1 / (circleMap z R q.2 - z) ^ (n + 1)) • W q.1 (circleMap z R q.2)) := by
    have hθ : Continuous fun q : P × ℝ => circleMap z R q.2 :=
      (continuous_circleMap z R).comp continuous_snd
    have hderiv : Continuous fun q : P × ℝ => deriv (circleMap z R) q.2 := by
      have hrw : (fun q : P × ℝ => deriv (circleMap z R) q.2)
          = fun q : P × ℝ => circleMap 0 R q.2 * Complex.I := by
        funext q
        rw [deriv_circleMap]
      rw [hrw]
      exact ((continuous_circleMap 0 R).comp continuous_snd).mul continuous_const
    have hden : Continuous fun q : P × ℝ =>
        1 / (circleMap z R q.2 - z) ^ (n + 1) := by
      refine continuous_const.div ((hθ.sub continuous_const).pow (n + 1)) fun q => ?_
      exact pow_ne_zero _ (sub_ne_zero_of_ne (circleMap_ne_center hRne))
    have hval : Continuous fun q : P × ℝ => W q.1 (circleMap z R q.2) :=
      hWc.comp (continuous_fst.prodMk hθ)
    exact hderiv.smul (hden.smul hval)
  have hcirc : Continuous fun p : P =>
      ∮ ζ in C(z, R), (1 / (ζ - z) ^ (n + 1)) • W p ζ := by
    show Continuous fun p : P =>
      ∫ θ in (0 : ℝ)..(2 * Real.pi), deriv (circleMap z R) θ
        • ((1 / (circleMap z R θ - z) ^ (n + 1)) • W p (circleMap z R θ))
    exact continuous_parametric_intervalIntegral_of_continuous' hint 0 (2 * Real.pi)
  have hrw : (fun p : P => iteratedDeriv n (W p) z)
      = fun p : P => (2 * Real.pi * Complex.I / (n.factorial : ℂ))⁻¹
        • ∮ ζ in C(z, R), (1 / (ζ - z) ^ (n + 1)) • W p ζ := by
    funext p
    exact iteratedDeriv_eq_circleIntegral hR n (hslice p) (hWd p)
  rw [hrw]
  exact hcirc.const_smul ((2 * Real.pi * Complex.I / (n.factorial : ℂ))⁻¹)

/-- **The second derivative of a holomorphic family is continuous in the parameters.** This is the
form the clock iteration needs. -/
theorem continuous_deriv_deriv_parametric {R : ℝ} (hR : 0 < R) {z : ℂ}
    {W : P → ℂ → ℂ} (hWc : Continuous fun q : P × ℂ => W q.1 q.2)
    (hWd : ∀ p : P, ∀ ζ ∈ ball z R, DifferentiableAt ℂ (W p) ζ) :
    Continuous fun p : P => deriv (deriv (W p)) z := by
  have h := continuous_iteratedDeriv_parametric hR 2 hWc hWd
  have hrw : (fun p : P => iteratedDeriv 2 (W p) z)
      = fun p : P => deriv (deriv (W p)) z := by
    funext p
    rw [iteratedDeriv_two]
  rwa [hrw] at h

/-! ## Joint continuity in the parameters and the point

The clock iteration needs the second derivative to be continuous jointly in the null coordinates and
in the transverse point, because the next iterate integrates it in the former and is evaluated at
the latter. Moving the contour with the point costs nothing: the contour integral only ever sees
`ζ - z`, which is `circleMap 0 R θ`, independent of `z`.
-/

/-- The Cauchy representation of the second derivative, as a function of the parameters and the
point together. -/
noncomputable def cauchySecond (R : ℝ) (W : P → ℂ → ℂ) : P × ℂ → ℂ :=
  fun q => (2 * Real.pi * Complex.I / ((Nat.factorial 2 : ℕ) : ℂ))⁻¹
    • ∮ ζ in C(q.2, R), (1 / (ζ - q.2) ^ (2 + 1)) • W q.1 ζ

theorem circleMap_eq_add (c : ℂ) (R : ℝ) (θ : ℝ) :
    circleMap c R θ = c + circleMap 0 R θ := by
  have h := circleMap_sub_center c R θ
  linear_combination h

/-- **The Cauchy representation is jointly continuous.** -/
theorem continuous_cauchySecond {R : ℝ} {W : P → ℂ → ℂ}
    (hWc : Continuous fun q : P × ℂ => W q.1 q.2) (hR : R ≠ 0) :
    Continuous (cauchySecond R W) := by
  have hint : Continuous fun r : (P × ℂ) × ℝ =>
      deriv (circleMap r.1.2 R) r.2
        • ((1 / (circleMap r.1.2 R r.2 - r.1.2) ^ (2 + 1)) • W r.1.1 (circleMap r.1.2 R r.2)) := by
    have hrw : (fun r : (P × ℂ) × ℝ =>
        deriv (circleMap r.1.2 R) r.2
          • ((1 / (circleMap r.1.2 R r.2 - r.1.2) ^ (2 + 1)) • W r.1.1 (circleMap r.1.2 R r.2)))
        = fun r : (P × ℂ) × ℝ =>
          (circleMap 0 R r.2 * Complex.I)
            • ((1 / (circleMap 0 R r.2) ^ (2 + 1)) • W r.1.1 (r.1.2 + circleMap 0 R r.2)) := by
      funext r
      rw [deriv_circleMap, circleMap_sub_center, circleMap_eq_add r.1.2 R r.2]
    rw [hrw]
    have hc0 : Continuous fun r : (P × ℂ) × ℝ => circleMap 0 R r.2 :=
      (continuous_circleMap 0 R).comp continuous_snd
    have hden : Continuous fun r : (P × ℂ) × ℝ =>
        1 / (circleMap 0 R r.2) ^ (2 + 1) := by
      refine continuous_const.div (hc0.pow (2 + 1)) fun r => ?_
      have : circleMap 0 R r.2 ≠ 0 := circleMap_ne_center hR
      exact pow_ne_zero _ this
    have hval : Continuous fun r : (P × ℂ) × ℝ =>
        W r.1.1 (r.1.2 + circleMap 0 R r.2) :=
      hWc.comp ((continuous_fst.comp continuous_fst).prodMk
        ((continuous_snd.comp continuous_fst).add hc0))
    exact (hc0.mul continuous_const).smul (hden.smul hval)
  have hcirc : Continuous fun q : P × ℂ =>
      ∮ ζ in C(q.2, R), (1 / (ζ - q.2) ^ (2 + 1)) • W q.1 ζ := by
    show Continuous fun q : P × ℂ =>
      ∫ θ in (0 : ℝ)..(2 * Real.pi), deriv (circleMap q.2 R) θ
        • ((1 / (circleMap q.2 R θ - q.2) ^ (2 + 1)) • W q.1 (circleMap q.2 R θ))
    exact continuous_parametric_intervalIntegral_of_continuous' hint 0 (2 * Real.pi)
  rw [show cauchySecond R W
      = ((2 * Real.pi * Complex.I / ((Nat.factorial 2 : ℕ) : ℂ))⁻¹ •
        fun q : P × ℂ => ∮ ζ in C(q.2, R), (1 / (ζ - q.2) ^ (2 + 1)) • W q.1 ζ) from rfl]
  exact hcirc.const_smul _

/-- **The second derivative of a holomorphic family is continuous jointly in the parameters and the
point.** -/
theorem continuousAt_deriv_deriv_parametric {ρ ρ' : ℝ} (hρ : ρ < ρ')
    {W : P → ℂ → ℂ} (hWc : Continuous fun q : P × ℂ => W q.1 q.2)
    (hWd : ∀ p : P, DifferentiableOn ℂ (W p) (imStrip ρ'))
    {q : P × ℂ} (hq : q.2 ∈ imStrip ρ) :
    ContinuousAt (fun q' : P × ℂ => deriv (deriv (W q'.1)) q'.2) q := by
  have hRpos : (0 : ℝ) < (ρ' - ρ) / 2 := by
    have : ρ < ρ' := hρ
    linarith
  have hslice : ∀ p : P, Continuous (W p) := fun p =>
    hWc.comp (continuous_const.prodMk continuous_id)
  have hform : ∀ q' : P × ℂ, q'.2 ∈ imStrip ρ →
      deriv (deriv (W q'.1)) q'.2 = cauchySecond ((ρ' - ρ) / 2) W q' := by
    intro q' hq'
    have hsub := closedBall_subset_imStrip hρ (le_of_lt (mem_imStrip.mp hq'))
    have hd : ∀ ζ ∈ ball q'.2 ((ρ' - ρ) / 2), DifferentiableAt ℂ (W q'.1) ζ := by
      intro ζ hζ
      exact (hWd q'.1).differentiableAt
        ((isOpen_imStrip ρ').mem_nhds (hsub (ball_subset_closedBall hζ)))
    have h := iteratedDeriv_eq_circleIntegral hRpos 2 (hslice q'.1) hd
    rw [iteratedDeriv_two] at h
    exact h
  have hcont : ContinuousAt (cauchySecond ((ρ' - ρ) / 2) W) q :=
    (continuous_cauchySecond hWc (ne_of_gt hRpos)).continuousAt
  refine hcont.congr ?_
  refine Filter.eventuallyEq_of_mem ?_ fun q' hq' => (hform q' hq').symm
  exact (isOpen_imStrip ρ).preimage continuous_snd |>.mem_nhds hq

end GaloisForLFunctions.HTGeometry
