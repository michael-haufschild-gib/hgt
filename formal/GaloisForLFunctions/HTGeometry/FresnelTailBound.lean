import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# The oscillatory half-power tail is uniformly small

The Fresnel integrand `u^{-1/2} e^{iu}` is not absolutely integrable at infinity, but one
integration by parts makes its tail explicitly small: with `v(u) = e^{iu}/i`,

`∫_a^b u^{-1/2} e^{iu} du = [u^{-1/2} e^{iu}/i]_a^b + (1/2) ∫_a^b u^{-3/2} e^{iu}/i du`,

and both the boundary term and the remaining absolutely convergent integral are `O(a^{-1/2})`.
The oscillatory half-power integral therefore satisfies the Cauchy criterion on the ray, with the
uniform tail bound `2 a^{-1/2}`.
-/

open Complex intervalIntegral MeasureTheory

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The oscillatory half-power integrand. -/
def fresnelKernel (u : ℝ) : ℂ := ((u ^ (-(1:ℝ)/2) : ℝ) : ℂ) * Complex.exp ((u : ℂ) * I)

/-- The primitive used in the integration by parts. -/
def fresnelPrimitive (u : ℝ) : ℂ := Complex.exp ((u : ℂ) * I) / I

theorem norm_fresnelPrimitive (u : ℝ) : ‖fresnelPrimitive u‖ = 1 := by
  rw [fresnelPrimitive, norm_div, Complex.norm_I, div_one, Complex.norm_exp]
  simp

theorem hasDerivAt_fresnelPrimitive (u : ℝ) :
    HasDerivAt fresnelPrimitive (Complex.exp ((u : ℂ) * I)) u := by
  have h1 : HasDerivAt (fun x : ℝ => (x : ℂ) * I) I u := by
    have h := (Complex.ofRealCLM.hasDerivAt (x := u)).mul_const I
    simpa using h
  have hbase : HasDerivAt (fun x : ℝ => Complex.exp ((x : ℂ) * I))
      (Complex.exp ((u : ℂ) * I) * I) u := h1.cexp
  have hdiv := hbase.div_const I
  have hval : Complex.exp ((u : ℂ) * I) * I / I = Complex.exp ((u : ℂ) * I) := by
    field_simp
  have hfun : fresnelPrimitive = fun x : ℝ => Complex.exp ((x : ℂ) * I) / I := rfl
  rw [hfun, ← hval]
  exact hdiv

theorem hasDerivAt_ofReal_rpow {u p : ℝ} (hu : 0 < u) :
    HasDerivAt (fun x : ℝ => ((x ^ p : ℝ) : ℂ)) (((p * u ^ (p - 1) : ℝ) : ℂ)) u := by
  have hreal : HasDerivAt (fun x : ℝ => x ^ p) (p * u ^ (p - 1)) u :=
    Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt hu))
  exact hreal.ofReal_comp

/-- **Integration by parts for the oscillatory half-power integral.** -/
theorem integral_fresnelKernel_eq {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∫ u in a..b, fresnelKernel u)
      = ((b ^ (-(1:ℝ)/2) : ℝ) : ℂ) * fresnelPrimitive b
        - ((a ^ (-(1:ℝ)/2) : ℝ) : ℂ) * fresnelPrimitive a
        - ∫ u in a..b, ((-(1:ℝ)/2 * u ^ (-(1:ℝ)/2 - 1) : ℝ) : ℂ) * fresnelPrimitive u := by
  have huIcc : Set.uIcc a b = Set.Icc a b := Set.uIcc_of_le hab
  have hsub : Set.uIcc a b ⊆ Set.Ioi 0 := by
    rw [huIcc]
    intro x hx
    exact lt_of_lt_of_le ha hx.1
  have hderiv_u : ∀ x ∈ Set.uIcc a b,
      HasDerivAt (fun y : ℝ => ((y ^ (-(1:ℝ)/2) : ℝ) : ℂ))
        (((-(1:ℝ)/2 * x ^ (-(1:ℝ)/2 - 1) : ℝ) : ℂ)) x :=
    fun x hx => hasDerivAt_ofReal_rpow (hsub hx)
  have hderiv_v : ∀ x ∈ Set.uIcc a b,
      HasDerivAt fresnelPrimitive (Complex.exp ((x : ℂ) * I)) x :=
    fun x _ => hasDerivAt_fresnelPrimitive x
  have hcont_u' : ContinuousOn
      (fun x : ℝ => ((-(1:ℝ)/2 * x ^ (-(1:ℝ)/2 - 1) : ℝ) : ℂ)) (Set.uIcc a b) := by
    intro x hx
    have hx0 : 0 < x := hsub hx
    have h1 : ContinuousAt (fun y : ℝ => y ^ (-(1:ℝ)/2 - 1)) x :=
      Real.continuousAt_rpow_const x _ (Or.inl (ne_of_gt hx0))
    exact ((Complex.continuous_ofReal.continuousAt).comp
      (continuousAt_const.mul h1)).continuousWithinAt
  have hint_u : IntervalIntegrable
      (fun x : ℝ => ((-(1:ℝ)/2 * x ^ (-(1:ℝ)/2 - 1) : ℝ) : ℂ)) volume a b :=
    hcont_u'.intervalIntegrable
  have hint_v : IntervalIntegrable (fun x : ℝ => Complex.exp ((x : ℂ) * I)) volume a b := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hparts := integral_mul_deriv_eq_deriv_mul hderiv_u hderiv_v hint_u hint_v
  have hfun : (fun u : ℝ => fresnelKernel u)
      = fun u : ℝ => ((u ^ (-(1:ℝ)/2) : ℝ) : ℂ) * Complex.exp ((u : ℂ) * I) := rfl
  rw [hfun]
  exact hparts

/-- **The uniform tail bound.** -/
theorem norm_integral_fresnelKernel_le {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ‖∫ u in a..b, fresnelKernel u‖ ≤ 2 * a ^ (-(1:ℝ)/2) := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have hzero : (0:ℝ) ∉ Set.uIcc a b := by
    rw [Set.uIcc_of_le hab]
    intro hcon
    exact absurd hcon.1 (not_le.mpr ha)
  have hnormEq : ∀ u ∈ Set.uIcc a b,
      ‖((-(1:ℝ)/2 * u ^ (-(1:ℝ)/2 - 1) : ℝ) : ℂ) * fresnelPrimitive u‖
        = (1:ℝ)/2 * u ^ (-(3:ℝ)/2) := by
    intro u hu
    have hu0 : 0 < u := by
      rw [Set.uIcc_of_le hab] at hu
      exact lt_of_lt_of_le ha hu.1
    rw [norm_mul, norm_fresnelPrimitive, mul_one, Complex.norm_real, Real.norm_eq_abs]
    have hexp : -(1:ℝ)/2 - 1 = -(3:ℝ)/2 := by ring
    rw [hexp, abs_of_nonpos (by
      have : (0:ℝ) < u ^ (-(3:ℝ)/2) := Real.rpow_pos_of_pos hu0 _
      nlinarith)]
    ring
  have hintNorm : IntervalIntegrable (fun u : ℝ => (1:ℝ)/2 * u ^ (-(3:ℝ)/2)) volume a b := by
    apply ContinuousOn.intervalIntegrable
    intro x hx
    have hx0 : 0 < x := by
      rw [Set.uIcc_of_le hab] at hx
      exact lt_of_lt_of_le ha hx.1
    exact (continuousAt_const.mul
      (Real.continuousAt_rpow_const x _ (Or.inl (ne_of_gt hx0)))).continuousWithinAt
  have hvalue : (∫ u in a..b, (1:ℝ)/2 * u ^ (-(3:ℝ)/2))
      = a ^ (-(1:ℝ)/2) - b ^ (-(1:ℝ)/2) := by
    rw [intervalIntegral.integral_const_mul,
      integral_rpow (Or.inr ⟨by norm_num, hzero⟩)]
    have hexp : -(3:ℝ)/2 + 1 = -(1:ℝ)/2 := by ring
    rw [hexp]
    field_simp
    ring
  have hrem : ‖∫ u in a..b, ((-(1:ℝ)/2 * u ^ (-(1:ℝ)/2 - 1) : ℝ) : ℂ) * fresnelPrimitive u‖
      ≤ a ^ (-(1:ℝ)/2) - b ^ (-(1:ℝ)/2) := by
    have hstep : ‖∫ u in a..b, ((-(1:ℝ)/2 * u ^ (-(1:ℝ)/2 - 1) : ℝ) : ℂ) * fresnelPrimitive u‖
        ≤ ∫ u in a..b, (1:ℝ)/2 * u ^ (-(3:ℝ)/2) := by
      refine intervalIntegral.norm_integral_le_of_norm_le hab ?_ hintNorm
      filter_upwards with u hu
      have humem : u ∈ Set.uIcc a b := by
        rw [Set.uIcc_of_le hab]
        exact ⟨le_of_lt hu.1, hu.2⟩
      exact le_of_eq (hnormEq u humem)
    rw [hvalue] at hstep
    exact hstep
  rw [integral_fresnelKernel_eq ha hab]
  have hbb : ‖((b ^ (-(1:ℝ)/2) : ℝ) : ℂ) * fresnelPrimitive b‖ = b ^ (-(1:ℝ)/2) := by
    rw [norm_mul, norm_fresnelPrimitive, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.rpow_pos_of_pos hb _)]
  have haa : ‖((a ^ (-(1:ℝ)/2) : ℝ) : ℂ) * fresnelPrimitive a‖ = a ^ (-(1:ℝ)/2) := by
    rw [norm_mul, norm_fresnelPrimitive, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.rpow_pos_of_pos ha _)]
  calc ‖((b ^ (-(1:ℝ)/2) : ℝ) : ℂ) * fresnelPrimitive b
        - ((a ^ (-(1:ℝ)/2) : ℝ) : ℂ) * fresnelPrimitive a
        - ∫ u in a..b, ((-(1:ℝ)/2 * u ^ (-(1:ℝ)/2 - 1) : ℝ) : ℂ) * fresnelPrimitive u‖
      ≤ ‖((b ^ (-(1:ℝ)/2) : ℝ) : ℂ) * fresnelPrimitive b
          - ((a ^ (-(1:ℝ)/2) : ℝ) : ℂ) * fresnelPrimitive a‖
        + ‖∫ u in a..b, ((-(1:ℝ)/2 * u ^ (-(1:ℝ)/2 - 1) : ℝ) : ℂ) * fresnelPrimitive u‖ :=
        norm_sub_le _ _
    _ ≤ (‖((b ^ (-(1:ℝ)/2) : ℝ) : ℂ) * fresnelPrimitive b‖
          + ‖((a ^ (-(1:ℝ)/2) : ℝ) : ℂ) * fresnelPrimitive a‖)
        + (a ^ (-(1:ℝ)/2) - b ^ (-(1:ℝ)/2)) := by
        have := norm_sub_le (((b ^ (-(1:ℝ)/2) : ℝ) : ℂ) * fresnelPrimitive b)
          (((a ^ (-(1:ℝ)/2) : ℝ) : ℂ) * fresnelPrimitive a)
        linarith [hrem, this]
    _ = 2 * a ^ (-(1:ℝ)/2) := by
        rw [hbb, haa]
        ring

end

end GaloisForLFunctions.HTGeometry
