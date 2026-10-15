import GaloisForLFunctions.Hurwitz.JointAnchorRegularity
import Mathlib.Analysis.Calculus.ImplicitContDiff

/-!
# The actual Hurwitz level graph through the canonical anchor

The shift derivative at `a = 1` is nonzero for every exponent in `Re s > 0`.
Joint regularity therefore gives a holomorphic local level graph through
every anchor away from the zeta pole. No zero-free hypothesis is used.
-/

open Complex Filter Metric Set
open scoped Topology

namespace HurwitzZetaContinuation

/-- The right partial derivative of the actual joint source is the anchor derivative. -/
theorem fderiv_continuedHzeta_joint_comp_inr {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    (fderiv ℂ (fun p : ℂ × ℂ => continuedHzeta p.1 p.2) (s, 1)).comp
        (ContinuousLinearMap.inr ℂ ℂ ℂ) =
      ContinuousLinearMap.toSpanSingleton ℂ (-s * riemannZeta (s + 1)) := by
  have hc := contDiffAt_one_continuedHzeta_joint hs hs1 (a := 1) (by norm_num)
  have hg : HasFDerivAt (fun a : ℂ => (s, a))
      (ContinuousLinearMap.inr ℂ ℂ ℂ) 1 := by
    convert! (hasFDerivAt_const s (1 : ℂ)).prodMk (hasFDerivAt_id (1 : ℂ)) using 1
  have hd := hc.differentiableAt_one.hasFDerivAt.comp 1 hg
  have hd' : HasFDerivAt (continuedHzeta s)
      ((fderiv ℂ (fun p : ℂ × ℂ => continuedHzeta p.1 p.2) (s, 1)).comp
        (ContinuousLinearMap.inr ℂ ℂ ℂ)) 1 := by
    simpa only [Function.comp_def] using hd
  exact hd'.unique (continuedHzeta_hasDerivAt_one hs).hasFDerivAt

/-- The actual shift partial is invertible at every positive-real anchor away from the pole. -/
theorem isInvertible_fderiv_continuedHzeta_joint_comp_inr
    {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    ((fderiv ℂ (fun p : ℂ × ℂ => continuedHzeta p.1 p.2) (s, 1)).comp
      (ContinuousLinearMap.inr ℂ ℂ ℂ)).IsInvertible := by
  rw [fderiv_continuedHzeta_joint_comp_inr hs hs1]
  have hs0 : s ≠ 0 := by
    intro h
    simp [h] at hs
  have hz : riemannZeta (s + 1) ≠ 0 :=
    riemannZeta_ne_zero_of_one_lt_re (by simpa using hs)
  have hne : -s * riemannZeta (s + 1) ≠ 0 := mul_ne_zero (neg_ne_zero.mpr hs0) hz
  apply ContinuousLinearMap.IsInvertible.of_inverse
    (g := ContinuousLinearMap.toSpanSingleton ℂ (-s * riemannZeta (s + 1))⁻¹)
  · apply ContinuousLinearMap.ext
    intro z
    change z * (-s * riemannZeta (s + 1))⁻¹ * (-s * riemannZeta (s + 1)) = z
    rw [mul_assoc, inv_mul_cancel₀ hne, mul_one]
  · apply ContinuousLinearMap.ext
    intro z
    change z * (-s * riemannZeta (s + 1)) * (-s * riemannZeta (s + 1))⁻¹ = z
    rw [mul_assoc, mul_inv_cancel₀ hne, mul_one]

/-- A holomorphic local level graph of the actual continued Hurwitz function. -/
theorem exists_analytic_anchor_level_graph {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    ∃ A : ℂ → ℂ, A s = 1 ∧ AnalyticAt ℂ A s ∧
      ∀ᶠ p : ℂ × ℂ in 𝓝 (s, 1),
        continuedHzeta p.1 p.2 = riemannZeta s ↔ p.2 = A p.1 := by
  have hc := contDiffAt_one_continuedHzeta_joint hs hs1 (a := 1) (by norm_num)
  have hi := isInvertible_fderiv_continuedHzeta_joint_comp_inr hs hs1
  let A := hc.implicitFunction (by norm_num) hi
  have hA : ContDiffAt ℂ 1 A s := hc.contDiffAt_implicitFunction (by norm_num) hi
  refine ⟨A, hc.implicitFunction_apply_self (by norm_num) hi, ?_, ?_⟩
  · apply Complex.analyticAt_iff_eventually_differentiableAt.mpr
    filter_upwards [hA.eventually (by norm_num)] with z hz
    exact hz.differentiableAt_one
  · filter_upwards [hc.eventually_apply_eq_iff_implicitFunction (by norm_num) hi] with p hp
    simpa only [A, continuedHzeta_at_one, eq_comm (a := p.2)] using hp

private theorem deriv_right_eq_fderiv {F : ℂ × ℂ → ℂ} {p : ℂ × ℂ}
    (h : DifferentiableAt ℂ F p) :
    deriv (fun a : ℂ => F (p.1, a)) p.2 = fderiv ℂ F p (0, 1) := by
  have hg : HasDerivAt (fun a : ℂ => (p.1, a)) (0, 1) p.2 :=
    (hasDerivAt_const p.2 p.1).prodMk (hasDerivAt_id p.2)
  have hd := h.hasFDerivAt.comp_hasDerivAt p.2 hg
  exact hd.deriv

/-- The shift derivative is continuous jointly in exponent and shift near the anchor. -/
theorem continuousAt_deriv_continuedHzeta_shift_joint {s a : ℂ}
    (hs : 0 < s.re) (hs1 : s ≠ 1) (ha : ‖a - 1‖ < (1 / 2 : ℝ)) :
    ContinuousAt (fun p : ℂ × ℂ => deriv (continuedHzeta p.1) p.2) (s, a) := by
  have hc := contDiffAt_one_continuedHzeta_joint hs hs1 ha
  have hd := (hc.continuousAt_fderiv (by norm_num)).clm_apply
    (continuousAt_const (y := ((0 : ℂ), (1 : ℂ))))
  apply hd.congr
  filter_upwards [hc.eventually (by norm_num)] with p hp
  exact (deriv_right_eq_fderiv hp.differentiableAt_one).symm

/-- Every nearby shift slice of the actual Hurwitz source is analytic. -/
theorem continuedHzeta_analyticAt_shift {s a : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1)
    (ha : ‖a - 1‖ < (1 / 2 : ℝ)) : AnalyticAt ℂ (continuedHzeta s) a := by
  have hc : ContDiffAt ℂ 1 (continuedHzeta s) a :=
    (contDiffAt_one_continuedHzeta_joint hs hs1 ha).comp a
      (contDiffAt_const.prodMk contDiffAt_id)
  apply Complex.analyticAt_iff_eventually_differentiableAt.mpr
  filter_upwards [hc.eventually (by norm_num)] with z hz
  exact hz.differentiableAt_one

end HurwitzZetaContinuation
