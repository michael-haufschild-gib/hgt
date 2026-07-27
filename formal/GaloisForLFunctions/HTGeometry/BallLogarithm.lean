import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Complex.BorelCaratheodory
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Tactic

/-!
# The logarithm of a nonvanishing function on a disc

On a disc a nonvanishing holomorphic function is its value at the centre times the exponential of a
holomorphic function vanishing at the centre.  The logarithmic derivative `f'/f` is holomorphic on
the disc, hence has a primitive there by Morera's theorem for a disc; then `f · exp(-g)` has
vanishing derivative on a convex set and is therefore constant.

This is the disc analogue of `exists_entire_log_of_ne_zero`, and it is what turns an upper bound on
`|f|` into a bound on `Re log f`, the input of Borel–Carathéodory.
-/

open Complex Metric

namespace GaloisForLFunctions.HTGeometry

/-- **Logarithm on a disc.**  A nonvanishing holomorphic function on a disc is `f c` times the
exponential of a holomorphic function vanishing at the centre. -/
theorem exists_log_on_ball {f : ℂ → ℂ} {c : ℂ} {r : ℝ} (hr : 0 < r)
    (hf : DifferentiableOn ℂ f (ball c r)) (hne : ∀ z ∈ ball c r, f z ≠ 0) :
    ∃ g : ℂ → ℂ, DifferentiableOn ℂ g (ball c r) ∧ g c = 0 ∧
      ∀ z ∈ ball c r, f z = f c * Complex.exp (g z) := by
  have hcmem : c ∈ ball c r := mem_ball_self hr
  have hnhds : ∀ z ∈ ball c r, ball c r ∈ nhds z := fun z hz => isOpen_ball.mem_nhds hz
  have hfat : ∀ z ∈ ball c r, DifferentiableAt ℂ f z := fun z hz =>
    hf.differentiableAt (hnhds z hz)
  have hderivat : ∀ z ∈ ball c r, DifferentiableAt ℂ (deriv f) z := fun z hz =>
    ((hf.analyticAt (hnhds z hz)).deriv).differentiableAt
  have hquot : DifferentiableOn ℂ (fun z => deriv f z / f z) (ball c r) := fun z hz =>
    (((hderivat z hz).div (hfat z hz) (hne z hz))).differentiableWithinAt
  obtain ⟨g, hg0, hg⟩ := (hquot.isExactOn_ball).with_val_at c 0
  have hgat : ∀ z ∈ ball c r, DifferentiableAt ℂ g z := fun z hz => (hg z hz).differentiableAt
  have hgon : DifferentiableOn ℂ g (ball c r) := fun z hz => (hgat z hz).differentiableWithinAt
  refine ⟨g, hgon, hg0, ?_⟩
  -- `F = f · exp (-g)` has vanishing derivative on the disc
  set F : ℂ → ℂ := fun z => f z * Complex.exp (-g z) with hF
  have hFat : ∀ z ∈ ball c r, HasDerivAt F 0 z := by
    intro z hz
    have hgz : HasDerivAt g (deriv f z / f z) z := hg z hz
    have hexp : HasDerivAt (fun w => Complex.exp (-g w))
        (-(Complex.exp (-g z) * (deriv f z / f z))) z := by
      simpa using (hgz.neg).cexp
    have hprod : HasDerivAt F
        (deriv f z * Complex.exp (-g z) +
          f z * (-(Complex.exp (-g z) * (deriv f z / f z)))) z :=
      (hfat z hz).hasDerivAt.mul hexp
    have hzero : deriv f z * Complex.exp (-g z) +
        f z * (-(Complex.exp (-g z) * (deriv f z / f z))) = 0 := by
      field_simp
      rw [div_self (hne z hz)]
      ring
    rwa [hzero] at hprod
  have hFon : DifferentiableOn ℂ F (ball c r) := fun z hz =>
    (hFat z hz).differentiableAt.differentiableWithinAt
  have hfd : ∀ z ∈ ball c r, fderivWithin ℂ F (ball c r) z = 0 := by
    intro z hz
    rw [fderivWithin_of_isOpen isOpen_ball hz]
    have hfz : HasFDerivAt F (0 : ℂ →L[ℂ] ℂ) z := by
      simpa using (hFat z hz).hasFDerivAt
    exact hfz.fderiv
  have hconst : ∀ z ∈ ball c r, F z = F c := fun z hz =>
    (convex_ball c r).is_const_of_fderivWithin_eq_zero hFon hfd hz hcmem
  intro z hz
  have hFc : F c = f c := by
    rw [hF]
    simp [hg0]
  have hz' := hconst z hz
  rw [hFc, hF] at hz'
  have hexpne : Complex.exp (-g z) ≠ 0 := Complex.exp_ne_zero _
  field_simp at hz'
  rw [← hz', mul_assoc, ← Complex.exp_add]
  simp

/-- **Lower bound from an upper bound.**  A nonvanishing holomorphic function on a disc, bounded
above by `M` there and below by `m` at the centre, is bounded below on the concentric disc of
radius `r` by `m exp (-2 (log (M/m) + 1) r / (R - r))`.

Mechanism: the holomorphic logarithm `g` has `Re g = log (‖f‖/‖f c‖) ≤ log (M/m)` and `g c = 0`, so
Borel–Carathéodory bounds `‖g‖`, and `‖f‖ = ‖f c‖ exp (Re g) ≥ m exp (-‖g‖)`. -/
theorem norm_lower_bound_of_ball {f : ℂ → ℂ} {c : ℂ} {R r M m : ℝ}
    (hr0 : 0 ≤ r) (hrR : r < R)
    (hf : DifferentiableOn ℂ f (ball c R)) (hne : ∀ z ∈ ball c R, f z ≠ 0)
    (hM : ∀ z ∈ ball c R, ‖f z‖ ≤ M) (hm0 : 0 < m) (hm : m ≤ ‖f c‖)
    {z : ℂ} (hz : ‖z - c‖ ≤ r) :
    m * Real.exp (-(2 * (Real.log (M / m) + 1) * r / (R - r))) ≤ ‖f z‖ := by
  have hR : 0 < R := lt_of_le_of_lt hr0 hrR
  have hcmem : c ∈ ball c R := mem_ball_self hR
  have hMm : m ≤ M := le_trans hm (hM c hcmem)
  have hlogA : 0 ≤ Real.log (M / m) := Real.log_nonneg (by rw [le_div_iff₀ hm0]; linarith)
  set A : ℝ := Real.log (M / m) + 1 with hA
  have hApos : 0 < A := by rw [hA]; linarith
  obtain ⟨g, hgon, hg0, hgeq⟩ := exists_log_on_ball hR hf hne
  have hgat : ∀ w ∈ ball c R, DifferentiableAt ℂ g w := fun w hw =>
    hgon.differentiableAt (isOpen_ball.mem_nhds hw)
  -- the modulus identity
  have hmod : ∀ w ∈ ball c R, ‖f w‖ = ‖f c‖ * Real.exp ((g w).re) := by
    intro w hw
    rw [hgeq w hw, norm_mul, Complex.norm_exp]
  have hfc0 : (0 : ℝ) < ‖f c‖ := lt_of_lt_of_le hm0 hm
  -- the real part of the logarithm is bounded above
  have hre : ∀ w ∈ ball c R, (g w).re ≤ Real.log (M / m) := by
    intro w hw
    have h1 : ‖f c‖ * Real.exp ((g w).re) ≤ M := by rw [← hmod w hw]; exact hM w hw
    have h2 : Real.exp ((g w).re) ≤ M / m := by
      rw [le_div_iff₀ hm0]
      nlinarith [Real.exp_pos ((g w).re), hm, h1]
    have h3 : (0 : ℝ) < M / m := lt_of_lt_of_le (Real.exp_pos _) h2
    rw [← Real.log_exp ((g w).re)]
    exact Real.log_le_log (Real.exp_pos _) h2
  -- translate to the origin and apply Borel–Carathéodory
  have hzmem : z - c ∈ ball (0 : ℂ) R := by
    rw [mem_ball_zero_iff]
    linarith
  have hGdiff : DifferentiableOn ℂ (fun w => g (c + w)) (ball (0 : ℂ) R) := by
    intro w hw
    have hcw : c + w ∈ ball c R := by
      rw [mem_ball_iff_norm]
      simpa using mem_ball_zero_iff.mp hw
    exact ((hgat (c + w) hcw).comp w (by fun_prop)).differentiableWithinAt
  have hGmaps : Set.MapsTo (fun w => g (c + w)) (ball (0 : ℂ) R) {u : ℂ | u.re ≤ A} := by
    intro w hw
    have hcw : c + w ∈ ball c R := by
      rw [mem_ball_iff_norm]
      simpa using mem_ball_zero_iff.mp hw
    have := hre (c + w) hcw
    simp only [Set.mem_setOf_eq]
    rw [hA]
    linarith
  have hG0 : (fun w => g (c + w)) 0 = 0 := by simpa using hg0
  have hBC := Complex.borelCaratheodory_zero hApos hGdiff hGmaps hR hzmem hG0
  rw [show c + (z - c) = z by ring] at hBC
  -- the Borel–Carathéodory bound is monotone in the radius
  have hmono : 2 * A * ‖z - c‖ / (R - ‖z - c‖) ≤ 2 * A * r / (R - r) := by
    have hden1 : (0 : ℝ) < R - ‖z - c‖ := by
      have := mem_ball_zero_iff.mp hzmem
      linarith
    have hden2 : (0 : ℝ) < R - r := by linarith
    rw [div_le_div_iff₀ hden1 hden2]
    nlinarith [mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ 2 * A) hR.le)
      (sub_nonneg.mpr hz)]
  have hgbound : ‖g z‖ ≤ 2 * A * r / (R - r) := le_trans hBC hmono
  -- assemble
  have hzball : z ∈ ball c R := by
    rw [mem_ball_iff_norm]
    linarith
  have hrege : -(2 * A * r / (R - r)) ≤ (g z).re := by
    have h1 : |(g z).re| ≤ ‖g z‖ := Complex.abs_re_le_norm _
    have h2 : -(g z).re ≤ |(g z).re| := neg_le_abs _
    linarith
  calc m * Real.exp (-(2 * A * r / (R - r)))
      ≤ ‖f c‖ * Real.exp ((g z).re) :=
        mul_le_mul hm (Real.exp_le_exp.mpr hrege) (Real.exp_pos _).le (le_of_lt hfc0)
    _ = ‖f z‖ := (hmod z hzball).symm

end GaloisForLFunctions.HTGeometry
