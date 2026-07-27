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

/-- **Borel–Carathéodory for a given branch of the logarithm.**  If `f = f c · exp g` on a disc
where `‖f‖ ≤ M` and `m ≤ ‖f c‖`, then `‖g‖ ≤ 2 (log (M/m) + 1) r / (R - r)` on the smaller disc.

The real part of the branch is `log (|f| / |f c|) ≤ log (M/m)`; Borel–Carathéodory converts that
one-sided bound on the real part into a two-sided bound on the modulus.

Taking the branch as an argument rather than producing it lets the same `g` be bounded on several
radii, with a different `M/m` on each — which is what makes the three-circles argument possible. -/
theorem norm_log_le_of_ball {f g : ℂ → ℂ} {c : ℂ} {R r M m : ℝ} (hr0 : 0 ≤ r) (hrR : r < R)
    (hg : DifferentiableOn ℂ g (ball c R)) (hg0 : g c = 0)
    (hfg : ∀ z ∈ ball c R, f z = f c * Complex.exp (g z))
    (hM : ∀ z ∈ ball c R, ‖f z‖ ≤ M) (hm0 : 0 < m) (hm : m ≤ ‖f c‖)
    {z : ℂ} (hz : ‖z - c‖ ≤ r) :
    ‖g z‖ ≤ 2 * (Real.log (M / m) + 1) * r / (R - r) := by
  have hR : 0 < R := lt_of_le_of_lt hr0 hrR
  have hcmem : c ∈ ball c R := mem_ball_self hR
  have hMm : m ≤ M := le_trans hm (hM c hcmem)
  have hlogA : 0 ≤ Real.log (M / m) := Real.log_nonneg (by rw [le_div_iff₀ hm0]; linarith)
  set A : ℝ := Real.log (M / m) + 1 with hA
  have hApos : 0 < A := by rw [hA]; linarith
  have hgat : ∀ w ∈ ball c R, DifferentiableAt ℂ g w := fun w hw =>
    hg.differentiableAt (isOpen_ball.mem_nhds hw)
  have hmod : ∀ w ∈ ball c R, ‖f w‖ = ‖f c‖ * Real.exp ((g w).re) := by
    intro w hw
    rw [hfg w hw, norm_mul, Complex.norm_exp]
  have hfc0 : (0 : ℝ) < ‖f c‖ := lt_of_lt_of_le hm0 hm
  have hre : ∀ w ∈ ball c R, (g w).re ≤ Real.log (M / m) := by
    intro w hw
    have h1 : ‖f c‖ * Real.exp ((g w).re) ≤ M := by rw [← hmod w hw]; exact hM w hw
    have h2 : Real.exp ((g w).re) ≤ M / m := by
      rw [le_div_iff₀ hm0]
      nlinarith [Real.exp_pos ((g w).re), hm, h1]
    rw [← Real.log_exp ((g w).re)]
    exact Real.log_le_log (Real.exp_pos _) h2
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
  have hmono : 2 * A * ‖z - c‖ / (R - ‖z - c‖) ≤ 2 * A * r / (R - r) := by
    have hden1 : (0 : ℝ) < R - ‖z - c‖ := by
      have := mem_ball_zero_iff.mp hzmem
      linarith
    have hden2 : (0 : ℝ) < R - r := by linarith
    rw [div_le_div_iff₀ hden1 hden2]
    nlinarith [mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ 2 * A) hR.le)
      (sub_nonneg.mpr hz)]
  exact le_trans hBC hmono

/-- **Borel–Carathéodory for the logarithm.**  On a disc where a nonvanishing holomorphic function
has modulus at most `M`, and modulus at least `m` at the centre, the branch of `log (f / f c)`
vanishing at the centre is bounded by `2 (log (M/m) + 1) r / (R - r)` on the smaller disc. -/
theorem exists_bound_log_on_ball {f : ℂ → ℂ} {c : ℂ} {R r M m : ℝ}
    (hr0 : 0 ≤ r) (hrR : r < R)
    (hf : DifferentiableOn ℂ f (ball c R)) (hne : ∀ z ∈ ball c R, f z ≠ 0)
    (hM : ∀ z ∈ ball c R, ‖f z‖ ≤ M) (hm0 : 0 < m) (hm : m ≤ ‖f c‖) :
    ∃ g : ℂ → ℂ, DifferentiableOn ℂ g (ball c R) ∧ g c = 0 ∧
      (∀ z ∈ ball c R, f z = f c * Complex.exp (g z)) ∧
      ∀ z : ℂ, ‖z - c‖ ≤ r → ‖g z‖ ≤ 2 * (Real.log (M / m) + 1) * r / (R - r) := by
  have hR : 0 < R := lt_of_le_of_lt hr0 hrR
  obtain ⟨g, hgon, hg0, hgeq⟩ := exists_log_on_ball hR hf hne
  exact ⟨g, hgon, hg0, hgeq, fun z hz =>
    norm_log_le_of_ball hr0 hrR hgon hg0 hgeq hM hm0 hm hz⟩

/-- **Lower bound from an upper bound.**  Borel–Carathéodory turns a bound on the modulus of a
nonvanishing holomorphic function into a lower bound on the smaller disc. -/
theorem norm_lower_bound_of_ball {f : ℂ → ℂ} {c : ℂ} {R r M m : ℝ}
    (hr0 : 0 ≤ r) (hrR : r < R)
    (hf : DifferentiableOn ℂ f (ball c R)) (hne : ∀ z ∈ ball c R, f z ≠ 0)
    (hM : ∀ z ∈ ball c R, ‖f z‖ ≤ M) (hm0 : 0 < m) (hm : m ≤ ‖f c‖)
    {z : ℂ} (hz : ‖z - c‖ ≤ r) :
    m * Real.exp (-(2 * (Real.log (M / m) + 1) * r / (R - r))) ≤ ‖f z‖ := by
  obtain ⟨g, _, _, hgeq, hgbd⟩ := exists_bound_log_on_ball hr0 hrR hf hne hM hm0 hm
  have hR : 0 < R := lt_of_le_of_lt hr0 hrR
  have hfc0 : (0 : ℝ) < ‖f c‖ := lt_of_lt_of_le hm0 hm
  have hzball : z ∈ ball c R := by
    rw [mem_ball_iff_norm]
    linarith
  have hmod : ‖f z‖ = ‖f c‖ * Real.exp ((g z).re) := by
    rw [hgeq z hzball, norm_mul, Complex.norm_exp]
  have hgz := hgbd z hz
  have hrege : -(2 * (Real.log (M / m) + 1) * r / (R - r)) ≤ (g z).re := by
    have h1 : |(g z).re| ≤ ‖g z‖ := Complex.abs_re_le_norm _
    have h2 : -(g z).re ≤ |(g z).re| := neg_le_abs _
    linarith
  calc m * Real.exp (-(2 * (Real.log (M / m) + 1) * r / (R - r)))
      ≤ ‖f c‖ * Real.exp ((g z).re) :=
        mul_le_mul hm (Real.exp_le_exp.mpr hrege) (Real.exp_pos _).le hfc0.le
    _ = ‖f z‖ := hmod.symm

end GaloisForLFunctions.HTGeometry
