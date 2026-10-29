import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic

/-!
# Horizontal cutoffs in the vertical energy of heat zeros

Pairwise symmetrization cancels the singular force when two zeros approach.
A Lipschitz bound on the cutoff derivative pays the remaining horizontal
flux by squared heights. The negative vertical interaction is retained;
for a conjugate pair it is independent of the nonzero height.
-/

open Set

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The trapezoid error for a function with Lipschitz derivative is
quadratic in the interval length. -/
theorem abs_trapezoid_remainder_le_of_lipschitz_deriv
    {w v : ℝ → ℝ} {M : ℝ} (hw : ∀ x, HasDerivAt w (v x) x)
    (hv : ∀ x y, |v x - v y| ≤ M * |x - y|) (x y : ℝ) :
    |(v x + v y) * (x - y) / 2 - (w x - w y)| ≤ M * (x - y) ^ 2 / 2 := by
  have hordered (a b : ℝ) (hab : a ≤ b) :
      |(v a + v b) * (a - b) / 2 - (w a - w b)| ≤ M * (a - b) ^ 2 / 2 := by
    let c := (v a + v b) / 2
    let f : ℝ → ℝ := fun r => w r - c * r
    have hfd (r : ℝ) : HasDerivAt f (v r - c) r := by
      simpa only [f, Pi.sub_def, id_eq, mul_one] using
        (hw r).sub ((hasDerivAt_id r).const_mul c)
    have hbound (r : ℝ) (hr : r ∈ Icc a b) : ‖deriv f r‖ ≤ M * (b - a) / 2 := by
      rw [(hfd r).deriv, Real.norm_eq_abs]
      have htri := abs_add_le (v r - v a) (v r - v b)
      have heq : v r - c = ((v r - v a) + (v r - v b)) / 2 := by dsimp only [c]; ring
      rw [heq, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      have h1 := hv r a
      have h2 := hv r b
      rw [abs_of_nonneg (sub_nonneg.mpr hr.1)] at h1
      rw [abs_of_nonpos (sub_nonpos.mpr hr.2)] at h2
      linarith only [htri, h1, h2]
    have h := Convex.norm_image_sub_le_of_norm_deriv_le
      (fun r _ => (hfd r).differentiableAt) hbound (convex_Icc a b)
      (left_mem_Icc.mpr hab) (right_mem_Icc.mpr hab)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hab)] at h
    convert h using 1
    · congr 1
      dsimp only [f, c]
      ring
    · ring
  rcases le_total x y with hxy | hyx
  · exact hordered x y hxy
  · have h := hordered y x hyx
    have heq : (v x + v y) * (x - y) / 2 - (w x - w y) =
        -((v y + v x) * (y - x) / 2 - (w y - w x)) := by ring
    rw [heq, abs_neg]
    convert h using 1; ring

/-- The combined contribution of two distinct zeros to localized
squared-height energy. -/
def localizedHeatPairForce (w v : ℝ → ℝ) (x x' y y' : ℝ) : ℝ :=
  2 * ((v x * y ^ 2 - v x' * y' ^ 2) * (x - x') -
    2 * (w x * y - w x' * y') * (y - y')) / ((x - x') ^ 2 + (y - y') ^ 2)

/-- The cutoff error is paid by squared heights, uniformly as the zero
gap shrinks, while the dissipative interaction keeps its full sign. -/
theorem localizedHeatPairForce_le
    {w v : ℝ → ℝ} {M : ℝ} (hM : 0 ≤ M)
    (hw : ∀ x, HasDerivAt w (v x) x)
    (hv : ∀ x x', |v x - v x'| ≤ M * |x - x'|)
    (x x' y y' : ℝ) (hsep : 0 < (x - x') ^ 2 + (y - y') ^ 2) :
    localizedHeatPairForce w v x x' y y' ≤
      -2 * (w x + w x') * (y - y') ^ 2 / ((x - x') ^ 2 + (y - y') ^ 2) +
        2 * M * (y ^ 2 + y' ^ 2) := by
  let d := x - x'
  let e := y - y'
  let E := y ^ 2 + y' ^ 2
  let r := (v x + v x') * d / 2 - (w x - w x')
  have hE : 0 ≤ E := add_nonneg (sq_nonneg y) (sq_nonneg y')
  have hvariation : |(v x - v x') * d| ≤ M * d ^ 2 := by
    rw [abs_mul]
    calc
      |v x - v x'| * |d| ≤ (M * |d|) * |d| :=
        mul_le_mul_of_nonneg_right (hv x x') (abs_nonneg d)
      _ = M * d ^ 2 := by rw [mul_assoc, ← sq, sq_abs]
  have hfirst : (v x - v x') * d * E / 2 ≤ M * d ^ 2 * E / 2 :=
    div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right ((le_abs_self _).trans hvariation) hE) (by norm_num)
  have htrap : |r| ≤ M * d ^ 2 / 2 :=
    abs_trapezoid_remainder_le_of_lipschitz_deriv hw hv x x'
  have hheights : |(y + y') * e| ≤ E := by
    rw [show (y + y') * e = y ^ 2 - y' ^ 2 by dsimp only [e]; ring]
    have h := abs_sub (y ^ 2) (y' ^ 2)
    simpa only [abs_of_nonneg (sq_nonneg y), abs_of_nonneg (sq_nonneg y')] using h
  have hsecond : r * (y + y') * e ≤ M * d ^ 2 / 2 * E := by
    calc
      r * (y + y') * e = r * ((y + y') * e) := by ring
      _ ≤ |r * ((y + y') * e)| := le_abs_self _
      _ = |r| * |(y + y') * e| := abs_mul _ _
      _ ≤ (M * d ^ 2 / 2) * E :=
        mul_le_mul htrap hheights (abs_nonneg _) (by positivity)
  have hpaid : M * d ^ 2 * E ≤ M * E * (d ^ 2 + e ^ 2) := by
    have h := mul_nonneg (mul_nonneg hM hE) (sq_nonneg e)
    nlinarith only [h]
  have hid : (v x * y ^ 2 - v x' * y' ^ 2) * d - 2 * (w x * y - w x' * y') * e =
      -(w x + w x') * e ^ 2 + (v x - v x') * d * E / 2 + r * (y + y') * e := by
    dsimp only [d, e, E, r]
    ring
  have hnum : (v x * y ^ 2 - v x' * y' ^ 2) * d - 2 * (w x * y - w x' * y') * e ≤
      -(w x + w x') * e ^ 2 + M * E * (d ^ 2 + e ^ 2) := by
    rw [hid]
    nlinarith only [hfirst, hsecond, hpaid]
  unfold localizedHeatPairForce
  apply (div_le_iff₀ hsep).mpr
  rw [add_mul, div_mul_cancel₀ _ hsep.ne']
  dsimp only [d, e, E] at hnum
  nlinarith only [hnum]

/-- A conjugate pair dissipates a fixed amount of localized energy,
independent of how close its nonzero height is to the real axis. -/
theorem localizedHeatPairForce_conjugate (w v : ℝ → ℝ) (x : ℝ) {y : ℝ} (hy : y ≠ 0) :
    localizedHeatPairForce w v x x y (-y) = -4 * w x := by
  have hden : (x - x) ^ 2 + (y - -y) ^ 2 ≠ 0 := by
    have h := sq_pos_of_ne_zero hy
    nlinarith only [h]
  unfold localizedHeatPairForce
  field_simp [hden]
  ring

end

end GaloisForLFunctions.HTGeometry
