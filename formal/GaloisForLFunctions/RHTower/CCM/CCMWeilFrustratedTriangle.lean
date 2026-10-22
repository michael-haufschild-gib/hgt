import GaloisForLFunctions.RHTower.CCM.CCMRestrictedWeilGroundParity

/-!
# A collective lower bound from three incompatible Weil couplings

Two negative couplings and one positive coupling form a frustrated triangle:
the three pairwise minimizing signs cannot occur together. An exact square
identity improves the separate-edge lower bound by the minimum edge weight,
times the squared coefficient norm. The statement applies to the actual full
restricted Weil form, without assuming positivity of that form.
-/

noncomputable section

namespace RHTower

def ccmWeilRealPolar (a : SuzukiPositiveAperture) (u v : CCMArchimedeanFormDomain a) : ℝ :=
  (ccmRestrictedWeilSourceQuadratic a (u + v) -
    ccmRestrictedWeilSourceQuadratic a (u - v)) / 4

theorem ccmWeilRealPolar_eq_form (a : SuzukiPositiveAperture)
    (u v : CCMArchimedeanFormDomain a) :
    ccmWeilRealPolar a u v =
      ((ccmRestrictedWeilForm a u v).re + (ccmRestrictedWeilForm a v u).re) / 2 := by
  unfold ccmWeilRealPolar
  simp_rw [← ccmRestrictedWeilForm_self_re_eq_source]
  unfold ccmRestrictedWeilForm
  simp only [map_add, map_sub, inner_add_left, inner_add_right, inner_sub_left, inner_sub_right,
    Complex.add_re, Complex.sub_re]
  ring

theorem ccmRestrictedWeilSourceQuadratic_real_three (a : SuzukiPositiveAperture)
    (u v w : CCMArchimedeanFormDomain a) (x y z : ℝ) :
    ccmRestrictedWeilSourceQuadratic a ((x : ℂ) • u + (y : ℂ) • v + (z : ℂ) • w) =
      x ^ 2 * ccmRestrictedWeilSourceQuadratic a u +
      y ^ 2 * ccmRestrictedWeilSourceQuadratic a v +
      z ^ 2 * ccmRestrictedWeilSourceQuadratic a w +
      2 * x * y * ccmWeilRealPolar a u v +
      2 * x * z * ccmWeilRealPolar a u w +
      2 * y * z * ccmWeilRealPolar a v w := by
  simp_rw [ccmWeilRealPolar_eq_form, ← ccmRestrictedWeilForm_self_re_eq_source]
  unfold ccmRestrictedWeilForm
  simp only [map_add, map_smul, inner_add_left, inner_add_right,
    inner_smul_left (E := CCMArchimedeanFormDomain a),
    inner_smul_right (E := CCMArchimedeanFormDomain a),
    inner_smul_left (E := suzukiApertureHilbert a),
    inner_smul_right (E := suzukiApertureHilbert a),
    Complex.conj_ofReal, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero]
  ring

theorem frustratedTriangle_square_identity (x y z : ℝ) :
    (x - y) ^ 2 + (x - z) ^ 2 + (y + z) ^ 2 =
      x ^ 2 + y ^ 2 + z ^ 2 + (x - y - z) ^ 2 := by ring

theorem frustratedTriangle_weighted_gap (a b c x y z : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    min a (min b c) * (x ^ 2 + y ^ 2 + z ^ 2) ≤
      a * (x - y) ^ 2 + b * (x - z) ^ 2 + c * (y + z) ^ 2 := by
  let m := min a (min b c)
  have hm : 0 ≤ m := le_min ha (le_min hb hc)
  have hma : m ≤ a := min_le_left _ _
  have hmb : m ≤ b := (min_le_right _ _).trans (min_le_left _ _)
  have hmc : m ≤ c := (min_le_right _ _).trans (min_le_right _ _)
  have h₁ := mul_le_mul_of_nonneg_right hma (sq_nonneg (x - y))
  have h₂ := mul_le_mul_of_nonneg_right hmb (sq_nonneg (x - z))
  have h₃ := mul_le_mul_of_nonneg_right hmc (sq_nonneg (y + z))
  have h₄ := mul_nonneg hm (sq_nonneg (x - y - z))
  change m * _ ≤ _
  nlinarith only [h₁, h₂, h₃, h₄]

/-- Diagonal estimate obtained by bounding each off-diagonal entry separately. -/
def ccmWeilTriangleSeparateLower (a : SuzukiPositiveAperture)
    (u v w : CCMArchimedeanFormDomain a) (x y z : ℝ) : ℝ :=
  (ccmRestrictedWeilSourceQuadratic a u - |ccmWeilRealPolar a u v| - |ccmWeilRealPolar a u w|) * x ^ 2 +
    (ccmRestrictedWeilSourceQuadratic a v - |ccmWeilRealPolar a u v| - |ccmWeilRealPolar a v w|) * y ^ 2 +
    (ccmRestrictedWeilSourceQuadratic a w - |ccmWeilRealPolar a u w| - |ccmWeilRealPolar a v w|) * z ^ 2

/-- Genuine signed-form improvement over the separate-edge lower estimate. -/
theorem ccmWeil_frustratedTriangle_lower (a : SuzukiPositiveAperture)
    (u v w : CCMArchimedeanFormDomain a)
    (huv : ccmWeilRealPolar a u v ≤ 0)
    (huw : ccmWeilRealPolar a u w ≤ 0)
    (hvw : 0 ≤ ccmWeilRealPolar a v w) (x y z : ℝ) :
    ccmWeilTriangleSeparateLower a u v w x y z +
      min (-ccmWeilRealPolar a u v) (min (-ccmWeilRealPolar a u w) (ccmWeilRealPolar a v w)) *
        (x ^ 2 + y ^ 2 + z ^ 2) ≤
      ccmRestrictedWeilSourceQuadratic a ((x : ℂ) • u + (y : ℂ) • v + (z : ℂ) • w) := by
  rw [ccmRestrictedWeilSourceQuadratic_real_three]
  unfold ccmWeilTriangleSeparateLower
  rw [abs_of_nonpos huv, abs_of_nonpos huw, abs_of_nonneg hvw]
  have h := frustratedTriangle_weighted_gap (-ccmWeilRealPolar a u v)
    (-ccmWeilRealPolar a u w) (ccmWeilRealPolar a v w) x y z
    (neg_nonneg.mpr huv) (neg_nonneg.mpr huw) hvw
  nlinarith only [h]

end RHTower
