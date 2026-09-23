import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# A relative-approximation calculus

`RelApprox x y e` says that `x` approximates the positive reference value `y` with relative error
at most `e`.  The relation is closed under products, quotients and square roots, with the obvious
error composition; taking a square root does not increase the relative error, because
`|√x − √y| = |x − y|/(√x + √y) ≤ |x − y|/√y`.

This is the bookkeeping device used to convert leading-order asymptotics of explicit sequences into
rigorous two-sided bounds without expanding the algebra by hand.
-/

namespace GaloisForLFunctions.HTGeometry

/-- `x` approximates the positive reference `y` with relative error at most `e`. -/
def RelApprox (x y e : ℝ) : Prop := |x - y| ≤ e * y

theorem RelApprox.nonneg_error {x y e : ℝ} (hy : 0 < y) (h : RelApprox x y e) : 0 ≤ e := by
  by_contra hcon
  rw [not_le] at hcon
  have h1 : |x - y| ≥ 0 := abs_nonneg _
  have h2 : e * y < 0 := mul_neg_of_neg_of_pos hcon hy
  exact absurd (le_trans h1 h) (not_le.mpr h2)

theorem RelApprox.lower {x y e : ℝ} (h : RelApprox x y e) : (1 - e) * y ≤ x := by
  have := (abs_le.mp h).1
  nlinarith [this]

theorem RelApprox.upper {x y e : ℝ} (h : RelApprox x y e) : x ≤ (1 + e) * y := by
  have := (abs_le.mp h).2
  nlinarith [this]

theorem RelApprox.pos {x y e : ℝ} (hy : 0 < y) (he : e < 1) (h : RelApprox x y e) : 0 < x := by
  have := h.lower
  nlinarith

theorem RelApprox.abs_le_of_lt_one {x y e : ℝ} (hy : 0 < y) (he : e < 1) (h : RelApprox x y e) :
    |x| ≤ (1 + e) * y := by
  have hpos : 0 < x := h.pos hy he
  rw [abs_of_pos hpos]
  exact h.upper

theorem RelApprox.mul {x y x' y' e e' : ℝ} (hy : 0 < y) (hy' : 0 < y')
    (he' : e' < 1)
    (h : RelApprox x y e) (h' : RelApprox x' y' e') :
    RelApprox (x * x') (y * y') (e + e' + e * e') := by
  have he0 : 0 ≤ e := h.nonneg_error hy
  have he'0 : 0 ≤ e' := h'.nonneg_error hy'
  have hx'abs : |x'| ≤ (1 + e') * y' := h'.abs_le_of_lt_one hy' he'
  have hkey : x * x' - y * y' = (x - y) * x' + y * (x' - y') := by ring
  rw [RelApprox, hkey]
  have h1 : |(x - y) * x'| ≤ (e * y) * ((1 + e') * y') := by
    rw [abs_mul]
    exact mul_le_mul h hx'abs (abs_nonneg _) (by positivity)
  have h2 : |y * (x' - y')| ≤ y * (e' * y') := by
    rw [abs_mul, abs_of_pos hy]
    exact mul_le_mul_of_nonneg_left h' hy.le
  calc |(x - y) * x' + y * (x' - y')| ≤ |(x - y) * x'| + |y * (x' - y')| := abs_add_le _ _
    _ ≤ (e * y) * ((1 + e') * y') + y * (e' * y') := by linarith
    _ = (e + e' + e * e') * (y * y') := by ring

theorem RelApprox.div {x y x' y' e e' : ℝ} (hy : 0 < y) (hy' : 0 < y')
    (he' : e' < 1) (h : RelApprox x y e) (h' : RelApprox x' y' e') :
    RelApprox (x / x') (y / y') ((e + e') / (1 - e')) := by
  have he : 0 ≤ e := h.nonneg_error hy
  have he'0 : 0 ≤ e' := h'.nonneg_error hy'
  have hx' : 0 < x' := h'.pos hy' he'
  have hlow : (1 - e') * y' ≤ x' := h'.lower
  have hden : 0 < 1 - e' := by linarith
  have key : |x / x' - y / y'| * (x' * y') = |x * y' - y * x'| := by
    rw [← abs_of_pos (mul_pos hx' hy'), ← abs_mul]
    congr 1
    field_simp
  have hnum : |x * y' - y * x'| ≤ (e + e') * (y * y') := by
    have hrw : x * y' - y * x' = (x - y) * y' - y * (x' - y') := by ring
    rw [hrw]
    have h1 : |(x - y) * y'| ≤ (e * y) * y' := by
      rw [abs_mul, abs_of_pos hy']
      exact mul_le_mul_of_nonneg_right h hy'.le
    have h2 : |y * (x' - y')| ≤ y * (e' * y') := by
      rw [abs_mul, abs_of_pos hy]
      exact mul_le_mul_of_nonneg_left h' hy.le
    calc |(x - y) * y' - y * (x' - y')| ≤ |(x - y) * y'| + |y * (x' - y')| := abs_sub _ _
      _ ≤ (e * y) * y' + y * (e' * y') := by linarith
      _ = (e + e') * (y * y') := by ring
  have hquot : |x / x' - y / y'| * (x' * y') ≤ (e + e') * (y * y') := by rw [key]; exact hnum
  have h1 : |x / x' - y / y'| * x' ≤ (e + e') * y := by
    refine le_of_mul_le_mul_right ?_ hy'
    calc |x / x' - y / y'| * x' * y' = |x / x' - y / y'| * (x' * y') := by ring
      _ ≤ (e + e') * (y * y') := hquot
      _ = (e + e') * y * y' := by ring
  have h2 : |x / x' - y / y'| ≤ (e + e') * y / x' := by
    rw [le_div_iff₀ hx']
    exact h1
  have h3 : (e + e') * y / x' ≤ (e + e') * y / ((1 - e') * y') := by
    have hnn : (0:ℝ) ≤ (e + e') * y := by positivity
    exact div_le_div_of_nonneg_left hnn (mul_pos hden hy') hlow
  have h4 : (e + e') * y / ((1 - e') * y') = (e + e') / (1 - e') * (y / y') := by
    field_simp
  show |x / x' - y / y'| ≤ (e + e') / (1 - e') * (y / y')
  rw [← h4]
  linarith

theorem RelApprox.sqrt {x y e : ℝ} (hy : 0 < y) (he : e < 1) (h : RelApprox x y e) :
    RelApprox (Real.sqrt x) (Real.sqrt y) e := by
  have he0 : 0 ≤ e := h.nonneg_error hy
  have hx : 0 < x := h.pos hy he
  have hsx : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
  have hsy : 0 < Real.sqrt y := Real.sqrt_pos.mpr hy
  have hxy : Real.sqrt x ^ (2 : ℕ) = x := Real.sq_sqrt hx.le
  have hyy : Real.sqrt y ^ (2 : ℕ) = y := Real.sq_sqrt hy.le
  have h3 : Real.sqrt y * Real.sqrt y = y := Real.mul_self_sqrt hy.le
  have hfac : (Real.sqrt x - Real.sqrt y) * (Real.sqrt x + Real.sqrt y) = x - y := by
    nlinarith [hxy, hyy]
  have hkey : |Real.sqrt x - Real.sqrt y| * (Real.sqrt x + Real.sqrt y) = |x - y| := by
    rw [← abs_of_pos (by positivity : (0:ℝ) < Real.sqrt x + Real.sqrt y), ← abs_mul, hfac]
  have h1 : |Real.sqrt x - Real.sqrt y| * Real.sqrt y
      ≤ |Real.sqrt x - Real.sqrt y| * (Real.sqrt x + Real.sqrt y) :=
    mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
  rw [hkey] at h1
  have h2 : |x - y| ≤ e * y := h
  show |Real.sqrt x - Real.sqrt y| ≤ e * Real.sqrt y
  refine le_of_mul_le_mul_right ?_ hsy
  calc |Real.sqrt x - Real.sqrt y| * Real.sqrt y ≤ e * y := by linarith
    _ = e * Real.sqrt y * Real.sqrt y := by rw [mul_assoc, h3]

theorem RelApprox.mono {x y e e' : ℝ} (hy : 0 < y) (h : RelApprox x y e) (hee : e ≤ e') :
    RelApprox x y e' := le_trans h (mul_le_mul_of_nonneg_right hee hy.le)

theorem RelApprox.of_abs_le {x y d e : ℝ} (h : |x - y| ≤ d) (hd : d ≤ e * y) :
    RelApprox x y e := le_trans h hd

theorem RelApprox.add {x y x' y' e e' : ℝ} (hy : 0 < y) (hy' : 0 < y')
    (h : RelApprox x y e) (h' : RelApprox x' y' e') :
    RelApprox (x + x') (y + y') (max e e') := by
  have he : 0 ≤ e := h.nonneg_error hy
  have he' : 0 ≤ e' := h'.nonneg_error hy'
  have h1 : |x - y| ≤ max e e' * y :=
    le_trans h (mul_le_mul_of_nonneg_right (le_max_left _ _) hy.le)
  have h2 : |x' - y'| ≤ max e e' * y' :=
    le_trans h' (mul_le_mul_of_nonneg_right (le_max_right _ _) hy'.le)
  have hrw : x + x' - (y + y') = (x - y) + (x' - y') := by ring
  show |x + x' - (y + y')| ≤ max e e' * (y + y')
  rw [hrw]
  calc |(x - y) + (x' - y')| ≤ |x - y| + |x' - y'| := abs_add_le _ _
    _ ≤ max e e' * y + max e e' * y' := by linarith
    _ = max e e' * (y + y') := by ring

theorem RelApprox.trans {x y y' e e' : ℝ} (hy : 0 < y) (hy' : 0 < y')
    (h : RelApprox x y e) (h' : RelApprox y y' e') :
    RelApprox x y' (e * (1 + e') + e') := by
  have he : 0 ≤ e := h.nonneg_error hy
  have he' : 0 ≤ e' := h'.nonneg_error hy'
  have hyu : y ≤ (1 + e') * y' := h'.upper
  have hrw : x - y' = (x - y) + (y - y') := by ring
  show |x - y'| ≤ (e * (1 + e') + e') * y'
  rw [hrw]
  calc |(x - y) + (y - y')| ≤ |x - y| + |y - y'| := abs_add_le _ _
    _ ≤ e * y + e' * y' := by
        have hh : |x - y| ≤ e * y := h
        have hh' : |y - y'| ≤ e' * y' := h'
        linarith
    _ ≤ e * ((1 + e') * y') + e' * y' := by nlinarith
    _ = (e * (1 + e') + e') * y' := by ring

end GaloisForLFunctions.HTGeometry
