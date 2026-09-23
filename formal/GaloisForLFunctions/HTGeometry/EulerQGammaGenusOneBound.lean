import GaloisForLFunctions.HTGeometry.EulerQGammaGenusOne
import GaloisForLFunctions.HTGeometry.WeierstrassGenusFactor

/-!
# Quadratic estimates for the genus-one Euler unit

The genus-one Euler unit `E₁(w) = (1−w)eʷ` is the Weierstrass elementary factor of genus one, so
on the half disc it differs from `1` by at most a constant times `‖w‖²`; the same holds for its
reciprocal once the deviation is small enough to keep the unit away from zero.  These are the two
local estimates behind the normal convergence of the renormalised Euler q-Gamma product.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-! ## Reciprocals of near-one numbers -/

private theorem norm_le_of_norm_sub_one_le {u : ℂ} (h : ‖u - 1‖ ≤ 1 / 2) : 1 / 2 ≤ ‖u‖ := by
  have h1 : ‖(1 : ℂ)‖ - ‖u‖ ≤ ‖(1 : ℂ) - u‖ := norm_sub_norm_le _ _
  rw [norm_one] at h1
  rw [← norm_neg, neg_sub] at h
  linarith

theorem ne_zero_of_norm_sub_one_le {u : ℂ} (h : ‖u - 1‖ ≤ 1 / 2) : u ≠ 0 := by
  intro h0
  have := norm_le_of_norm_sub_one_le h
  rw [h0, norm_zero] at this
  linarith

/-- Inverting a number close to one doubles the deviation at worst. -/
theorem norm_inv_sub_one_le {u : ℂ} (h : ‖u - 1‖ ≤ 1 / 2) : ‖u⁻¹ - 1‖ ≤ 2 * ‖u - 1‖ := by
  have hu : u ≠ 0 := ne_zero_of_norm_sub_one_le h
  have hnorm : 1 / 2 ≤ ‖u‖ := norm_le_of_norm_sub_one_le h
  have hid : u⁻¹ - 1 = (1 - u) / u := by
    field_simp
  rw [hid, norm_div, ← norm_neg (1 - u), neg_sub]
  rw [div_le_iff₀ (lt_of_lt_of_le (by norm_num) hnorm)]
  nlinarith [norm_nonneg (u - 1)]

/-! ## The genus-one unit -/

theorem eulerProcessGenusOneFactor_eq_weierstrassFactor (w : ℂ) :
    eulerProcessGenusOneFactor w = weierstrassFactor 1 w := by
  rw [eulerProcessGenusOneFactor, weierstrassFactor, weierstrassLog]
  simp

/-- The constant in the genus-one quadratic estimate. -/
def genusOneBoundConst : ℝ := Real.exp (weierstrassLogBound 1)

theorem genusOneBoundConst_pos : 0 < genusOneBoundConst := Real.exp_pos _

/-- **The genus-one estimate.**  On the half disc `E₁` deviates from `1` quadratically. -/
theorem norm_genusOneFactor_sub_one_le {w : ℂ} (hw : ‖w‖ ≤ 1 / 2) :
    ‖eulerProcessGenusOneFactor w - 1‖ ≤ genusOneBoundConst * ‖w‖ ^ (2 : ℕ) := by
  rw [eulerProcessGenusOneFactor_eq_weierstrassFactor, genusOneBoundConst]
  simpa using norm_weierstrassFactor_sub_one_le 1 hw

/-- **The reciprocal genus-one estimate.** -/
theorem norm_inv_genusOneFactor_sub_one_le {w : ℂ} (hw : ‖w‖ ≤ 1 / 2)
    (hsmall : genusOneBoundConst * ‖w‖ ^ (2 : ℕ) ≤ 1 / 2) :
    ‖(eulerProcessGenusOneFactor w)⁻¹ - 1‖ ≤ 2 * genusOneBoundConst * ‖w‖ ^ (2 : ℕ) := by
  have hdev : ‖eulerProcessGenusOneFactor w - 1‖ ≤ 1 / 2 :=
    le_trans (norm_genusOneFactor_sub_one_le hw) hsmall
  have h := norm_inv_sub_one_le hdev
  have h2 := norm_genusOneFactor_sub_one_le hw
  calc ‖(eulerProcessGenusOneFactor w)⁻¹ - 1‖
      ≤ 2 * ‖eulerProcessGenusOneFactor w - 1‖ := h
    _ ≤ 2 * (genusOneBoundConst * ‖w‖ ^ (2 : ℕ)) := by linarith
    _ = 2 * genusOneBoundConst * ‖w‖ ^ (2 : ℕ) := by ring

/-! ## Multiplying near-one numbers -/

/-- Deviations from one add up under multiplication, with a cross term. -/
theorem norm_mul_sub_one_le {u v : ℂ} {a b : ℝ} (hu : ‖u - 1‖ ≤ a) (hv : ‖v - 1‖ ≤ b) :
    ‖u * v - 1‖ ≤ a + b + a * b := by
  have ha : 0 ≤ a := le_trans (norm_nonneg _) hu
  have hb : 0 ≤ b := le_trans (norm_nonneg _) hv
  have hid : u * v - 1 = (u - 1) * (v - 1) + (u - 1) + (v - 1) := by ring
  rw [hid]
  refine le_trans (norm_add_le _ _) ?_
  refine le_trans (add_le_add (norm_add_le _ _) le_rfl) ?_
  rw [norm_mul]
  have hcross : ‖u - 1‖ * ‖v - 1‖ ≤ a * b :=
    mul_le_mul hu hv (norm_nonneg _) ha
  linarith

/-! ## The exponential near zero -/

/-- An unrestricted bound for the deviation of `exp` from one. -/
theorem norm_cexp_sub_one_le (w : ℂ) : ‖Complex.exp w - 1‖ ≤ Real.exp ‖w‖ * ‖w‖ := by
  have hconv : Convex ℝ (Metric.closedBall (0 : ℂ) ‖w‖) := convex_closedBall _ _
  have hzero : (0 : ℂ) ∈ Metric.closedBall (0 : ℂ) ‖w‖ := by
    simp [Metric.mem_closedBall, norm_nonneg]
  have hmem : w ∈ Metric.closedBall (0 : ℂ) ‖w‖ := by
    simp [Metric.mem_closedBall]
  have hbound : ∀ ζ ∈ Metric.closedBall (0 : ℂ) ‖w‖,
      ‖deriv Complex.exp ζ‖ ≤ Real.exp ‖w‖ := by
    intro ζ hζ
    rw [Metric.mem_closedBall, dist_zero_right] at hζ
    rw [(Complex.hasDerivAt_exp ζ).deriv, Complex.norm_exp]
    exact Real.exp_le_exp.mpr (le_trans (Complex.re_le_norm ζ) hζ)
  have hmv := hconv.norm_image_sub_le_of_norm_deriv_le
    (fun ζ _ => Complex.differentiable_exp ζ) hbound hzero hmem
  rw [Complex.exp_zero] at hmv
  simpa using hmv

/-- The bound `t ↦ eᵗ·t` is monotone on the nonnegative reals. -/
theorem exp_mul_self_mono {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    Real.exp a * a ≤ Real.exp b * b :=
  mul_le_mul (Real.exp_le_exp.mpr hab) hab ha (Real.exp_pos b).le

theorem norm_cexp_sub_one_le_of_le {w : ℂ} {B : ℝ} (hB : ‖w‖ ≤ B) :
    ‖Complex.exp w - 1‖ ≤ Real.exp B * B :=
  le_trans (norm_cexp_sub_one_le w) (exp_mul_self_mono (norm_nonneg w) hB)

end

end GaloisForLFunctions.HTGeometry
