import GaloisForLFunctions.HilbertMetric.Geometry.BonnetSecondForm

/-!
# Height maxima recover the actual Gauss normal

The positive radius matrix kills every tangential component of a critical
height direction. Unit length leaves two choices; the second derivative
excludes the opposite normal at a maximum.
-/

open scoped ContDiff
namespace GaloisForLFunctions.HilbertMetric.Geometry.BonnetHeightCritical
open BonnetSupport BonnetSurface StereographicFrame SchwartzRadius BonnetSecondForm
noncomputable section

/-- A unit height direction at a finite-chart maximum is the actual Gauss normal. -/
theorem normal_of_height_max (f : SchwartzMap (ℝ × ℝ) ℝ) (p : ℝ × ℝ)
    (n : Space) (hn : ‖n‖ = 1)
    (hx : IsLocalMax (fun t => inner ℝ
      (surface (support f (positiveScale f)) (t, p.2)) n) p.1)
    (hy : IsLocalMax (fun t => inner ℝ
      (surface (support f (positiveScale f)) (p.1, t)) n) p.2) :
    n = normal p := by
  let ρ := support f (positiveScale f)
  have hρ : ContDiff ℝ ∞ ρ := support_smooth (f.smooth ⊤) _
  have hdx := (surface_path hρ (hasDerivAt_id p.1) (hasDerivAt_const p.1 p.2)).inner
    ℝ (hasDerivAt_const p.1 n)
  have hdy := (surface_path hρ (hasDerivAt_const p.2 p.1) (hasDerivAt_id p.2)).inner
    ℝ (hasDerivAt_const p.2 n)
  have hex := hx.hasDerivAt_eq_zero hdx
  have hey := hy.hasDerivAt_eq_zero hdy
  simp only [one_smul, zero_smul, add_zero, zero_add, id_eq, Prod.mk.eta,
    inner_zero_right, inner_add_left, inner_smul_left, starRingEnd_apply, star_trivial] at hex hey
  let a := inner ℝ (tangentX p) n
  let b := inner ℝ (tangentY p) n
  have he₁ : radiusXX ρ p * a + radiusXY ρ p * b = 0 := hex
  have he₂ : radiusXY ρ p * a + radiusYY ρ p * b = 0 := hey
  have hquad : radiusXX ρ p * a ^ 2 + 2 * radiusXY ρ p * a * b +
      radiusYY ρ p * b ^ 2 = 0 := by
    nlinarith only [congrArg (fun t => a * t) he₁, congrArg (fun t => b * t) he₂]
  have hp := radius_uniform_positive f p a b
  change (a ^ 2 + b ^ 2) / 2 ≤ radiusXX ρ p * a ^ 2 +
    2 * radiusXY ρ p * a * b + radiusYY ρ p * b ^ 2 at hp
  rw [hquad] at hp
  have ha : a = 0 := by nlinarith only [hp, sq_nonneg b]
  have hb : b = 0 := by nlinarith only [hp, sq_nonneg a]
  have hnx : inner ℝ n (tangentX p) = 0 := (real_inner_comm _ _).trans ha
  have hny : inner ℝ n (tangentY p) = 0 := (real_inner_comm _ _).trans hb
  have hres := frame_resolution p n
  rw [hnx, hny] at hres
  simp only [mul_zero, zero_smul, add_zero] at hres
  let c := inner ℝ n (normal p)
  have hres' : n = c • normal p := hres
  have hsq : inner ℝ n n = 1 := by rw [real_inner_self_eq_norm_sq, hn]; norm_num
  rw [hres', inner_smul_left, inner_smul_right, (normal_metric p).1] at hsq
  simp only [starRingEnd_apply, star_trivial, mul_one] at hsq
  have hc : (c - 1) * (c + 1) = 0 := by nlinarith only [hsq]
  rcases mul_eq_zero.mp hc with hc | hc
  · have hc1 : c = 1 := by linarith only [hc]
    simpa only [hc1, one_smul] using hres'
  · have hc1 : c = -1 := by linarith only [hc]
    have he : n = -normal p := by simpa only [hc1, neg_one_smul] using hres'
    rw [he] at hx
    exact (no_opposite_height_max f p hx).elim

#print axioms normal_of_height_max
end
end GaloisForLFunctions.HilbertMetric.Geometry.BonnetHeightCritical
