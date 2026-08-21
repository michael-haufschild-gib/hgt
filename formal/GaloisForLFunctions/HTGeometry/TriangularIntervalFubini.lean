import GaloisForLFunctions.HTGeometry.BlockWindowFubini
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Fubini on the triangle `p < x < t ≤ q`

Two iterated interval integrals over the same triangle agree:

`∫_p^q F(x) (∫_x^q G(t) dt) dx = ∫_p^q (∫_p^t F(x) dx) G(t) dt`.

Only interval integrability of the two one-variable profiles is required; no continuity, no
compact support, and no boundedness.  The proof writes both sides as the integral of the
triangle-indicator of the product `F(x)G(t)` over the square and applies the product-majorant
Fubini theorem `integral_swap_of_dominated_prod`.

This is the exchange step behind every "prefix integral against a profile" identity — in
particular behind Suzuki's inverse Neumann Laplacian quadratic form.
-/

open MeasureTheory Set

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- The triangle `{(x,t) | x < t}` in the plane is measurable. -/
theorem measurableSet_strictLowerTriangle :
    MeasurableSet {z : ℝ × ℝ | z.1 < z.2} :=
  measurableSet_lt measurable_fst measurable_snd

/-- The triangle-indicator integrand `F(x)G(t)·1_{x<t}` attached to two profiles. -/
def triangleIntegrand (F G : ℝ → ℂ) (x t : ℝ) : ℂ :=
  if x < t then F x * G t else 0

theorem triangleIntegrand_uncurry (F G : ℝ → ℂ) :
    Function.uncurry (triangleIntegrand F G) =
      Set.indicator {z : ℝ × ℝ | z.1 < z.2} (fun z => F z.1 * G z.2) := by
  funext z
  simp [triangleIntegrand, Function.uncurry, Set.indicator_apply]

theorem norm_triangleIntegrand_le (F G : ℝ → ℂ) (x t : ℝ) :
    ‖triangleIntegrand F G x t‖ ≤ ‖F x‖ * ‖G t‖ := by
  unfold triangleIntegrand
  split_ifs with h
  · exact le_of_eq (norm_mul _ _)
  · simpa using mul_nonneg (norm_nonneg (F x)) (norm_nonneg (G t))

theorem aestronglyMeasurable_uncurry_triangleIntegrand
    {p q : ℝ} {F G : ℝ → ℂ}
    (hF : IntegrableOn F (Ioc p q) volume)
    (hG : IntegrableOn G (Ioc p q) volume) :
    AEStronglyMeasurable (Function.uncurry (triangleIntegrand F G))
      ((volume.restrict (Ioc p q)).prod (volume.restrict (Ioc p q))) := by
  rw [triangleIntegrand_uncurry]
  have h1 : AEStronglyMeasurable (fun z : ℝ × ℝ => F z.1)
      ((volume.restrict (Ioc p q)).prod (volume.restrict (Ioc p q))) :=
    hF.aestronglyMeasurable.comp_fst
  have h2 : AEStronglyMeasurable (fun z : ℝ × ℝ => G z.2)
      ((volume.restrict (Ioc p q)).prod (volume.restrict (Ioc p q))) :=
    hG.aestronglyMeasurable.comp_snd
  exact (h1.mul h2).indicator measurableSet_strictLowerTriangle

/-- Inner integral in the `t` variable: the triangle indicator cuts the square down to the
upper interval `(x, q]`. -/
theorem setIntegral_triangleIntegrand_right
    {p q x : ℝ} (F G : ℝ → ℂ) (hpx : p ≤ x) (hxq : x ≤ q) :
    (∫ t in Ioc p q, triangleIntegrand F G x t) = F x * ∫ t in x..q, G t := by
  have hsplit : ∀ t : ℝ, triangleIntegrand F G x t = F x * (Ioi x).indicator G t := by
    intro t
    unfold triangleIntegrand
    by_cases h : x < t <;> simp [h]
  have hset : Ioc p q ∩ Ioi x = Ioc x q := by
    ext t
    simp only [Set.mem_inter_iff, Set.mem_Ioc, Set.mem_Ioi]
    constructor
    · rintro ⟨⟨-, htq⟩, hxt⟩; exact ⟨hxt, htq⟩
    · rintro ⟨hxt, htq⟩; exact ⟨⟨lt_of_le_of_lt hpx hxt, htq⟩, hxt⟩
  simp_rw [hsplit]
  rw [MeasureTheory.integral_const_mul, MeasureTheory.setIntegral_indicator measurableSet_Ioi,
    hset, intervalIntegral.integral_of_le hxq]

/-- Inner integral in the `x` variable: the triangle indicator cuts the square down to the
lower interval `(p, t)`, which has the same integral as `(p, t]`. -/
theorem setIntegral_triangleIntegrand_left
    {p q t : ℝ} (F G : ℝ → ℂ) (hpt : p ≤ t) (htq : t ≤ q) :
    (∫ x in Ioc p q, triangleIntegrand F G x t) = (∫ x in p..t, F x) * G t := by
  have hsplit : ∀ x : ℝ, triangleIntegrand F G x t = (Iio t).indicator F x * G t := by
    intro x
    unfold triangleIntegrand
    by_cases h : x < t <;> simp [h]
  have hset : Ioc p q ∩ Iio t = Ioo p t := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_Ioc, Set.mem_Iio, Set.mem_Ioo]
    constructor
    · rintro ⟨⟨hpx, -⟩, hxt⟩; exact ⟨hpx, hxt⟩
    · rintro ⟨hpx, hxt⟩; exact ⟨⟨hpx, le_trans (le_of_lt hxt) htq⟩, hxt⟩
  simp_rw [hsplit]
  rw [MeasureTheory.integral_mul_const, MeasureTheory.setIntegral_indicator measurableSet_Iio,
    hset, ← MeasureTheory.integral_Ioc_eq_integral_Ioo,
    intervalIntegral.integral_of_le hpt]

/-- **Triangular interval Fubini.**  For interval-integrable profiles `F` and `G`,

`∫_p^q F(x) (∫_x^q G) dx = ∫_p^q (∫_p^t F) G(t) dt`.

Both sides are the integral of `F(x)G(t)` over the triangle `p < x < t ≤ q`. -/
theorem intervalIntegral_triangle_swap
    {p q : ℝ} (hpq : p ≤ q) {F G : ℝ → ℂ}
    (hF : IntervalIntegrable F volume p q) (hG : IntervalIntegrable G volume p q) :
    (∫ x in p..q, F x * ∫ t in x..q, G t) = ∫ t in p..q, (∫ x in p..t, F x) * G t := by
  have hFI : IntegrableOn F (Ioc p q) volume := hF.1
  have hGI : IntegrableOn G (Ioc p q) volume := hG.1
  have hswap :
      (∫ x in Ioc p q, ∫ t in Ioc p q, triangleIntegrand F G x t) =
        ∫ t in Ioc p q, ∫ x in Ioc p q, triangleIntegrand F G x t := by
    refine integral_swap_of_dominated_prod hFI.norm hGI.norm
      (aestronglyMeasurable_uncurry_triangleIntegrand hFI hGI)
      (Filter.Eventually.of_forall fun z => ?_)
    exact norm_triangleIntegrand_le F G z.1 z.2
  calc (∫ x in p..q, F x * ∫ t in x..q, G t)
      = ∫ x in Ioc p q, F x * ∫ t in x..q, G t :=
        intervalIntegral.integral_of_le hpq
    _ = ∫ x in Ioc p q, ∫ t in Ioc p q, triangleIntegrand F G x t := by
        refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioc ?_
        intro x hx
        exact (setIntegral_triangleIntegrand_right F G (le_of_lt hx.1) hx.2).symm
    _ = ∫ t in Ioc p q, ∫ x in Ioc p q, triangleIntegrand F G x t := hswap
    _ = ∫ t in Ioc p q, (∫ x in p..t, F x) * G t := by
        refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioc ?_
        intro t ht
        exact setIntegral_triangleIntegrand_left F G (le_of_lt ht.1) ht.2
    _ = ∫ t in p..q, (∫ x in p..t, F x) * G t :=
        (intervalIntegral.integral_of_le hpq).symm

end GaloisForLFunctions.HTGeometry
