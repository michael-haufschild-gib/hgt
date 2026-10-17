import GaloisForLFunctions.BiScaleUncertainty.ClampedExponentialRamp
import GaloisForLFunctions.BiScaleUncertainty.ExponentialTentMoments
import Mathlib.Analysis.Calculus.MeanValue

/-! Explicit Lipschitz estimates for the nonsmooth factorial-source profiles. -/

open Set
namespace GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
noncomputable section
set_option autoImplicit false

theorem exp_abs_sub_le_of_le {L x y : ℝ} (hx : x ≤ L) (hy : y ≤ L) :
    |Real.exp x - Real.exp y| ≤ Real.exp L * |x-y| := by
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := Real.exp) (f' := Real.exp) (s := Iic L)
    (fun t _ => (Real.hasDerivAt_exp t).hasDerivWithinAt)
    (fun t ht => by simpa only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos t)]
      using Real.exp_le_exp.mpr ht)
    (convex_Iic L) hy hx
  simpa only [Real.norm_eq_abs] using h

/-- A profile zero at and outside both endpoints inherits its interval estimate. -/
theorem compact_interval_abs_sub_le {f : ℝ → ℝ} {a b K : ℝ}
    (hab : a ≤ b) (hK : 0 ≤ K)
    (hleft : ∀ x, x ≤ a → f x = 0) (hright : ∀ x, b ≤ x → f x = 0)
    (hlocal : ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, |f x-f y| ≤ K*|x-y|)
    (x y : ℝ) : |f x-f y| ≤ K*|x-y| := by
  let c : ℝ → ℝ := fun t => min b (max a t)
  have hmem (t : ℝ) : c t ∈ Icc a b :=
    ⟨le_min hab (le_max_left _ _), min_le_left _ _⟩
  have heq (t : ℝ) : f t = f (c t) := by
    by_cases hta : t ≤ a
    · have hc : c t = a := by simp [c, max_eq_left hta, min_eq_right hab]
      rw [hc, hleft t hta, hleft a le_rfl]
    · by_cases hbt : b ≤ t
      · have hc : c t = b := by
          simp [c, max_eq_right (hab.trans hbt), min_eq_left hbt]
        rw [hc, hright t hbt, hright b le_rfl]
      · have hc : c t = t := by
          simp [c, max_eq_right (le_of_not_ge hta), min_eq_right (le_of_not_ge hbt)]
        rw [hc]
  have hc : |c x-c y| ≤ |x-y| := by
    have hmin := abs_min_sub_min_le_max b (max a x) b (max a y)
    have hmax := abs_max_sub_max_le_max a x a y
    simp only [sub_self, abs_zero, max_eq_right (abs_nonneg (max a x-max a y))] at hmin
    simp only [sub_self, abs_zero, max_eq_right (abs_nonneg (x-y))] at hmax
    exact hmin.trans hmax
  rw [heq x, heq y]
  exact (hlocal (c x) (hmem x) (c y) (hmem y)).trans (mul_le_mul_of_nonneg_left hc hK)

theorem clampedRamp_abs_sub_le {ε : ℝ} (hε : 0 < ε) (a b : ℝ) :
    |clampedRamp ε a-clampedRamp ε b| ≤ |a-b|/ε := by
  have hmin := abs_min_sub_min_le_max (1 : ℝ) (max 0 ((1+ε-a)/ε))
    1 (max 0 ((1+ε-b)/ε))
  have hmax := abs_max_sub_max_le_max (0 : ℝ) ((1+ε-a)/ε) 0 ((1+ε-b)/ε)
  simp only [sub_self, abs_zero,
    max_eq_right (abs_nonneg (max 0 ((1+ε-a)/ε)-max 0 ((1+ε-b)/ε)))] at hmin
  simp only [sub_self, abs_zero,
    max_eq_right (abs_nonneg ((1+ε-a)/ε-(1+ε-b)/ε))] at hmax
  change |min 1 (max 0 ((1+ε-a)/ε))-min 1 (max 0 ((1+ε-b)/ε))| ≤ _
  calc
    _ ≤ |(1+ε-a)/ε-(1+ε-b)/ε| := hmin.trans hmax
    _ = |a-b|/ε := by
      rw [show (1+ε-a)/ε-(1+ε-b)/ε = -(a-b)/ε by ring,
        abs_div, abs_neg, abs_of_pos hε]

theorem causalTent_abs_sub_le (δ a b : ℝ) :
    |causalTent δ a-causalTent δ b| ≤ |a-b| := by
  have hmax := abs_max_sub_max_le_max (0 : ℝ) (min a (2*δ-a)) 0 (min b (2*δ-b))
  have hmin := abs_min_sub_min_le_max a (2*δ-a) b (2*δ-b)
  simp only [sub_self, abs_zero,
    max_eq_right (abs_nonneg (min a (2*δ-a)-min b (2*δ-b)))] at hmax
  rw [show 2*δ-a-(2*δ-b) = -(a-b) by ring, abs_neg, max_self] at hmin
  exact hmax.trans hmin

theorem abs_mul_sub_mul_le (a b c d : ℝ) :
    |a*b-c*d| ≤ |a-c| * |b|+|c| * |b-d| := by
  calc
    _ = |(a-c)*b+c*(b-d)| := by congr 1; ring
    _ ≤ |(a-c)*b|+|c*(b-d)| := abs_add_le _ _
    _ = _ := by rw [abs_mul, abs_mul]

end
end GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
