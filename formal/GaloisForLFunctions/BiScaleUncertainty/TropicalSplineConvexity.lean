import GaloisForLFunctions.BiScaleUncertainty.TropicalJensen
import Mathlib.Analysis.Convex.Function

/-!
# Convexity of continuous finite-divisor tropical characteristics

Splitting each slope weight into its positive and negative parts writes a
finite spline as a difference of convex functions. The tropical
characteristic is the symmetric boundary average of their maximum,
minus the pole potential at the origin. Thus it is convex and even,
and is nondecreasing on nonnegative radii.

This implements the finite continuous case of the entire-quotient
decomposition in Cao–Korhonen–Wang, Proposition 2.7, and identifies the
convex mechanism that is unavailable for arbitrary discontinuities.
-/

namespace GaloisForLFunctions.BiScaleUncertainty.TropicalJensen
open scoped BigOperators
noncomputable section

/-- The convex potential of the negative slope jumps. -/
def polePotential (s : Finset ℝ) (w : ℝ → ℝ) (x : ℝ) : ℝ :=
  spline s (fun t => max 0 (-w t)) 0 0 x

/-- The affine part together with the positive slope jumps. -/
def rootPotential (s : Finset ℝ) (w : ℝ → ℝ) (a b x : ℝ) : ℝ :=
  spline s (fun t => max 0 (w t)) a b x

/-- Positive and negative slope supports are disjoint; their potentials recover the spline. -/
theorem spline_jordan_decomposition (s : Finset ℝ) (w : ℝ → ℝ) (a b x : ℝ) :
    rootPotential s w a b x - polePotential s w x = spline s w a b x := by
  have h (t : ℝ) : max 0 (w t) - max 0 (-w t) = w t := by
    rcases le_total 0 (w t) with ht | ht
    · rw [max_eq_right ht, max_eq_left (neg_nonpos.mpr ht)]
      ring
    · rw [max_eq_left ht, max_eq_right (neg_nonneg.mpr ht)]
      ring
  have hs : (∑ t ∈ s, max 0 (w t) * |x - t|) -
      (∑ t ∈ s, max 0 (-w t) * |x - t|) = ∑ t ∈ s, w t * |x - t| := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro t _
    rw [← sub_mul, h]
  simp only [rootPotential, polePotential, spline, zero_mul, zero_add]
  linarith only [hs]

/-- The maximum of the root and pole potentials controls the characteristic exactly. -/
def envelope (s : Finset ℝ) (w : ℝ → ℝ) (a b x : ℝ) : ℝ :=
  max (rootPotential s w a b x) (polePotential s w x)

theorem characteristic_eq_envelope (s : Finset ℝ) (w : ℝ → ℝ) (a b r : ℝ) :
    characteristic s w a b r =
      (envelope s w a b r + envelope s w a b (-r)) / 2 - polePotential s w 0 := by
  have hp : (polePotential s w r + polePotential s w (-r)) / 2 - polePotential s w 0 =
      poleCount s w r := spline_jensen s (fun t => max 0 (-w t)) 0 0 r
  have hmax (x : ℝ) : max 0 (spline s w a b x) + polePotential s w x = envelope s w a b x := by
    have h := spline_jordan_decomposition s w a b x
    unfold envelope
    simp only [max_def]
    split_ifs <;> linarith
  unfold characteristic proximity
  linarith only [hp, hmax r, hmax (-r)]

/-- Positive and negative slope jumps have no common support. -/
theorem jordan_weights_disjoint (w : ℝ → ℝ) (t : ℝ) :
    min (max 0 (w t)) (max 0 (-w t)) = 0 := by
  rcases le_total 0 (w t) with ht | ht
  · rw [max_eq_right ht, max_eq_left (neg_nonpos.mpr ht), min_eq_right ht]
  · rw [max_eq_left ht, max_eq_right (neg_nonneg.mpr ht), min_eq_left (neg_nonneg.mpr ht)]

/-- Nonnegative slope jumps produce a convex spline, for every affine part. -/
theorem rootPotential_convex (s : Finset ℝ) (w : ℝ → ℝ) (a b : ℝ) :
    ConvexOn ℝ Set.univ (rootPotential s w a b) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ u v hu hv huv
  have hterm (t : ℝ) : |u * x + v * y - t| ≤ u * |x - t| + v * |y - t| := by
    have he : u * x + v * y - t = u * (x - t) + v * (y - t) := by
      have h := congrArg (fun z : ℝ => z * t) huv
      linear_combination h
    rw [he]
    calc
      _ ≤ |u * (x - t)| + |v * (y - t)| := by
        simpa only [sub_neg_eq_add, abs_neg] using
          (abs_sub (u * (x - t)) (-(v * (y - t))))
      _ = _ := by rw [abs_mul, abs_mul, abs_of_nonneg hu, abs_of_nonneg hv]
  have hs := Finset.sum_le_sum (s := s) (fun t _ =>
    mul_le_mul_of_nonneg_left (hterm t) (le_max_left 0 (w t)))
  have hexp : (∑ t ∈ s, max 0 (w t) * (u * |x - t| + v * |y - t|)) =
      u * (∑ t ∈ s, max 0 (w t) * |x - t|) +
      v * (∑ t ∈ s, max 0 (w t) * |y - t|) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro t _
    ring
  rw [hexp] at hs
  have hb : (u + v) * b = b := by rw [huv, one_mul]
  simp only [rootPotential, spline, smul_eq_mul]
  nlinarith only [hs, hb]

theorem polePotential_convex (s : Finset ℝ) (w : ℝ → ℝ) :
    ConvexOn ℝ Set.univ (polePotential s w) :=
  rootPotential_convex s (fun t => -w t) 0 0

theorem envelope_convex (s : Finset ℝ) (w : ℝ → ℝ) (a b : ℝ) :
    ConvexOn ℝ Set.univ (envelope s w a b) :=
  (rootPotential_convex s w a b).sup (polePotential_convex s w)

/-- Continuous finite-divisor characteristics are convex on the full radius line. -/
theorem characteristic_convex (s : Finset ℝ) (w : ℝ → ℝ) (a b : ℝ) :
    ConvexOn ℝ Set.univ (characteristic s w a b) := by
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy u v hu hv huv
  have hp := (envelope_convex s w a b).2 hx hy hu hv huv
  have hn := (envelope_convex s w a b).2 (Set.mem_univ (-x)) (Set.mem_univ (-y)) hu hv huv
  simp only [smul_eq_mul] at hp hn ⊢
  rw [show u * -x + v * -y = -(u * x + v * y) by ring] at hn
  simp only [characteristic_eq_envelope]
  have hc : (u + v) * polePotential s w 0 = polePotential s w 0 := by rw [huv, one_mul]
  linarith only [hp, hn, hc]

theorem characteristic_even (s : Finset ℝ) (w : ℝ → ℝ) (a b r : ℝ) :
    characteristic s w a b (-r) = characteristic s w a b r := by
  simp only [characteristic_eq_envelope, neg_neg, add_comm]

/-- Convexity and evenness imply monotonicity on nonnegative radii. -/
theorem characteristic_monotoneOn (s : Finset ℝ) (w : ℝ → ℝ) (a b : ℝ) :
    MonotoneOn (characteristic s w a b) (Set.Ici 0) := by
  intro x hx y hy hxy
  have hx0 : 0 ≤ x := hx
  have hy0 : 0 ≤ y := hy
  by_cases hyz : y = 0
  · have hxz : x = 0 := le_antisymm (hyz ▸ hxy) hx0
    simp only [hxz, hyz, le_refl]
  have hyp : 0 < y := lt_of_le_of_ne hy0 (Ne.symm hyz)
  let u := (y + x) / (2 * y)
  let v := (y - x) / (2 * y)
  have hu : 0 ≤ u := div_nonneg (add_nonneg hy0 hx0) (by positivity)
  have hv : 0 ≤ v := div_nonneg (sub_nonneg.mpr hxy) (by positivity)
  have huv : u + v = 1 := by dsimp only [u, v]; field_simp [hyz]; ring
  have hpoint : u * y + v * (-y) = x := by dsimp only [u, v]; field_simp [hyz]; ring
  have h := (characteristic_convex s w a b).2
    (Set.mem_univ y) (Set.mem_univ (-y)) hu hv huv
  simp only [smul_eq_mul] at h
  rw [hpoint, characteristic_even, ← add_mul, huv, one_mul] at h
  exact h

#print axioms spline_jordan_decomposition
#print axioms characteristic_eq_envelope
#print axioms characteristic_convex
#print axioms characteristic_monotoneOn

end
end GaloisForLFunctions.BiScaleUncertainty.TropicalJensen
