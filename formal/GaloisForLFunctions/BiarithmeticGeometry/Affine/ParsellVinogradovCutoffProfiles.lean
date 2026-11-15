import GaloisForLFunctions.BiarithmeticGeometry.Affine.ParsellVinogradovFrameCutoffs

/-!
# Fixed profiles for ordered moment cutoffs

A normalized parallel translate moves the vertical degree-one coordinate
by its translation parameter. Nonzero cutoff values force this coordinate
strictly between minus two and two, so translates separated by at least
four have disjoint nonzero sets. Finite products of earlier normalized
cutoffs give smooth compactly supported profiles independent of scale and
direction.
-/

open scoped BigOperators
open GaloisForLFunctions.BiarithmeticGeometry.CoordinateCubeCutoff

namespace GaloisForLFunctions.BiarithmeticGeometry.ParsellVinogradov
noncomputable section

/-- A normalized vertical translation adds its parameter to the linear vertical coordinate. -/
theorem degreeOne_momentAffineAction_vertical (r k : ℕ) (t : ℝ)
    (x : AffineAxisSpace r (k + 1)) :
    momentAffineAction r (k + 1) 0 t x (degreeOneIndex r k 0) =
      t + x (degreeOneIndex r k 0) := by
  change degreeOneProjection r k (momentAffineAction r (k + 1) 0 t x) 0 = _
  rw [momentAffineAction, map_add, degreeOneProjection_moment, degreeOneProjection_vectorAffine]
  change t + (x (degreeOneIndex r k 0) + ∑ i : Fin (r + 1),
    (0 : Fin (r + 1) → ℝ) i * x (degreeOneIndex r k i.succ)) = _
  simp only [Pi.zero_apply, zero_mul, Finset.sum_const_zero, add_zero]

/-- A nonzero cutoff lies strictly inside each coordinate boundary. -/
theorem cubeCutoff_coordinate_lt {ι : Type*} [Fintype ι] (x : ι → ℝ)
    (hx : cubeCutoff x ≠ 0) (i : ι) : |x i| < 2 :=
  not_le.mp (fun h => hx (cubeCutoff_eq_zero_of_coordinate x i h))

/-- Parallel normalized cutoffs cannot both be nonzero at displacement at least four. -/
theorem cubeCutoff_mul_vertical_translate_eq_zero (r k : ℕ) (t : ℝ) (ht : 4 ≤ |t|)
    (x : AffineAxisSpace r (k + 1)) :
    cubeCutoff x * cubeCutoff (momentAffineAction r (k + 1) 0 t x) = 0 := by
  by_cases hx : cubeCutoff x = 0
  · rw [hx, zero_mul]
  have hc := abs_lt.mp (cubeCutoff_coordinate_lt x hx (degreeOneIndex r k 0))
  have hb : 2 ≤ |momentAffineAction r (k + 1) 0 t x (degreeOneIndex r k 0)| := by
    rw [degreeOne_momentAffineAction_vertical]
    apply not_lt.mp
    intro h
    have hd := abs_lt.mp h
    rcases le_total 0 t with ht0 | ht0
    · rw [abs_of_nonneg ht0] at ht
      linarith only [hc.1, hd.2, ht]
    · rw [abs_of_nonpos ht0] at ht
      linarith only [hc.2, hd.1, ht]
  rw [cubeCutoff_eq_zero_of_coordinate _ (degreeOneIndex r k 0) hb, mul_zero]

/-- Parallel physical cutoffs have zero product once their centers are four scales apart. -/
theorem frameCutoff_mul_eq_zero_of_separation (r k : ℕ) (ε : ℝ) (hε : ε ≠ 0)
    (δ : Fin (r + 1) → ℝ) (t s : ℝ) (h : 4 * |ε| ≤ |t - s|)
    (x : AffineAxisSpace r (k + 1)) :
    frameCutoff r (k + 1) ε δ t x * frameCutoff r (k + 1) ε δ s x = 0 := by
  have ht : 4 ≤ |(t - s) / ε| := by
    rw [abs_div]
    exact (le_div_iff₀ (abs_pos.mpr hε)).mpr h
  calc
    _ = cubeCutoff (momentFrameInverse r (k + 1) ε δ t x) *
        cubeCutoff (momentFrameInverse r (k + 1) ε δ s
          (momentFrame r (k + 1) ε δ t (momentFrameInverse r (k + 1) ε δ t x))) := by
      rw [momentFrame_frameInverse r (k + 1) ε hε]
      rfl
    _ = 0 := by
      rw [momentFrameInverse_parallelFrame r (k + 1) ε hε]
      exact cubeCutoff_mul_vertical_translate_eq_zero r k _ ht _

/-- The boundary indices at distance four grid-density units already have zero cutoff product. -/
theorem frameCutoff_integer_mul_eq_zero (r k q : ℕ) (ε : ℝ) (hε : ε ≠ 0)
    (δ : Fin (r + 1) → ℝ) (i j : ℤ)
    (h : 4 * (q + 1 : ℝ) ≤ |(i : ℝ) - (j : ℝ)|) (x : AffineAxisSpace r (k + 1)) :
    frameCutoff r (k + 1) ε δ (ε * (i : ℝ) / (q + 1 : ℝ)) x *
      frameCutoff r (k + 1) ε δ (ε * (j : ℝ) / (q + 1 : ℝ)) x = 0 := by
  apply frameCutoff_mul_eq_zero_of_separation r k ε hε δ _ _ _ x
  have hd : (0 : ℝ) < q + 1 := by positivity
  rw [show ε * (i : ℝ) / (q + 1 : ℝ) - ε * (j : ℝ) / (q + 1 : ℝ) =
    ε * (((i : ℝ) - (j : ℝ)) / (q + 1 : ℝ)) by ring,
    abs_mul, abs_div, abs_of_pos hd]
  calc
    _ = |ε| * 4 := mul_comm _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left ((le_div_iff₀ hd).mpr h) (abs_nonneg ε)

/-- A profile with a prescribed number of preceding integer-grid cutoffs. -/
def cutoffProfile (r k q : ℕ) (N : ℤ) (x : AffineAxisSpace r k) : ℝ :=
  cubeCutoff x * ∏ m ∈ Finset.Icc (1 : ℤ) N,
    (1 - cubeCutoff (momentAffineAction r k 0 ((m : ℝ) / (q + 1 : ℝ)) x))

theorem contDiff_cutoffProfile (r k q : ℕ) (N : ℤ) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (cutoffProfile r k q N) := by
  unfold cutoffProfile
  apply contDiff_cubeCutoff.mul
  apply contDiff_prod
  intro m _
  exact contDiff_const.sub (contDiff_cubeCutoff.comp (contDiff_momentAffineAction r k 0 _))

theorem hasCompactSupport_cutoffProfile (r k q : ℕ) (N : ℤ) :
    HasCompactSupport (cutoffProfile r k q N) := hasCompactSupport_cubeCutoff.mul_right

/-- Every normalized profile is a complex Schwartz function. -/
def cutoffProfileSchwartz (r k q : ℕ) (N : ℤ) : SchwartzMap (AffineAxisSpace r k) ℂ :=
  ((hasCompactSupport_cutoffProfile r k q N).comp_left
    (show Complex.ofRealCLM 0 = 0 from rfl)).toSchwartzMap
      (Complex.ofRealCLM.contDiff.comp (contDiff_cutoffProfile r k q N))

#print axioms degreeOne_momentAffineAction_vertical
#print axioms cubeCutoff_coordinate_lt
#print axioms cubeCutoff_mul_vertical_translate_eq_zero
#print axioms frameCutoff_mul_eq_zero_of_separation
#print axioms frameCutoff_integer_mul_eq_zero
#print axioms contDiff_cutoffProfile
#print axioms hasCompactSupport_cutoffProfile
#print axioms cutoffProfileSchwartz

end
end GaloisForLFunctions.BiarithmeticGeometry.ParsellVinogradov
