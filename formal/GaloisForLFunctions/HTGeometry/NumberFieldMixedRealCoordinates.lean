import GaloisForLFunctions.HTGeometry.NumberFieldUnitLogDiscrete
import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic

/-!
# Real coordinates and weighted scaling on mixed Minkowski space

The mixed embedding has one real coordinate at each real place and one complex coordinate at each
complex place.  Splitting each complex coordinate into real and imaginary parts produces exactly
the multiplicity-weighted real coordinate set.  Placewise exponential scaling is diagonal in these
coordinates, with complex places occurring twice.
-/

namespace GaloisForLFunctions.HTGeometry

open NumberField NumberField.InfinitePlace
open scoped Classical NumberField

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

/-- Real coordinates underlying mixed Minkowski space. -/
abbrev numberFieldMixedRealCoordinateIndex (K : Type*) [Field K] :=
  Sum {w : InfinitePlace K // w.IsReal} ({w : InfinitePlace K // w.IsComplex} × Fin 2)

noncomputable instance : Nonempty (numberFieldMixedRealCoordinateIndex K) := by
  let σ : K →+* ℂ := Classical.choice inferInstance
  let w : InfinitePlace K := InfinitePlace.mk σ
  rcases InfinitePlace.isReal_or_isComplex w with hw | hw
  · exact ⟨Sum.inl ⟨w, hw⟩⟩
  · exact ⟨Sum.inr (⟨w, hw⟩, 0)⟩

/-- Split every complex mixed coordinate into its real and imaginary parts. -/
def numberFieldMixedRealCoordinates :
    mixedEmbedding.mixedSpace K ≃ₗ[ℝ] (numberFieldMixedRealCoordinateIndex K → ℝ) where
  toFun z := fun i => match i with
    | Sum.inl w => z.1 w
    | Sum.inr (w, j) => if j = 0 then (z.2 w).re else (z.2 w).im
  invFun x :=
    (fun w => x (Sum.inl w),
      fun w => ⟨x (Sum.inr (w, 0)), x (Sum.inr (w, 1))⟩)
  left_inv z := by
    apply Prod.ext
    · funext w
      rfl
    · funext w
      apply Complex.ext <;> rfl
  right_inv x := by
    funext i
    rcases i with w | ⟨w, j⟩
    · rfl
    · fin_cases j <;> rfl
  map_add' z z' := by
    funext i
    rcases i with w | ⟨w, j⟩
    · rfl
    · fin_cases j <;> simp
  map_smul' c z := by
    funext i
    rcases i with w | ⟨w, j⟩
    · rfl
    · fin_cases j <;> simp

/-- Scale a mixed vector by `exp (-y_w)` at each archimedean place. -/
def numberFieldMixedPlaceScale (y : InfinitePlace K → ℝ) :
    mixedEmbedding.mixedSpace K ≃ₗ[ℝ] mixedEmbedding.mixedSpace K where
  toFun z :=
    (fun w => Real.exp (-y w.1) * z.1 w,
      fun w => Complex.ofReal (Real.exp (-y w.1)) * z.2 w)
  invFun z :=
    (fun w => Real.exp (y w.1) * z.1 w,
      fun w => Complex.ofReal (Real.exp (y w.1)) * z.2 w)
  left_inv z := by
    apply Prod.ext
    · funext w
      change Real.exp (y w.1) * (Real.exp (-y w.1) * z.1 w) = z.1 w
      rw [← mul_assoc, ← Real.exp_add]
      simp
    · funext w
      change Complex.ofReal (Real.exp (y w.1)) *
        (Complex.ofReal (Real.exp (-y w.1)) * z.2 w) = z.2 w
      rw [← mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add]
      simp
  right_inv z := by
    apply Prod.ext
    · funext w
      change Real.exp (-y w.1) * (Real.exp (y w.1) * z.1 w) = z.1 w
      rw [← mul_assoc, ← Real.exp_add]
      simp
    · funext w
      change Complex.ofReal (Real.exp (-y w.1)) *
        (Complex.ofReal (Real.exp (y w.1)) * z.2 w) = z.2 w
      rw [← mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add]
      simp
  map_add' z z' := by
    apply Prod.ext <;> funext w <;> simp [mul_add]
  map_smul' c z := by
    apply Prod.ext
    · funext w
      simp [mul_assoc, mul_comm c]
    · funext w
      change Complex.ofReal (Real.exp (-y w.1)) * (Complex.ofReal c * z.2 w) =
        Complex.ofReal c * (Complex.ofReal (Real.exp (-y w.1)) * z.2 w)
      ring

/-- Positive diagonal scale on split real coordinates. -/
def numberFieldMixedCoordinateScale (y : InfinitePlace K → ℝ) :
    numberFieldMixedRealCoordinateIndex K → ℝ
  | Sum.inl w => Real.exp (-y w.1)
  | Sum.inr (w, _) => Real.exp (-y w.1)

/-- Logarithm of the split-coordinate scale. -/
def numberFieldMixedCoordinateLogScale (y : InfinitePlace K → ℝ) :
    numberFieldMixedRealCoordinateIndex K → ℝ
  | Sum.inl w => -y w.1
  | Sum.inr (w, _) => -y w.1

private theorem sum_isReal_subtype (f : InfinitePlace K → ℝ) :
    ∑ w : {w : InfinitePlace K // w.IsReal}, f w =
      ∑ w ∈ (Finset.univ.filter fun w : InfinitePlace K => w.IsReal), f w := by
  classical
  apply Finset.sum_bij (fun w _ => w.1)
  · intro w _
    simp [w.2]
  · intro w _ w' _ h
    exact Subtype.ext h
  · intro w hw
    have hreal := (Finset.mem_filter.mp hw).2
    exact ⟨⟨w, hreal⟩, Finset.mem_univ _, rfl⟩
  · intro w _
    rfl

private theorem sum_isComplex_subtype (f : InfinitePlace K → ℝ) :
    ∑ w : {w : InfinitePlace K // w.IsComplex}, f w =
      ∑ w ∈ (Finset.univ.filter fun w : InfinitePlace K => ¬w.IsReal), f w := by
  classical
  apply Finset.sum_bij (fun w _ => w.1)
  · intro w _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact InfinitePlace.not_isReal_iff_isComplex.mpr w.2
  · intro w _ w' _ h
    exact Subtype.ext h
  · intro w hw
    have hcomplex := (Finset.mem_filter.mp hw).2
    exact ⟨⟨w, InfinitePlace.not_isReal_iff_isComplex.mp hcomplex⟩,
      Finset.mem_univ _, rfl⟩
  · intro w _
    rfl

/-- Split coordinate log-scales sum to the negative weighted place sum. -/
theorem sum_numberFieldMixedCoordinateLogScale (y : InfinitePlace K → ℝ) :
    ∑ i, numberFieldMixedCoordinateLogScale y i =
      -(∑ w : InfinitePlace K, (mult w : ℝ) * y w) := by
  classical
  have hweighted :
      (∑ w : InfinitePlace K, (mult w : ℝ) * y w) =
        (∑ w ∈ (Finset.univ.filter fun w : InfinitePlace K => w.IsReal), y w) +
          2 * ∑ w ∈ (Finset.univ.filter fun w : InfinitePlace K => ¬w.IsReal), y w := by
    rw [← Finset.sum_filter_add_sum_filter_not (Finset.univ)
      (fun w : InfinitePlace K => w.IsReal) (fun w => (mult w : ℝ) * y w)]
    congr 1
    · apply Finset.sum_congr rfl
      intro w hw
      have hreal := (Finset.mem_filter.mp hw).2
      simp [InfinitePlace.mult, hreal]
    · rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro w hw
      have hnot := (Finset.mem_filter.mp hw).2
      simp [InfinitePlace.mult, hnot]
  rw [Fintype.sum_sum_type, Fintype.sum_prod_type]
  simp only [numberFieldMixedCoordinateLogScale, Fin.sum_univ_two]
  simp only [Finset.sum_add_distrib, Finset.sum_neg_distrib]
  rw [sum_isReal_subtype (f := y), sum_isComplex_subtype (f := y), hweighted]
  ring

/-- Weighted-zero place profiles give determinant-one split-coordinate scaling. -/
theorem prod_numberFieldMixedCoordinateScale (y : InfinitePlace K → ℝ)
    (hy : ∑ w : InfinitePlace K, (mult w : ℝ) * y w = 0) :
    ∏ i, numberFieldMixedCoordinateScale y i = 1 := by
  have hscale (i : numberFieldMixedRealCoordinateIndex K) :
      numberFieldMixedCoordinateScale y i =
        Real.exp (numberFieldMixedCoordinateLogScale y i) := by
    rcases i with w | ⟨w, j⟩ <;> rfl
  simp_rw [hscale, ← Real.exp_sum]
  rw [sum_numberFieldMixedCoordinateLogScale, hy, neg_zero, Real.exp_zero]

omit [NumberField K] in
theorem numberFieldMixedRealCoordinates_placeScale
    (y : InfinitePlace K → ℝ) (z : mixedEmbedding.mixedSpace K) :
    numberFieldMixedRealCoordinates (numberFieldMixedPlaceScale y z) =
      fun i => numberFieldMixedCoordinateScale y i * numberFieldMixedRealCoordinates z i := by
  funext i
  rcases i with w | ⟨w, j⟩
  · rfl
  · fin_cases j
    · change (Complex.ofReal (Real.exp (-y w.1)) * z.2 w).re =
        Real.exp (-y w.1) * (z.2 w).re
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    · change (Complex.ofReal (Real.exp (-y w.1)) * z.2 w).im =
        Real.exp (-y w.1) * (z.2 w).im
      simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]

omit [NumberField K] in
theorem numberFieldMixedCoordinateScale_pos (y : InfinitePlace K → ℝ) (i) :
    0 < numberFieldMixedCoordinateScale y i := by
  rcases i with w | ⟨w, j⟩
  · exact Real.exp_pos _
  · exact Real.exp_pos _

end

end GaloisForLFunctions.HTGeometry
