import GaloisForLFunctions.HTGeometry.DeterminantOneLatticeShortVector
import GaloisForLFunctions.HTGeometry.NumberFieldMixedRealCoordinates
import GaloisForLFunctions.HTGeometry.NumberFieldUnitPlaceLog

/-!
# Uniform Minkowski reduction for number-field integers

Every weighted-zero archimedean profile defines a determinant-one deformation of the Minkowski
lattice.  A single radius, independent of that profile, contains a nonzero algebraic integer after
the corresponding deformation.
-/

namespace GaloisForLFunctions.HTGeometry

open NumberField NumberField.InfinitePlace
open scoped Classical NumberField

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

/-- Uniform scaled-coordinate Minkowski bound for nonzero algebraic integers. -/
theorem exists_numberFieldInteger_scaled_realCoordinates_norm_le :
    ∃ R : ℝ, 0 < R ∧ ∀ y : InfinitePlace K → ℝ,
      (∑ w : InfinitePlace K, (mult w : ℝ) * y w = 0) →
        ∃ α : 𝓞 K, α ≠ 0 ∧
          ‖numberFieldMixedRealCoordinates
            (numberFieldMixedPlaceScale y (mixedEmbedding K (α : K)))‖ ≤ R := by
  let e := numberFieldMixedRealCoordinates (K := K)
  let b := (mixedEmbedding.latticeBasis K).map e
  obtain ⟨R, hR, hRall⟩ :=
    exists_uniform_ne_zero_zspan_positiveDiagonal_norm_le b
  refine ⟨R, hR, ?_⟩
  intro y hy
  let s := numberFieldMixedCoordinateScale y
  have hs : ∀ i, 0 < s i := numberFieldMixedCoordinateScale_pos y
  have hprod : ∏ i, s i = 1 := prod_numberFieldMixedCoordinateScale y hy
  obtain ⟨x, hx, hx0, hxR⟩ := hRall s hs hprod
  have hxMap : x ∈ Submodule.map
      (e.restrictScalars ℤ : mixedEmbedding.mixedSpace K →ₗ[ℤ]
        (numberFieldMixedRealCoordinateIndex K → ℝ))
      (mixedEmbedding.integerLattice K) := by
    rw [← mixedEmbedding.span_latticeBasis K, ZSpan.map]
    exact hx
  rcases hxMap with ⟨z, hz, hzx⟩
  rcases hz with ⟨α, rfl⟩
  have hα : α ≠ 0 := by
    intro hα0
    apply hx0
    rw [← hzx, hα0]
    simp
  refine ⟨α, hα, ?_⟩
  calc
    ‖numberFieldMixedRealCoordinates
        (numberFieldMixedPlaceScale y (mixedEmbedding K (α : K)))‖ =
        ‖positiveDiagonalLinearEquiv s hs
          (numberFieldMixedRealCoordinates (mixedEmbedding K (α : K)))‖ := by
      congr 1
      rw [numberFieldMixedRealCoordinates_placeScale,
        positiveDiagonalLinearEquiv_apply]
    _ = ‖positiveDiagonalLinearEquiv s hs x‖ := by
      have hzx' : e (mixedEmbedding K (α : K)) = x := hzx
      rw [hzx']
    _ ≤ R := hxR

/-- Uniform place-value form of number-field Minkowski reduction. -/
theorem exists_numberFieldInteger_placeValue_le :
    ∃ C : ℝ, 0 < C ∧ ∀ y : InfinitePlace K → ℝ,
      (∑ w : InfinitePlace K, (mult w : ℝ) * y w = 0) →
        ∃ α : 𝓞 K, α ≠ 0 ∧ ∀ w : InfinitePlace K,
          w (α : K) ≤ C * Real.exp (y w) := by
  obtain ⟨R, hR, hRall⟩ :=
    exists_numberFieldInteger_scaled_realCoordinates_norm_le (K := K)
  refine ⟨2 * R, by positivity, ?_⟩
  intro y hy
  obtain ⟨α, hα, hαR⟩ := hRall y hy
  let v := numberFieldMixedRealCoordinates
    (numberFieldMixedPlaceScale y (mixedEmbedding K (α : K)))
  have hcoord (i : numberFieldMixedRealCoordinateIndex K) : |v i| ≤ R := by
    have hi : ‖v i‖ ≤ ‖v‖ :=
      (pi_norm_le_iff_of_nonneg (norm_nonneg v)).1 le_rfl i
    exact le_trans (by simpa [Real.norm_eq_abs] using hi) hαR
  refine ⟨α, hα, ?_⟩
  intro w
  rcases InfinitePlace.isReal_or_isComplex w with hw | hw
  · let wr : {w : InfinitePlace K // w.IsReal} := ⟨w, hw⟩
    have hr := hcoord (Sum.inl wr)
    change |Real.exp (-y w) *
      InfinitePlace.embedding_of_isReal hw (α : K)| ≤ R at hr
    have hplace : w (α : K) =
        |InfinitePlace.embedding_of_isReal hw (α : K)| := by
      calc
        w (α : K) = (InfinitePlace.mk w.embedding) (α : K) :=
          congrArg (fun q : InfinitePlace K => q (α : K))
            (InfinitePlace.mk_embedding w).symm
        _ = ‖w.embedding (α : K)‖ := rfl
        _ = ‖(InfinitePlace.embedding_of_isReal hw (α : K) : ℂ)‖ := by
          symm
          rw [InfinitePlace.embedding_of_isReal_apply]
        _ = |InfinitePlace.embedding_of_isReal hw (α : K)| := by
          rw [Complex.norm_real, Real.norm_eq_abs]
    rw [hplace]
    have hr' : Real.exp (-y w) *
        |InfinitePlace.embedding_of_isReal hw (α : K)| ≤ R := by
      simpa [abs_mul, abs_of_pos (Real.exp_pos _)] using hr
    calc
      |InfinitePlace.embedding_of_isReal hw (α : K)| =
          Real.exp (y w) *
            (Real.exp (-y w) * |InfinitePlace.embedding_of_isReal hw (α : K)|) := by
              rw [← mul_assoc, ← Real.exp_add]
              simp
      _ ≤ Real.exp (y w) * R :=
        mul_le_mul_of_nonneg_left hr' (Real.exp_nonneg _)
      _ ≤ (2 * R) * Real.exp (y w) := by
        nlinarith [Real.exp_pos (y w)]
  · let wc : {w : InfinitePlace K // w.IsComplex} := ⟨w, hw⟩
    have hre := hcoord (Sum.inr (wc, 0))
    have him := hcoord (Sum.inr (wc, 1))
    change |(Complex.ofReal (Real.exp (-y w)) * w.embedding (α : K)).re| ≤ R at hre
    change |(Complex.ofReal (Real.exp (-y w)) * w.embedding (α : K)).im| ≤ R at him
    let z : ℂ := Complex.ofReal (Real.exp (-y w)) * w.embedding (α : K)
    have hz : ‖z‖ ≤ 2 * R := by
      have hzrepr : z = (z.re : ℂ) + (z.im : ℂ) * Complex.I := by
        apply Complex.ext <;> simp
      calc
        ‖z‖ = ‖(z.re : ℂ) + (z.im : ℂ) * Complex.I‖ := by rw [← hzrepr]
        _ ≤ ‖(z.re : ℂ)‖ + ‖(z.im : ℂ) * Complex.I‖ := norm_add_le _ _
        _ = |z.re| + |z.im| := by simp [Real.norm_eq_abs]
        _ ≤ R + R := add_le_add hre him
        _ = 2 * R := by ring
    have hplaceNorm : w (α : K) = ‖w.embedding (α : K)‖ := by
      calc
        w (α : K) = (InfinitePlace.mk w.embedding) (α : K) :=
          congrArg (fun q : InfinitePlace K => q (α : K))
            (InfinitePlace.mk_embedding w).symm
        _ = ‖w.embedding (α : K)‖ := rfl
    rw [hplaceNorm]
    calc
      ‖w.embedding (α : K)‖ = Real.exp (y w) * ‖z‖ := by
        dsimp [z]
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (Real.exp_pos _), ← mul_assoc, ← Real.exp_add]
        simp
      _ ≤ Real.exp (y w) * (2 * R) :=
        mul_le_mul_of_nonneg_left hz (Real.exp_nonneg _)
      _ = (2 * R) * Real.exp (y w) := by ring

end

end GaloisForLFunctions.HTGeometry
