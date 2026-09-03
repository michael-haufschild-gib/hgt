import GaloisForLFunctions.HTGeometry.NumberFieldIdealClassRepresentatives
import GaloisForLFunctions.HTGeometry.NumberFieldIntegerMinkowskiReduction

/-!
# Uniform Minkowski reduction for ideal-class representatives

Choose one nonzero member of each fixed fractional-ideal representative.  Multiplication by that
member transports the standard integer Minkowski lattice into the representative ideal.  Applying
the determinant-one lattice theorem to these transported lattices and taking a finite sum over the
class group gives one radius valid for every ideal class and every weighted-zero archimedean
profile.
-/

namespace GaloisForLFunctions.HTGeometry

open NumberField NumberField.InfinitePlace
open scoped Classical NumberField

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

private theorem numberFieldIdealClassRepresentative_ne_bot
    (c : ClassGroup (𝓞 K)) :
    (↑(↑(numberFieldIdealClassRepresentative K c) :
      FractionalIdeal (nonZeroDivisors (𝓞 K)) K) : Submodule (𝓞 K) K) ≠ ⊥ := by
  intro hbot
  have hzero : (↑(numberFieldIdealClassRepresentative K c) :
      FractionalIdeal (nonZeroDivisors (𝓞 K)) K) = 0 :=
    FractionalIdeal.coeToSubmodule_eq_bot.mp hbot
  exact Units.ne_zero (numberFieldIdealClassRepresentative K c) hzero

/-- A fixed nonzero field element in the fractional ideal representing an ideal class. -/
def numberFieldIdealClassRepresentativeMember (c : ClassGroup (𝓞 K)) : K :=
  Classical.choose (Submodule.exists_mem_ne_zero_of_ne_bot
    (numberFieldIdealClassRepresentative_ne_bot (K := K) c))

/-- The fixed representative member lies in its fractional ideal. -/
theorem numberFieldIdealClassRepresentativeMember_mem (c : ClassGroup (𝓞 K)) :
    numberFieldIdealClassRepresentativeMember (K := K) c ∈
      (↑(numberFieldIdealClassRepresentative K c) :
        FractionalIdeal (nonZeroDivisors (𝓞 K)) K) :=
  (Classical.choose_spec (Submodule.exists_mem_ne_zero_of_ne_bot
    (numberFieldIdealClassRepresentative_ne_bot (K := K) c))).1

/-- The fixed representative member is nonzero. -/
theorem numberFieldIdealClassRepresentativeMember_ne_zero (c : ClassGroup (𝓞 K)) :
    numberFieldIdealClassRepresentativeMember (K := K) c ≠ 0 :=
  (Classical.choose_spec (Submodule.exists_mem_ne_zero_of_ne_bot
    (numberFieldIdealClassRepresentative_ne_bot (K := K) c))).2

/-- Multiplication by a nonzero field element on mixed Minkowski space. -/
def numberFieldMixedMulEquiv (a : K) (ha : a ≠ 0) :
    mixedEmbedding.mixedSpace K ≃ₗ[ℝ] mixedEmbedding.mixedSpace K where
  toFun z := mixedEmbedding K a * z
  invFun z := mixedEmbedding K a⁻¹ * z
  left_inv z := by
    change mixedEmbedding K a⁻¹ * (mixedEmbedding K a * z) = z
    rw [← mul_assoc, ← map_mul]
    simp [ha]
  right_inv z := by
    change mixedEmbedding K a * (mixedEmbedding K a⁻¹ * z) = z
    rw [← mul_assoc, ← map_mul]
    simp [ha]
  map_add' z z' := by simp [mul_add]
  map_smul' c z := by
    apply Prod.ext <;> funext w
    · simp [mul_comm]
    · change (mixedEmbedding K a).2 w * (Complex.ofReal c * z.2 w) =
        Complex.ofReal c * ((mixedEmbedding K a).2 w * z.2 w)
      ring

omit [NumberField K] in
@[simp]
theorem numberFieldMixedMulEquiv_apply_mixedEmbedding (a b : K) (ha : a ≠ 0) :
    numberFieldMixedMulEquiv a ha (mixedEmbedding K b) = mixedEmbedding K (a * b) := by
  simp [numberFieldMixedMulEquiv]

/-- Multiplying the fixed representative member by an algebraic integer stays in the
representative fractional ideal. -/
theorem numberFieldIdealClassRepresentativeMember_mul_mem
    (c : ClassGroup (𝓞 K)) (α : 𝓞 K) :
    numberFieldIdealClassRepresentativeMember (K := K) c * (α : K) ∈
      (↑(numberFieldIdealClassRepresentative K c) :
        FractionalIdeal (nonZeroDivisors (𝓞 K)) K) := by
  rw [mul_comm]
  change (α : 𝓞 K) • numberFieldIdealClassRepresentativeMember (K := K) c ∈
    (↑(↑(numberFieldIdealClassRepresentative K c) :
      FractionalIdeal (nonZeroDivisors (𝓞 K)) K) : Submodule (𝓞 K) K)
  exact Submodule.smul_mem _ _ (numberFieldIdealClassRepresentativeMember_mem c)

/-- One determinant-one Minkowski radius works for a fixed ideal-class representative. -/
theorem exists_numberFieldIdealClassRepresentative_scaled_realCoordinates_norm_le
    (c : ClassGroup (𝓞 K)) :
    ∃ R : ℝ, 0 < R ∧ ∀ y : InfinitePlace K → ℝ,
      (∑ w : InfinitePlace K, (mult w : ℝ) * y w = 0) →
        ∃ β : K, β ∈
            (↑(numberFieldIdealClassRepresentative K c) :
              FractionalIdeal (nonZeroDivisors (𝓞 K)) K) ∧
          β ≠ 0 ∧
          ‖numberFieldMixedRealCoordinates
            (numberFieldMixedPlaceScale y (mixedEmbedding K β))‖ ≤ R := by
  let a := numberFieldIdealClassRepresentativeMember (K := K) c
  have ha : a ≠ 0 := numberFieldIdealClassRepresentativeMember_ne_zero c
  let e := numberFieldMixedRealCoordinates (K := K)
  let m := numberFieldMixedMulEquiv a ha
  let b := (mixedEmbedding.latticeBasis K).map (m.trans e)
  obtain ⟨R, hR, hRall⟩ :=
    exists_uniform_ne_zero_zspan_positiveDiagonal_norm_le b
  refine ⟨R, hR, ?_⟩
  intro y hy
  let s := numberFieldMixedCoordinateScale y
  have hs : ∀ i, 0 < s i := numberFieldMixedCoordinateScale_pos y
  have hprod : ∏ i, s i = 1 := prod_numberFieldMixedCoordinateScale y hy
  obtain ⟨x, hx, hx0, hxR⟩ := hRall s hs hprod
  have hxMap : x ∈ Submodule.map
      ((m.trans e).restrictScalars ℤ : mixedEmbedding.mixedSpace K →ₗ[ℤ]
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
  refine ⟨a * (α : K), numberFieldIdealClassRepresentativeMember_mul_mem c α,
    mul_ne_zero ha ?_, ?_⟩
  · exact_mod_cast hα
  · calc
      ‖numberFieldMixedRealCoordinates
          (numberFieldMixedPlaceScale y (mixedEmbedding K (a * (α : K))))‖ =
          ‖positiveDiagonalLinearEquiv s hs
            (numberFieldMixedRealCoordinates (mixedEmbedding K (a * (α : K))))‖ := by
        congr 1
        rw [numberFieldMixedRealCoordinates_placeScale,
          positiveDiagonalLinearEquiv_apply]
      _ = ‖positiveDiagonalLinearEquiv s hs x‖ := by
        congr 2
        simpa [m, e] using hzx
      _ ≤ R := hxR

/-- **Finite ideal-class Minkowski reduction.**  A single radius works simultaneously for every
fixed ideal-class representative and every weighted-zero archimedean profile. -/
theorem exists_uniform_numberFieldIdealClassRepresentative_scaled_realCoordinates_norm_le :
    ∃ R : ℝ, 0 < R ∧ ∀ (c : ClassGroup (𝓞 K)) (y : InfinitePlace K → ℝ),
      (∑ w : InfinitePlace K, (mult w : ℝ) * y w = 0) →
        ∃ β : K, β ∈
            (↑(numberFieldIdealClassRepresentative K c) :
              FractionalIdeal (nonZeroDivisors (𝓞 K)) K) ∧
          β ≠ 0 ∧
          ‖numberFieldMixedRealCoordinates
            (numberFieldMixedPlaceScale y (mixedEmbedding K β))‖ ≤ R := by
  choose radius hradius_pos hradius using
    fun c : ClassGroup (𝓞 K) =>
      exists_numberFieldIdealClassRepresentative_scaled_realCoordinates_norm_le (K := K) c
  let R := ∑ c : ClassGroup (𝓞 K), radius c
  have hR : 0 < R := by
    dsimp [R]
    exact Finset.sum_pos (fun c _ => hradius_pos c) Finset.univ_nonempty
  refine ⟨R, hR, ?_⟩
  intro c y hy
  obtain ⟨β, hβmem, hβ0, hβbound⟩ := hradius c y hy
  refine ⟨β, hβmem, hβ0, le_trans hβbound ?_⟩
  dsimp [R]
  exact Finset.single_le_sum (fun i _ => (hradius_pos i).le) (Finset.mem_univ c)

private theorem numberField_placeValue_le_two_mul_of_scaled_realCoordinates_norm_le
    (y : InfinitePlace K → ℝ) (β : K) (R : ℝ) (hR : 0 ≤ R)
    (hβR : ‖numberFieldMixedRealCoordinates
      (numberFieldMixedPlaceScale y (mixedEmbedding K β))‖ ≤ R) :
    ∀ w : InfinitePlace K, w β ≤ (2 * R) * Real.exp (y w) := by
  let v := numberFieldMixedRealCoordinates
    (numberFieldMixedPlaceScale y (mixedEmbedding K β))
  have hcoord (i : numberFieldMixedRealCoordinateIndex K) : |v i| ≤ R := by
    have hi : ‖v i‖ ≤ ‖v‖ :=
      (pi_norm_le_iff_of_nonneg (norm_nonneg v)).1 le_rfl i
    exact le_trans (by simpa [Real.norm_eq_abs] using hi) hβR
  intro w
  rcases InfinitePlace.isReal_or_isComplex w with hw | hw
  · let wr : {w : InfinitePlace K // w.IsReal} := ⟨w, hw⟩
    have hr := hcoord (Sum.inl wr)
    change |Real.exp (-y w) * InfinitePlace.embedding_of_isReal hw β| ≤ R at hr
    have hplace : w β = |InfinitePlace.embedding_of_isReal hw β| := by
      calc
        w β = (InfinitePlace.mk w.embedding) β :=
          congrArg (fun q : InfinitePlace K => q β)
            (InfinitePlace.mk_embedding w).symm
        _ = ‖w.embedding β‖ := rfl
        _ = ‖(InfinitePlace.embedding_of_isReal hw β : ℂ)‖ := by
          symm
          rw [InfinitePlace.embedding_of_isReal_apply]
        _ = |InfinitePlace.embedding_of_isReal hw β| := by
          rw [Complex.norm_real, Real.norm_eq_abs]
    rw [hplace]
    have hr' : Real.exp (-y w) *
        |InfinitePlace.embedding_of_isReal hw β| ≤ R := by
      simpa [abs_mul, abs_of_pos (Real.exp_pos _)] using hr
    calc
      |InfinitePlace.embedding_of_isReal hw β| =
          Real.exp (y w) *
            (Real.exp (-y w) * |InfinitePlace.embedding_of_isReal hw β|) := by
              rw [← mul_assoc, ← Real.exp_add]
              simp
      _ ≤ Real.exp (y w) * R :=
        mul_le_mul_of_nonneg_left hr' (Real.exp_nonneg _)
      _ ≤ (2 * R) * Real.exp (y w) := by
        nlinarith [Real.exp_pos (y w)]
  · let wc : {w : InfinitePlace K // w.IsComplex} := ⟨w, hw⟩
    have hre := hcoord (Sum.inr (wc, 0))
    have him := hcoord (Sum.inr (wc, 1))
    change |(Complex.ofReal (Real.exp (-y w)) * w.embedding β).re| ≤ R at hre
    change |(Complex.ofReal (Real.exp (-y w)) * w.embedding β).im| ≤ R at him
    let z : ℂ := Complex.ofReal (Real.exp (-y w)) * w.embedding β
    have hz : ‖z‖ ≤ 2 * R := by
      have hzrepr : z = (z.re : ℂ) + (z.im : ℂ) * Complex.I := by
        apply Complex.ext <;> simp
      calc
        ‖z‖ = ‖(z.re : ℂ) + (z.im : ℂ) * Complex.I‖ := by rw [← hzrepr]
        _ ≤ ‖(z.re : ℂ)‖ + ‖(z.im : ℂ) * Complex.I‖ := norm_add_le _ _
        _ = |z.re| + |z.im| := by simp [Real.norm_eq_abs]
        _ ≤ R + R := add_le_add hre him
        _ = 2 * R := by ring
    have hplaceNorm : w β = ‖w.embedding β‖ := by
      calc
        w β = (InfinitePlace.mk w.embedding) β :=
          congrArg (fun q : InfinitePlace K => q β)
            (InfinitePlace.mk_embedding w).symm
        _ = ‖w.embedding β‖ := rfl
    rw [hplaceNorm]
    calc
      ‖w.embedding β‖ = Real.exp (y w) * ‖z‖ := by
        dsimp [z]
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (Real.exp_pos _), ← mul_assoc, ← Real.exp_add]
        simp
      _ ≤ Real.exp (y w) * (2 * R) :=
        mul_le_mul_of_nonneg_left hz (Real.exp_nonneg _)
      _ = (2 * R) * Real.exp (y w) := by ring

/-- Uniform place-value form of finite ideal-class Minkowski reduction. -/
theorem exists_uniform_numberFieldIdealClassRepresentative_placeValue_le :
    ∃ C : ℝ, 0 < C ∧ ∀ (c : ClassGroup (𝓞 K)) (y : InfinitePlace K → ℝ),
      (∑ w : InfinitePlace K, (mult w : ℝ) * y w = 0) →
        ∃ β : K, β ∈
            (↑(numberFieldIdealClassRepresentative K c) :
              FractionalIdeal (nonZeroDivisors (𝓞 K)) K) ∧
          β ≠ 0 ∧ ∀ w : InfinitePlace K,
            w β ≤ C * Real.exp (y w) := by
  obtain ⟨R, hR, hbound⟩ :=
    exists_uniform_numberFieldIdealClassRepresentative_scaled_realCoordinates_norm_le (K := K)
  refine ⟨2 * R, by positivity, ?_⟩
  intro c y hy
  obtain ⟨β, hβmem, hβ0, hβR⟩ := hbound c y hy
  exact ⟨β, hβmem, hβ0,
    numberField_placeValue_le_two_mul_of_scaled_realCoordinates_norm_le
      y β R hR.le hβR⟩

end

end GaloisForLFunctions.HTGeometry
