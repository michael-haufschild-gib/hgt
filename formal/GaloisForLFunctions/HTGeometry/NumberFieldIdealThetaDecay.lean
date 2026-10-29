import GaloisForLFunctions.HTGeometry.NumberFieldScaledIdealTheta
import GaloisForLFunctions.HTGeometry.LatticeSubsetLinearEquivMinimum

/-!
# Uniform exponential decay of fractional-ideal theta tails

A nonzero ideal has a positive minimum among its nonzero weighted embedding
norms. Upper bounds on the logarithmic place profile preserve a uniform positive
multiple of each squared norm. Splitting the Gaussian exponent leaves a fixed
summable majorant and an exponentially decaying factor. Removing the zero ideal
element therefore gives a uniform exponential bound for the theta tail.
-/

noncomputable section
open NumberField NumberField.InfinitePlace Module
open scoped Classical NumberField

namespace GaloisForLFunctions.HTGeometry
variable {K : Type*} [Field K] [NumberField K]
local notation "ι" => numberFieldMixedRealCoordinateIndex K
local notation "X" => ι → ℝ
local notation "E" => EuclideanSpace ℝ ι
local notation "FI" => FractionalIdeal (nonZeroDivisors (𝓞 K)) K

/-- A nonzero ideal has a positive lower bound for every nonzero weighted embedding norm. -/
theorem exists_positive_ideal_traceNorm_lower_bound (I : FIˣ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ a : K, a ∈ (I : Set K) → a ≠ 0 →
      δ ≤ ‖numberFieldTraceCoordinates (mixedEmbedding K a)‖ := by
  let L := numberFieldTraceLattice I
  let S : Set X := {x | x ∈ L ∧ x ≠ 0}
  let e : X ≃L[ℝ] E := (WithLp.linearEquiv 2 ℝ X).symm.toContinuousLinearEquiv
  have hS : S.Nonempty := by
    let b := numberFieldTraceLatticeBasis I
    let j := ((b.indexEquiv (Pi.basisFun ℝ ι)).symm (Classical.choice inferInstance))
    refine ⟨b j, ?_, b.ne_zero j⟩
    change b j ∈ numberFieldTraceLattice I
    rw [← span_numberFieldTraceLatticeBasis]
    exact Submodule.subset_span ⟨j, rfl⟩
  obtain ⟨v, hv, hmin⟩ := exists_minimal_image_norm_mem_of_nonempty_subset
    L S hS (fun _ hx => hx.1) e
  have hvpos : 0 < ‖e v‖ := by
    apply norm_pos_iff.mpr
    intro he
    exact hv.2 (e.injective (he.trans e.map_zero.symm))
  refine ⟨‖e v‖, hvpos, ?_⟩
  intro a ha hane
  have hx : numberFieldTraceRealCoordinates (mixedEmbedding K a) ∈ S := by
    refine ⟨(mem_numberFieldTraceLattice I).mpr ⟨a, ha, rfl⟩, ?_⟩
    intro hz
    apply hane
    apply NumberField.mixedEmbedding_injective K
    apply (numberFieldTraceRealCoordinates (K := K)).injective
    simpa only [map_zero] using hz
  exact hmin _ hx

/-- An upper bound on every profile coordinate gives a uniform lower bound on the scaled norm. -/
theorem norm_sq_placeScale_ge (M : ℝ) (y : InfinitePlace K → ℝ)
    (hy : ∀ w, y w ≤ M) (z : mixedEmbedding.mixedSpace K) :
    Real.exp (-M) ^ 2 * ‖numberFieldTraceCoordinates z‖ ^ 2 ≤
      ‖numberFieldTraceCoordinates (numberFieldMixedPlaceScale y z)‖ ^ 2 := by
  rw [norm_sq_numberFieldTraceCoordinates, norm_sq_numberFieldTraceCoordinates, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro w _
  rw [normAtPlace_numberFieldMixedPlaceScale]
  have hn := mixedEmbedding.normAtPlace_nonneg w z
  have he := Real.exp_le_exp.mpr (neg_le_neg (hy w))
  calc
    _ = (mult w : ℝ) * (Real.exp (-M) * mixedEmbedding.normAtPlace w z) ^ 2 := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (mul_nonneg (Real.exp_pos _).le hn)
        (mul_le_mul_of_nonneg_right he hn) 2) (Nat.cast_nonneg _)

private theorem gaussian_tail_factor_bound {q d r R t : ℝ}
    (hq : 0 ≤ q) (hr : 0 ≤ r) (hd : d ≤ r) (hR : q * r ≤ R) (ht : 1 ≤ t) :
    Real.exp (-(Real.pi * t) * R) ≤
      Real.exp (-(Real.pi * q * d / 2) * t) * Real.exp (-(Real.pi * (q / 2)) * r) := by
  have ht0 : 0 ≤ t := le_trans zero_le_one ht
  have h1 := mul_le_mul_of_nonneg_left ht (mul_nonneg hq hr)
  have h2 := mul_le_mul_of_nonneg_left hd (mul_nonneg ht0 hq)
  have h3 := mul_le_mul_of_nonneg_left hR ht0
  have hsplit : (q / 2) * r + (q * d / 2) * t ≤ t * R := by
    nlinarith only [h1, h2, h3]
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith only [mul_le_mul_of_nonneg_left hsplit Real.pi_pos.le]

/-- Removing the zero ideal element removes exactly the constant theta term. -/
theorem numberFieldScaledIdealTheta_sub_one_eq (I : FIˣ) (y : InfinitePlace K → ℝ)
    {t : ℝ} (ht : 0 < t) :
    numberFieldScaledIdealTheta (I : FI) y t - 1 =
      ∑' a : (I : FI), if (a : K) = 0 then 0 else Real.exp (-(Real.pi * t) *
        ‖numberFieldTraceCoordinates (numberFieldMixedPlaceScale y (mixedEmbedding K (a : K)))‖ ^ 2) := by
  let z : (I : FI) := ⟨0, (I : FI).zero_mem⟩
  have h := (summable_numberFieldScaledIdealTheta I y ht).tsum_eq_add_tsum_ite z
  have hz : Real.exp (-(Real.pi * t) * ‖numberFieldTraceCoordinates
      (numberFieldMixedPlaceScale y (mixedEmbedding K (z : K)))‖ ^ 2) = 1 := by
    change Real.exp (-(Real.pi * t) * ‖numberFieldTraceCoordinates
      (numberFieldMixedPlaceScale y (mixedEmbedding K 0))‖ ^ 2) = 1
    simp only [map_zero, norm_zero, zero_pow (by norm_num : 2 ≠ 0),
      mul_zero, Real.exp_zero]
  rw [hz] at h
  simp only [Subtype.ext_iff] at h
  exact sub_eq_iff_eq_add.mpr (h.trans (add_comm _ _))

/-- Ideal theta tails decay exponentially, uniformly over all upper-bounded place profiles. -/
theorem exists_uniform_exponential_numberFieldIdealTheta_tail (I : FIˣ) (M : ℝ) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ y : InfinitePlace K → ℝ, (∀ w, y w ≤ M) →
      ∀ t : ℝ, 1 ≤ t → 0 ≤ numberFieldScaledIdealTheta (I : FI) y t - 1 ∧
        numberFieldScaledIdealTheta (I : FI) y t - 1 ≤ C * Real.exp (-c * t) := by
  obtain ⟨δ, hδ, hmin⟩ := exists_positive_ideal_traceNorm_lower_bound I
  let q := Real.exp (-M) ^ 2
  have hq : 0 < q := sq_pos_of_pos (Real.exp_pos _)
  have hqhalf : 0 < q / 2 := half_pos hq
  have hs := summable_numberFieldIdealTheta I hqhalf
  have htheta : 0 ≤ numberFieldIdealTheta (I : FI) (q / 2) :=
    tsum_nonneg (fun _ => (Real.exp_pos _).le)
  refine ⟨numberFieldIdealTheta (I : FI) (q / 2) + 1,
    Real.pi * q * δ ^ 2 / 2, add_pos_of_nonneg_of_pos htheta zero_lt_one,
    div_pos (mul_pos (mul_pos Real.pi_pos hq) (sq_pos_of_pos hδ)) (by norm_num), ?_⟩
  intro y hy t ht
  have htpos : 0 < t := lt_of_lt_of_le zero_lt_one ht
  rw [numberFieldScaledIdealTheta_sub_one_eq I y htpos]
  have hnonneg (a : (I : FI)) : 0 ≤ if (a : K) = 0 then 0 else Real.exp (-(Real.pi * t) *
      ‖numberFieldTraceCoordinates (numberFieldMixedPlaceScale y (mixedEmbedding K (a : K)))‖ ^ 2) := by
    split_ifs
    · exact le_rfl
    · exact (Real.exp_pos _).le
  have hbound (a : (I : FI)) :
      (if (a : K) = 0 then 0 else Real.exp (-(Real.pi * t) *
        ‖numberFieldTraceCoordinates (numberFieldMixedPlaceScale y (mixedEmbedding K (a : K)))‖ ^ 2)) ≤
      Real.exp (-(Real.pi * q * δ ^ 2 / 2) * t) *
        Real.exp (-(Real.pi * (q / 2)) * ‖numberFieldTraceCoordinates (mixedEmbedding K (a : K))‖ ^ 2) := by
    split_ifs with ha
    · exact (mul_pos (Real.exp_pos _) (Real.exp_pos _)).le
    · exact gaussian_tail_factor_bound hq.le (sq_nonneg _)
        (pow_le_pow_left₀ hδ.le (hmin a a.property ha) 2)
        (norm_sq_placeScale_ge M y hy (mixedEmbedding K (a : K))) ht
  have hmajor := hs.mul_left (Real.exp (-(Real.pi * q * δ ^ 2 / 2) * t))
  have htail := Summable.of_nonneg_of_le hnonneg hbound hmajor
  refine ⟨tsum_nonneg hnonneg, ?_⟩
  calc
    _ ≤ ∑' a : (I : FI), Real.exp (-(Real.pi * q * δ ^ 2 / 2) * t) *
        Real.exp (-(Real.pi * (q / 2)) * ‖numberFieldTraceCoordinates (mixedEmbedding K (a : K))‖ ^ 2) :=
      htail.tsum_le_tsum hbound hmajor
    _ = Real.exp (-(Real.pi * q * δ ^ 2 / 2) * t) *
        numberFieldIdealTheta (I : FI) (q / 2) := tsum_mul_left
    _ ≤ (numberFieldIdealTheta (I : FI) (q / 2) + 1) *
        Real.exp (-(Real.pi * q * δ ^ 2 / 2) * t) := by
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) (Real.exp_pos _).le

end GaloisForLFunctions.HTGeometry
