import GaloisForLFunctions.HTGeometry.NumberFieldMixedRealCoordinates
import GaloisForLFunctions.HTGeometry.DeterminantOneLatticeShortVector
import Mathlib.RingTheory.Trace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Trace-compatible real coordinates for number fields

Complex embeddings occur in conjugate pairs. Regrouping their real parts by
infinite places expresses field trace as the sum of the real coordinates plus
twice the real parts of the complex coordinates. Splitting complex coordinates
and weighting each by `√2` turns this trace pairing into Euclidean inner product
after conjugating the second mixed vector.
-/

noncomputable section

open NumberField NumberField.InfinitePlace
open scoped Classical NumberField ComplexConjugate

namespace GaloisForLFunctions.HTGeometry

variable {K : Type*} [Field K] [NumberField K]

/-- Real parts of embedding values are constant on each infinite-place fiber. -/
theorem numberFieldEmbeddingReSum_eq_placeSum (x : K) :
    (∑ σ : K →+* ℂ, (σ x).re) =
      ∑ w : InfinitePlace K, (mult w : ℝ) * (w.embedding x).re := by
  classical
  have hmaps : ∀ σ ∈ (Finset.univ : Finset (K →+* ℂ)),
      mk σ ∈ (Finset.univ : Finset (InfinitePlace K)) :=
    fun _ _ => Finset.mem_univ _
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  refine Finset.sum_congr rfl fun w _ => ?_
  have hconst : ∀ σ ∈ Finset.univ.filter (fun σ : K →+* ℂ => mk σ = w),
      (σ x).re = (w.embedding x).re := by
    intro σ hσ
    rw [← (Finset.mem_filter.mp hσ).2]
    rcases embedding_mk_eq σ with h | h
    · rw [h]
    · rw [h, ComplexEmbedding.conjugate_coe_eq]
      simp only [Complex.conj_re]
  rw [Finset.sum_congr rfl hconst, Finset.sum_const, card_filter_mk_eq, nsmul_eq_mul]

/-- Field trace is the sum of real parts of its complex embedding values. -/
theorem numberField_trace_eq_embeddingReSum (x : K) :
    (Algebra.trace ℚ K x : ℝ) = ∑ σ : K →+* ℂ, (σ x).re := by
  have ht : (Algebra.trace ℚ K x : ℝ) = ∑ σ : K →ₐ[ℚ] ℂ, (σ x).re := by
    simpa using congrArg Complex.re
      (trace_eq_sum_embeddings ℂ (K := ℚ) (L := K) (x := x))
  rw [ht]
  let e : (K →+* ℂ) ≃ (K →ₐ[ℚ] ℂ) := RingHom.equivRatAlgHom
  exact (Fintype.sum_equiv e (fun σ => (σ x).re) (fun σ => (σ x).re)
    (fun _ => rfl)).symm

/-- Real places contribute once and complex places twice to field trace. -/
theorem numberField_trace_eq_placeSum (x : K) :
    (Algebra.trace ℚ K x : ℝ) =
      ∑ w : InfinitePlace K, (mult w : ℝ) * (w.embedding x).re := by
  rw [numberField_trace_eq_embeddingReSum, numberFieldEmbeddingReSum_eq_placeSum]

/-- A place sum splits into its real and complex contributions. -/
theorem sum_infinitePlaces_eq_real_add_complex (f : InfinitePlace K → ℝ) :
    (∑ w, f w) = (∑ w : {w : InfinitePlace K // w.IsReal}, f w) +
      ∑ w : {w : InfinitePlace K // w.IsComplex}, f w := by
  let e : {w : InfinitePlace K // ¬w.IsReal} ≃ {w : InfinitePlace K // w.IsComplex} :=
    { toFun w := ⟨w.1, not_isReal_iff_isComplex.mp w.2⟩
      invFun w := ⟨w.1, not_isReal_iff_isComplex.mpr w.2⟩
      left_inv _ := rfl
      right_inv _ := rfl }
  rw [← Fintype.sum_subtype_add_sum_subtype (fun w : InfinitePlace K => w.IsReal) f]
  congr 1
  exact Fintype.sum_equiv e (fun w => f w) (fun w => f w) (fun _ => rfl)

/-- The real-linear trace on mixed Minkowski space. -/
def numberFieldMixedTrace (z : mixedEmbedding.mixedSpace K) : ℝ :=
  (∑ w, z.1 w) + 2 * ∑ w, (z.2 w).re

/-- The mixed trace restricts to the number-field trace. -/
theorem numberFieldMixedTrace_embedding (x : K) :
    numberFieldMixedTrace (mixedEmbedding K x) = (Algebra.trace ℚ K x : ℝ) := by
  rw [numberField_trace_eq_placeSum, sum_infinitePlaces_eq_real_add_complex]
  simp only [numberFieldMixedTrace, mixedEmbedding.mixedEmbedding_apply_isReal,
    mixedEmbedding.mixedEmbedding_apply_isComplex]
  congr 1
  · apply Finset.sum_congr rfl
    intro w _
    rw [← embedding_of_isReal_apply w.2 x]
    simp only [mult, w.2, if_pos, Nat.cast_one, one_mul, Complex.ofReal_re]
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro w _
    simp only [mult, not_isReal_iff_isComplex.mpr w.2, if_false, Nat.cast_ofNat]

/-- Coordinatewise complex conjugation as a real linear equivalence. -/
def numberFieldMixedConjugation :
    mixedEmbedding.mixedSpace K ≃ₗ[ℝ] mixedEmbedding.mixedSpace K where
  toFun z := (z.1, fun w => conj (z.2 w))
  invFun z := (z.1, fun w => conj (z.2 w))
  left_inv z := by
    apply Prod.ext
    · rfl
    · funext w
      exact star_star _
  right_inv z := by
    apply Prod.ext
    · rfl
    · funext w
      exact star_star _
  map_add' z y := by
    apply Prod.ext
    · rfl
    · funext w
      exact map_add (starRingEnd ℂ) _ _
  map_smul' c z := by
    apply Prod.ext
    · rfl
    · funext w
      change conj ((c : ℂ) * z.2 w) = (c : ℂ) * conj (z.2 w)
      simp only [map_mul, Complex.conj_ofReal]

/-- Complex places receive `√2` in each of their two real coordinates. -/
def numberFieldMixedTraceWeight : numberFieldMixedRealCoordinateIndex K → ℝ
  | Sum.inl _ => 1
  | Sum.inr _ => Real.sqrt 2

omit [NumberField K] in
theorem numberFieldMixedTraceWeight_pos (i : numberFieldMixedRealCoordinateIndex K) :
    0 < numberFieldMixedTraceWeight i := by
  rcases i with w | w
  · exact zero_lt_one
  · exact Real.sqrt_pos.mpr (by norm_num)

/-- Trace-normalized Euclidean coordinates on mixed Minkowski space. -/
def numberFieldTraceCoordinates : mixedEmbedding.mixedSpace K ≃L[ℝ]
    EuclideanSpace ℝ (numberFieldMixedRealCoordinateIndex K) :=
  ((numberFieldMixedRealCoordinates.trans
    (positiveDiagonalLinearEquiv numberFieldMixedTraceWeight numberFieldMixedTraceWeight_pos)).trans
      (WithLp.linearEquiv 2 ℝ (numberFieldMixedRealCoordinateIndex K → ℝ)).symm).toContinuousLinearEquiv

theorem numberFieldTraceCoordinates_apply (z : mixedEmbedding.mixedSpace K) :
    numberFieldTraceCoordinates z = WithLp.toLp 2
      (fun i => numberFieldMixedTraceWeight i * numberFieldMixedRealCoordinates z i) := by
  change WithLp.toLp 2 (positiveDiagonalLinearEquiv numberFieldMixedTraceWeight
    numberFieldMixedTraceWeight_pos (numberFieldMixedRealCoordinates z)) = _
  rw [positiveDiagonalLinearEquiv_apply]

/-- Weighting each complex coordinate by `√2` turns conjugated inner product into trace. -/
theorem inner_numberFieldTraceCoordinates_conjugate (z y : mixedEmbedding.mixedSpace K) :
    inner ℝ (numberFieldTraceCoordinates z)
      (numberFieldTraceCoordinates (numberFieldMixedConjugation y)) =
        numberFieldMixedTrace (z * y) := by
  calc
    _ = ∑ i, numberFieldMixedTraceWeight i ^ 2 *
        (numberFieldMixedRealCoordinates z i *
          numberFieldMixedRealCoordinates (numberFieldMixedConjugation y) i) := by
      rw [numberFieldTraceCoordinates_apply, numberFieldTraceCoordinates_apply, PiLp.inner_apply]
      apply Finset.sum_congr rfl
      intro i _
      change inner ℝ
        (numberFieldMixedTraceWeight i * numberFieldMixedRealCoordinates z i)
        (numberFieldMixedTraceWeight i *
          numberFieldMixedRealCoordinates (numberFieldMixedConjugation y) i) = _
      rw [Real.inner_apply]
      ring
    _ = _ := by
      rw [Fintype.sum_sum_type, Fintype.sum_prod_type]
      unfold numberFieldMixedTrace
      rw [Finset.mul_sum]
      congr 1
      · apply Finset.sum_congr rfl
        intro w _
        change (1 : ℝ) ^ 2 * (z.1 w * y.1 w) = z.1 w * y.1 w
        ring
      · apply Finset.sum_congr rfl
        intro w _
        rw [Fin.sum_univ_two]
        change (Real.sqrt 2) ^ 2 * ((z.2 w).re * (conj (y.2 w)).re) +
          (Real.sqrt 2) ^ 2 * ((z.2 w).im * (conj (y.2 w)).im) =
            2 * (z.2 w * y.2 w).re
        simp only [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num),
          Complex.conj_re, Complex.conj_im, Complex.mul_re]
        ring

/-- Field trace is the conjugated Euclidean pairing of the weighted mixed embeddings. -/
theorem numberField_trace_eq_weighted_inner (a b : K) :
    inner ℝ (numberFieldTraceCoordinates (mixedEmbedding K a))
      (numberFieldTraceCoordinates (numberFieldMixedConjugation (mixedEmbedding K b))) =
        (Algebra.trace ℚ K (a * b) : ℝ) := by
  rw [inner_numberFieldTraceCoordinates_conjugate, ← map_mul, numberFieldMixedTrace_embedding]

end GaloisForLFunctions.HTGeometry
