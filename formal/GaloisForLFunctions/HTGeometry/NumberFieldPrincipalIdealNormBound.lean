import GaloisForLFunctions.HTGeometry.AlgebraicIntegerSeparation
import GaloisForLFunctions.HTGeometry.NumberFieldIntegerMinkowskiReduction

/-!
# Archimedean bounds imply principal-ideal norm bounds

The multiplicity-weighted place sum is exactly the sum over complex embeddings.  Consequently a
weighted-zero exponential place bound controls the integral field norm, hence the absolute norm of
the corresponding principal ideal.
-/

namespace GaloisForLFunctions.HTGeometry

open NumberField NumberField.InfinitePlace
open scoped Classical NumberField

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

/-- Sum over complex embeddings, grouped by their infinite places. -/
theorem numberFieldEmbeddingMkSum_eq_placeSum (f : InfinitePlace K → ℝ) :
    ∑ σ : K →+* ℂ, f (InfinitePlace.mk σ) =
      ∑ w : InfinitePlace K, (mult w : ℝ) * f w := by
  classical
  have hmaps : ∀ σ ∈ (Finset.univ : Finset (K →+* ℂ)),
      (InfinitePlace.mk σ) ∈ (Finset.univ : Finset (InfinitePlace K)) :=
    fun _ _ => Finset.mem_univ _
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  refine Finset.sum_congr rfl fun w _ => ?_
  have hconst : ∀ σ ∈ Finset.univ.filter
      (fun σ : K →+* ℂ => InfinitePlace.mk σ = w),
      f (InfinitePlace.mk σ) = f w := by
    intro σ hσ
    rw [(Finset.mem_filter.mp hσ).2]
  rw [Finset.sum_congr rfl hconst, Finset.sum_const,
    InfinitePlace.card_filter_mk_eq, nsmul_eq_mul]

/-- Integral norm magnitude is the product of all complex-embedding magnitudes. -/
theorem cast_natAbs_algebraNorm_eq_prod_norm_embeddings (α : 𝓞 K) :
    ((Algebra.norm ℤ α).natAbs : ℝ) = ∏ σ : K →+* ℂ, ‖σ (α : K)‖ := by
  classical
  have hcast : ((Algebra.norm ℤ α : ℤ) : ℚ) = Algebra.norm ℚ (α : K) :=
    Algebra.coe_norm_int α
  have hprod : (algebraMap ℚ ℂ) (Algebra.norm ℚ (α : K)) =
      ∏ σ : K →+* ℂ, σ (α : K) := by
    have h := Algebra.norm_eq_prod_embeddings (L := K) ℚ ℂ (α : K)
    refine h.trans ?_
    exact Fintype.prod_equiv
      (RingHom.equivRatAlgHom (R := K) (S := ℂ)).symm _ _ fun σ => rfl
  have hnormprod : ‖(algebraMap ℚ ℂ) (Algebra.norm ℚ (α : K))‖ =
      ∏ σ : K →+* ℂ, ‖σ (α : K)‖ := by
    rw [hprod, norm_prod]
  have hcast2 : (algebraMap ℚ ℂ) (Algebra.norm ℚ (α : K)) =
      ((Algebra.norm ℤ α : ℤ) : ℂ) := by
    rw [← hcast]
    simp
  rw [← hnormprod, hcast2, Complex.norm_intCast]
  generalize Algebra.norm ℤ α = z
  cases z with
  | ofNat n => simp
  | negSucc n =>
      have hneg : ((Int.negSucc n : ℤ) : ℝ) = -(n : ℝ) - 1 := by
        norm_num
        ring
      have hnonpos : ((Int.negSucc n : ℤ) : ℝ) ≤ 0 := by
        rw [hneg]
        have hn : (0 : ℝ) ≤ n := by positivity
        linarith
      rw [abs_of_nonpos hnonpos]
      norm_num

/-- A weighted-zero place bound gives a natural-number bound for the principal ideal norm. -/
theorem absNorm_span_singleton_le_ceil_of_placeValue_le
    (α : 𝓞 K) {C : ℝ} (y : InfinitePlace K → ℝ)
    (hy : ∑ w : InfinitePlace K, (mult w : ℝ) * y w = 0)
    (hα : ∀ w : InfinitePlace K, w (α : K) ≤ C * Real.exp (y w)) :
    Ideal.absNorm (Ideal.span {α}) ≤
      ⌈C ^ Fintype.card (K →+* ℂ)⌉₊ := by
  have hemb (σ : K →+* ℂ) : ‖σ (α : K)‖ ≤
      C * Real.exp (y (InfinitePlace.mk σ)) := hα (InfinitePlace.mk σ)
  have hprod : (∏ σ : K →+* ℂ, ‖σ (α : K)‖) ≤
      C ^ Fintype.card (K →+* ℂ) := by
    calc
      (∏ σ : K →+* ℂ, ‖σ (α : K)‖) ≤
          ∏ σ : K →+* ℂ, (C * Real.exp (y (InfinitePlace.mk σ))) := by
            exact Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun σ _ => hemb σ
      _ = C ^ Fintype.card (K →+* ℂ) := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, ← Real.exp_sum,
          numberFieldEmbeddingMkSum_eq_placeSum, hy, Real.exp_zero, mul_one]
  have hreal : (Ideal.absNorm (Ideal.span {α}) : ℝ) ≤
      C ^ Fintype.card (K →+* ℂ) := by
    rw [Ideal.absNorm_span_singleton,
      cast_natAbs_algebraNorm_eq_prod_norm_embeddings]
    exact hprod
  exact_mod_cast le_trans hreal (Nat.le_ceil _)

end

end GaloisForLFunctions.HTGeometry
