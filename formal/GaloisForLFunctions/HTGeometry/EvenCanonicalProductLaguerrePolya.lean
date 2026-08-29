import GaloisForLFunctions.HTGeometry.LaguerrePolyaClass
import GaloisForLFunctions.HTGeometry.MovingEvenCanonicalProduct

/-!
# The moving even canonical product is Laguerre–Pólya

Its partial products `∏_{n<N} (1 - X²/Λ_n(θ)²)` are real polynomials that split over `ℝ`, with
zeros `±Λ_n(θ)`, and the summability of `∑ Λ_n(θ)^{-2}` makes them converge locally uniformly to
the product.
-/

open Polynomial Filter Topology Complex

namespace GaloisForLFunctions.HTGeometry

noncomputable section

theorem tendstoLocallyUniformlyOn_comp_index {α β ι ι' : Type*} [TopologicalSpace α]
    [UniformSpace β] {p : Filter ι} {p' : Filter ι'} {F : ι → α → β} {f : α → β} {s : Set α}
    (h : TendstoLocallyUniformlyOn F f p s) {φ : ι' → ι} (hφ : Tendsto φ p' p) :
    TendstoLocallyUniformlyOn (fun m => F (φ m)) f p' s := by
  intro u hu x hx
  obtain ⟨t, ht, H⟩ := h u hu x hx
  exact ⟨t, ht, hφ.eventually H⟩

theorem splits_one_sub_C_mul_X (c : ℝ) : ((1 : ℝ[X]) - C c * X).Splits := by
  refine Polynomial.Splits.of_natDegree_le_one ?_
  refine le_trans (Polynomial.natDegree_sub_le _ _) (max_le (by simp) ?_)
  exact le_trans (Polynomial.natDegree_C_mul_le c X) (by simp)

theorem splits_one_add_C_mul_X (c : ℝ) : ((1 : ℝ[X]) + C c * X).Splits := by
  refine Polynomial.Splits.of_natDegree_le_one ?_
  refine le_trans (Polynomial.natDegree_add_le _ _) (max_le (by simp) ?_)
  exact le_trans (Polynomial.natDegree_C_mul_le c X) (by simp)

/-- The `N`-th partial product of the even canonical product, as a real polynomial. -/
def evenCanonicalPartial (θ : BoundedRealSequence) (N : ℕ) : ℝ[X] :=
  ∏ n ∈ Finset.range N,
    ((1 - C (movingCanonicalZero θ n)⁻¹ * X) * (1 + C (movingCanonicalZero θ n)⁻¹ * X))

theorem splits_evenCanonicalPartial (θ : BoundedRealSequence) (N : ℕ) :
    (evenCanonicalPartial θ N).Splits := by
  refine Finset.prod_induction _ _ (fun a b ha hb => ha.mul hb)
    (Polynomial.Splits.of_natDegree_le_one (by simp)) fun n _ => ?_
  exact (splits_one_sub_C_mul_X _).mul (splits_one_add_C_mul_X _)

theorem polyEvalC_evenCanonicalPartial (θ : BoundedRealSequence) (N : ℕ) (z : ℂ) :
    polyEvalC (evenCanonicalPartial θ N) z
      = ∏ n ∈ Finset.range N, (1 + (-(z ^ 2 / (movingCanonicalZero θ n : ℂ) ^ 2))) := by
  rw [polyEvalC, evenCanonicalPartial, map_prod]
  refine Finset.prod_congr rfl fun n _ => ?_
  have hne : ((movingCanonicalZero θ n : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (movingCanonicalZero_pos θ n))
  have hval : (aeval z) ((1 - C (movingCanonicalZero θ n)⁻¹ * X)
      * (1 + C (movingCanonicalZero θ n)⁻¹ * X))
      = (1 - (((movingCanonicalZero θ n)⁻¹ : ℝ) : ℂ) * z)
        * (1 + (((movingCanonicalZero θ n)⁻¹ : ℝ) : ℂ) * z) := by
    simp
  rw [hval]
  push_cast
  field_simp
  ring

theorem hasProdLocallyUniformlyOn_evenCanonical (θ : BoundedRealSequence) :
    HasProdLocallyUniformlyOn
      (fun n (z : ℂ) => 1 + (-(z ^ 2 / (movingCanonicalZero θ n : ℂ) ^ 2)))
      (movingEvenCanonicalProduct θ) Set.univ := by
  have hlim : (fun z : ℂ => ∏' n : ℕ, (1 + (-(z ^ 2 / (movingCanonicalZero θ n : ℂ) ^ 2))))
      = movingEvenCanonicalProduct θ := by
    funext z
    rw [movingEvenCanonicalProduct_eq_tprod]
    exact tprod_congr fun n => by ring
  rw [← hlim]
  refine hasProdLocallyUniformlyOn_of_forall_compact isOpen_univ ?_
  intro S _ hS
  obtain ⟨R, hRS⟩ := hS.isBounded.subset_closedBall 0
  have hR0 : (0 : ℝ) ≤ max R 0 := le_max_right _ _
  refine Summable.hasProdUniformlyOn_nat_one_add hS
    (u := fun n => (max R 0) ^ 2 * (1 / ‖(movingCanonicalZero θ n : ℂ)‖ ^ 2))
    ((summable_movingCanonicalZero_inv_sq θ).mul_left _) ?_ (fun n => by fun_prop)
  refine Filter.Eventually.of_forall fun n z hz => ?_
  have hzR : ‖z‖ ≤ max R 0 := by
    have := hRS hz
    rw [Metric.mem_closedBall, dist_zero_right] at this
    exact this.trans (le_max_left _ _)
  have hne : ((movingCanonicalZero θ n : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (movingCanonicalZero_pos θ n))
  rw [norm_neg, norm_div, norm_pow, norm_pow, div_eq_mul_inv, one_div]
  refine mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hzR 2) ?_
  positivity

/-- **The moving even canonical product lies in the Laguerre–Pólya class.** -/
theorem laguerrePolya_movingEvenCanonicalProduct (θ : BoundedRealSequence) :
    LaguerrePolya (movingEvenCanonicalProduct θ) := by
  refine ⟨evenCanonicalPartial θ, splits_evenCanonicalPartial θ, ?_⟩
  have h := hasProdLocallyUniformlyOn_evenCanonical θ
  rw [hasProdLocallyUniformlyOn_iff_tendstoLocallyUniformlyOn] at h
  have h2 := tendstoLocallyUniformlyOn_comp_index h (φ := Finset.range) tendsto_finset_range
  rw [tendstoLocallyUniformlyOn_univ] at h2
  have heq : (fun N => polyEvalC (evenCanonicalPartial θ N))
      = fun N (z : ℂ) =>
        ∏ n ∈ Finset.range N, (1 + (-(z ^ 2 / (movingCanonicalZero θ n : ℂ) ^ 2))) := by
    funext N z
    exact polyEvalC_evenCanonicalPartial θ N z
  rw [heq]
  exact h2

end

end GaloisForLFunctions.HTGeometry
