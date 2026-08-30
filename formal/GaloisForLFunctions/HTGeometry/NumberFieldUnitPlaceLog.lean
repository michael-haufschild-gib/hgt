import GaloisForLFunctions.HTGeometry.NumberFieldUnitLogProduct
import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic

/-!
# Weighted archimedean place logarithms of number-ring units

Complex embeddings occur in conjugate pairs, so Dirichlet reduction lives on archimedean places,
with multiplicity one at real places and two at complex places.  This module derives the weighted
product formula and the exact weighted zero-sum hyperplane from the already closed embedding
product formula.
-/

namespace GaloisForLFunctions.HTGeometry

open NumberField NumberField.InfinitePlace
open scoped Classical NumberField

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

/-- A sum over complex embeddings is the corresponding multiplicity-weighted place sum. -/
theorem numberFieldEmbeddingSum_eq_placeSum (F : ℝ → ℝ) (x : K) :
    ∑ σ : K →+* ℂ, F ‖σ x‖ =
      ∑ w : InfinitePlace K, (mult w : ℝ) * F (w x) := by
  classical
  have hmaps : ∀ σ ∈ (Finset.univ : Finset (K →+* ℂ)),
      (mk σ) ∈ (Finset.univ : Finset (InfinitePlace K)) :=
    fun _ _ => Finset.mem_univ _
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  refine Finset.sum_congr rfl fun w _ => ?_
  have hconst : ∀ σ ∈ Finset.univ.filter (fun σ : K →+* ℂ => mk σ = w),
      F ‖σ x‖ = F (w x) := by
    intro σ hσ
    rw [← (Finset.mem_filter.mp hσ).2]
    rfl
  rw [Finset.sum_congr rfl hconst, Finset.sum_const, card_filter_mk_eq, nsmul_eq_mul]

/-- Logarithmic modulus of a number-ring unit at each archimedean place. -/
def numberFieldUnitPlaceLogEmbeddings (u : (𝓞 K)ˣ) : InfinitePlace K → ℝ :=
  fun w => Real.log (w (((u : 𝓞 K) : K)))

omit [NumberField K] in
private theorem numberFieldUnit_placeValue_pos (u : (𝓞 K)ˣ) (w : InfinitePlace K) :
    0 < w (((u : 𝓞 K) : K)) := by
  rw [InfinitePlace.pos_iff]
  norm_cast
  exact u.ne_zero

omit [NumberField K] in
theorem numberFieldUnitPlaceLogEmbeddings_mul (u v : (𝓞 K)ˣ) :
    numberFieldUnitPlaceLogEmbeddings (u * v) =
      numberFieldUnitPlaceLogEmbeddings u + numberFieldUnitPlaceLogEmbeddings v := by
  funext w
  rw [Pi.add_apply]
  simp only [numberFieldUnitPlaceLogEmbeddings, Units.val_mul]
  have huv : ((((u : 𝓞 K) * (v : 𝓞 K) : 𝓞 K) : K)) =
      (((u : 𝓞 K) : K)) * (((v : 𝓞 K) : K)) := by norm_cast
  rw [huv, map_mul, Real.log_mul]
  · exact ne_of_gt (numberFieldUnit_placeValue_pos u w)
  · exact ne_of_gt (numberFieldUnit_placeValue_pos v w)

/-- Weighted product formula for the archimedean place-log profile. -/
theorem sum_mult_numberFieldUnitPlaceLogEmbeddings (u : (𝓞 K)ˣ) :
    ∑ w : InfinitePlace K,
      (mult w : ℝ) * numberFieldUnitPlaceLogEmbeddings u w = 0 := by
  change (∑ w : InfinitePlace K,
    (mult w : ℝ) * Real.log (w (((u : 𝓞 K) : K)))) = 0
  rw [← numberFieldEmbeddingSum_eq_placeSum (F := Real.log)
    ((((u : 𝓞 K) : K)))]
  exact sum_numberFieldUnitLogEmbeddings u

/-- Place-log profile as an additive homomorphism. -/
def numberFieldUnitPlaceLog : Additive (𝓞 K)ˣ →+ (InfinitePlace K → ℝ) where
  toFun u := numberFieldUnitPlaceLogEmbeddings (Additive.toMul u)
  map_zero' := by
    funext w
    simp [numberFieldUnitPlaceLogEmbeddings]
  map_add' u v :=
    numberFieldUnitPlaceLogEmbeddings_mul (Additive.toMul u) (Additive.toMul v)

/-- Weighted zero-sum archimedean hyperplane. -/
def numberFieldUnitPlaceLogHyperplane : Submodule ℝ (InfinitePlace K → ℝ) where
  carrier := {x | ∑ w, (mult w : ℝ) * x w = 0}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    change ∑ w, (mult w : ℝ) * (x w + y w) = 0
    simp_rw [mul_add]
    rw [Finset.sum_add_distrib, hx, hy, add_zero]
  smul_mem' := by
    intro c x hx
    change ∑ w, (mult w : ℝ) * (c * x w) = 0
    simp_rw [← mul_assoc, mul_comm (mult _ : ℝ) c, mul_assoc]
    rw [← Finset.mul_sum, hx, mul_zero]

@[simp]
theorem mem_numberFieldUnitPlaceLogHyperplane_iff (x : InfinitePlace K → ℝ) :
    x ∈ numberFieldUnitPlaceLogHyperplane (K := K) ↔
      ∑ w, (mult w : ℝ) * x w = 0 := Iff.rfl

theorem numberFieldUnitPlaceLog_mem_hyperplane (u : Additive (𝓞 K)ˣ) :
    numberFieldUnitPlaceLog u ∈ numberFieldUnitPlaceLogHyperplane (K := K) :=
  sum_mult_numberFieldUnitPlaceLogEmbeddings (Additive.toMul u)

theorem range_numberFieldUnitPlaceLog_le_hyperplane :
    (numberFieldUnitPlaceLog (K := K)).range ≤
      (numberFieldUnitPlaceLogHyperplane (K := K)).toAddSubgroup := by
  rintro x ⟨u, rfl⟩
  exact numberFieldUnitPlaceLog_mem_hyperplane u

end

end GaloisForLFunctions.HTGeometry
