import GaloisForLFunctions.HTGeometry.NumberFieldUnitPlaceLogFullRank

/-!
# Determinant-one tuples of number-field units with prescribed place logs

The one-unit covering theorem is upgraded to diagonal unit tuples whose product is exactly one.
All but one coordinate are reduced independently; the remaining coordinate is the inverse product.
The zero-sum target condition then bounds its error by the sum of the other errors.
-/

namespace GaloisForLFunctions.HTGeometry

open NumberField NumberField.InfinitePlace
open scoped Classical NumberField

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

omit [NumberField K] in
theorem numberFieldUnitPlaceLogEmbeddings_inv (u : (𝓞 K)ˣ) :
    numberFieldUnitPlaceLogEmbeddings u⁻¹ =
      -numberFieldUnitPlaceLogEmbeddings u := by
  have hmul := numberFieldUnitPlaceLogEmbeddings_mul u⁻¹ u
  have hzero : numberFieldUnitPlaceLogEmbeddings (u⁻¹ * u) = 0 := by
    funext w
    simp [numberFieldUnitPlaceLogEmbeddings]
  rw [hzero] at hmul
  exact eq_neg_of_add_eq_zero_left hmul.symm

omit [NumberField K] in
theorem numberFieldUnitPlaceLogEmbeddings_prod
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (u : ι → (𝓞 K)ˣ) :
    numberFieldUnitPlaceLogEmbeddings (∏ i ∈ s, u i) =
      ∑ i ∈ s, numberFieldUnitPlaceLogEmbeddings (u i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      funext w
      simp [numberFieldUnitPlaceLogEmbeddings]
  | @insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha,
        numberFieldUnitPlaceLogEmbeddings_mul, ih]

/-- A single radius approximates every zero-sum tuple of weighted-zero place profiles by unit
profiles whose units have product one. -/
theorem exists_numberFieldDetOneUnitPlaceLog_coveringRadius :
    ∃ R : ℝ, 0 < R ∧ ∀ (n : ℕ)
      (y : Fin (n + 1) → InfinitePlace K → ℝ),
      (∀ i, y i ∈ numberFieldUnitPlaceLogHyperplane (K := K)) →
      (∑ i, y i = 0) →
      ∃ u : Fin (n + 1) → (𝓞 K)ˣ,
        (∏ i, u i = 1) ∧
        ∀ i, ‖numberFieldUnitPlaceLogEmbeddings (u i) - y i‖ ≤
          (n + 1 : ℝ) * R := by
  obtain ⟨R, hR, hcover⟩ :=
    exists_numberFieldUnitPlaceLog_coveringRadius (K := K)
  refine ⟨R, hR, ?_⟩
  intro n y hy hysum
  choose v hv using fun i : Fin n => hcover (y i.succ) (hy i.succ)
  let u : Fin (n + 1) → (𝓞 K)ˣ := Fin.cons (∏ i, v i)⁻¹ v
  have hprod : ∏ i, u i = 1 := by
    rw [Fin.prod_univ_succ]
    simp [u]
  refine ⟨u, hprod, ?_⟩
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · have hyzero : y 0 = -∑ j : Fin n, y j.succ := by
      rw [Fin.sum_univ_succ] at hysum
      exact eq_neg_of_add_eq_zero_left hysum
    have hrewrite :
        numberFieldUnitPlaceLogEmbeddings (u 0) - y 0 =
          -∑ j : Fin n,
            (numberFieldUnitPlaceLogEmbeddings (v j) - y j.succ) := by
      rw [show u 0 = (∏ j, v j)⁻¹ by simp [u],
        numberFieldUnitPlaceLogEmbeddings_inv,
        numberFieldUnitPlaceLogEmbeddings_prod, hyzero]
      simp only [Finset.sum_sub_distrib]
      abel
    rw [hrewrite, norm_neg]
    calc
      ‖∑ j : Fin n, (numberFieldUnitPlaceLogEmbeddings (v j) - y j.succ)‖ ≤
          ∑ j : Fin n, ‖numberFieldUnitPlaceLogEmbeddings (v j) - y j.succ‖ := by
            simpa only [Finset.sum_const_zero, add_zero] using
              norm_sum_le Finset.univ
                (fun j : Fin n => numberFieldUnitPlaceLogEmbeddings (v j) - y j.succ)
      _ ≤ ∑ _j : Fin n, R := Finset.sum_le_sum fun j _ => hv j
      _ = (n : ℝ) * R := by simp
      _ ≤ (n + 1 : ℝ) * R := by
        exact mul_le_mul_of_nonneg_right (by norm_num) (le_of_lt hR)
  · rw [show u j.succ = v j by simp [u]]
    exact le_trans (hv j) (by
      calc
        R = 1 * R := (one_mul R).symm
        _ ≤ (n + 1 : ℝ) * R :=
          mul_le_mul_of_nonneg_right (by norm_num) (le_of_lt hR))

end

end GaloisForLFunctions.HTGeometry
