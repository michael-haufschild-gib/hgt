import GaloisForLFunctions.RHTower.TraceNorm

/-!
# Approximation numbers under isometric zero extension

If `U : H → H` is a linear isometry, then `U T U†` is the zero extension of `T` from the
closed range of `U`.  This file proves directly from finite-rank approximation that this operation
preserves every approximation number.  Surjectivity of `U` is neither needed nor assumed.
-/

namespace RHTower

open ContinuousLinearMap

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
private theorem linearIsometry_toContinuousLinearMap_norm_le_one
    (U : H →ₗᵢ[ℂ] H) : ‖U.toContinuousLinearMap‖ ≤ 1 := by
  apply U.toContinuousLinearMap.opNorm_le_bound zero_le_one
  intro x
  change ‖U x‖ ≤ 1 * ‖x‖
  rw [U.norm_map, one_mul]

private theorem adjoint_linearIsometry_toContinuousLinearMap_norm_le_one
    (U : H →ₗᵢ[ℂ] H) :
    ‖ContinuousLinearMap.adjoint U.toContinuousLinearMap‖ ≤ 1 := by
  rw [LinearIsometryEquiv.norm_map]
  exact linearIsometry_toContinuousLinearMap_norm_le_one U

/-- Compressing an isometric zero extension back to its source recovers the original operator. -/
theorem linearIsometry_adjoint_sandwich_eq
    (U : H →ₗᵢ[ℂ] H) (T : H →L[ℂ] H) :
    ContinuousLinearMap.adjoint U.toContinuousLinearMap ∘L
        ((U.toContinuousLinearMap ∘L T) ∘L
          ContinuousLinearMap.adjoint U.toContinuousLinearMap) ∘L
      U.toContinuousLinearMap = T := by
  apply ContinuousLinearMap.ext
  intro x
  have hcancel (y : H) :
      ContinuousLinearMap.adjoint U.toContinuousLinearMap
          (U.toContinuousLinearMap y) = y := by
    have h := DFunLike.congr_fun U.adjoint_comp_self y
    simpa only [ContinuousLinearMap.coe_comp, Function.comp_apply,
      one_apply_eq_self] using h
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply]
  rw [hcancel, hcancel]

/-- Isometric zero extension preserves every approximation number exactly. -/
theorem approxNumber_linearIsometry_adjoint_sandwich
    (U : H →ₗᵢ[ℂ] H) (T : H →L[ℂ] H) (n : ℕ) :
    approxNumber
        ((U.toContinuousLinearMap ∘L T) ∘L
          ContinuousLinearMap.adjoint U.toContinuousLinearMap) n =
      approxNumber T n := by
  let J := U.toContinuousLinearMap
  let A := ContinuousLinearMap.adjoint J
  let S := (J ∘L T) ∘L A
  have hJ : ‖J‖ ≤ 1 := linearIsometry_toContinuousLinearMap_norm_le_one U
  have hA : ‖A‖ ≤ 1 :=
    adjoint_linearIsometry_toContinuousLinearMap_norm_le_one U
  have hupper : approxNumber S n ≤ approxNumber T n := by
    calc
      approxNumber S n ≤ approxNumber (J ∘L T) n * ‖A‖ :=
        approxNumber_comp_le_right (J ∘L T) A n
      _ ≤ (‖J‖ * approxNumber T n) * ‖A‖ := by
        gcongr
        exact approxNumber_comp_le_left J T n
      _ ≤ approxNumber T n := by
        calc
          (‖J‖ * approxNumber T n) * ‖A‖ ≤
              (1 * approxNumber T n) * ‖A‖ := by
            gcongr
            exact approxNumber_nonneg T n
          _ ≤ (1 * approxNumber T n) * 1 := by
            gcongr
            simpa using approxNumber_nonneg T n
          _ = approxNumber T n := by ring
  have hlower : approxNumber T n ≤ approxNumber S n := by
    have heq : (A ∘L S) ∘L J = T := by
      apply ContinuousLinearMap.ext
      intro x
      have h := DFunLike.congr_fun (linearIsometry_adjoint_sandwich_eq U T) x
      simpa [A, S, J, ContinuousLinearMap.comp_apply] using h
    rw [← heq]
    calc
      approxNumber ((A ∘L S) ∘L J) n ≤
          approxNumber (A ∘L S) n * ‖J‖ :=
        approxNumber_comp_le_right (A ∘L S) J n
      _ ≤ (‖A‖ * approxNumber S n) * ‖J‖ := by
        gcongr
        exact approxNumber_comp_le_left A S n
      _ ≤ approxNumber S n := by
        calc
          (‖A‖ * approxNumber S n) * ‖J‖ ≤
              (1 * approxNumber S n) * ‖J‖ := by
            gcongr
            exact approxNumber_nonneg S n
          _ ≤ (1 * approxNumber S n) * 1 := by
            gcongr
            simpa using approxNumber_nonneg S n
          _ = approxNumber S n := by ring
  exact le_antisymm hupper hlower

end


end RHTower
