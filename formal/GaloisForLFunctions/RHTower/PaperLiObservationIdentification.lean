import GaloisForLFunctions.RHTower.PaperLiExactObservation
import GaloisForLFunctions.HTGeometry.LpObservationModulus

/-! # Exact negative-Li information in complete observations

Singleton observations recover each actual negative Li magnitude. Two budgets
have identical complete observations exactly when they agree or RH holds.
-/

namespace RHTower
noncomputable section
open GaloisForLFunctions.HTGeometry

theorem paperLiNegativeWeight_complex_norm (b : PaperLiBudget) (n : ℕ) :
    ‖(paperLiNegativeWeight b n : ℂ)‖ = paperLiNegativeWeight b n := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (paperLiNegativeWeight_nonneg b n)]

theorem paperLiNegative_singleObservation (b : PaperLiBudget) (n : ℕ) :
    lpSolidObservation (paperLiNegativeOperator b) (lp.single 2 n (1 : ℂ)) =
      paperLiNegativeWeight b n := by
  rw [lpSolidObservation_coordinate_single _ _ (paperLiNegativeOperator_apply b),
    paperLiNegativeWeight_complex_norm]

theorem paperLiNegativeMass_observation_reconstruct (b : PaperLiBudget) (n : ℕ) :
    paperLiNegativeMass n =
      b.val * lpSolidObservation (paperLiNegativeOperator b) (lp.single 2 n (1 : ℂ)) /
        (1 - lpSolidObservation (paperLiNegativeOperator b) (lp.single 2 n (1 : ℂ))) := by
  simp only [paperLiNegative_singleObservation]
  rw [eq_div_iff (sub_pos.mpr (paperLiNegativeWeight_lt_one b n)).ne']
  unfold paperLiNegativeWeight
  field_simp [(add_pos_of_nonneg_of_pos (paperLiNegativeMass_nonneg n) b.property).ne']
  ring

theorem paperLiNegativeWeight_budget_eq_iff (b c : PaperLiBudget) (n : ℕ) :
    paperLiNegativeWeight b n = paperLiNegativeWeight c n ↔
      b = c ∨ paperLiNegativeMass n = 0 := by
  constructor
  · intro h
    by_cases hm : paperLiNegativeMass n = 0
    · exact Or.inr hm
    · left
      apply Subtype.ext
      have he := (div_eq_div_iff
        (add_pos_of_nonneg_of_pos (paperLiNegativeMass_nonneg n) b.property).ne'
        (add_pos_of_nonneg_of_pos (paperLiNegativeMass_nonneg n) c.property).ne').mp h
      apply mul_left_cancel₀ hm
      nlinarith [he]
  · rintro (h | h)
    · rw [h]
    · simp only [paperLiNegativeWeight, h, zero_div]

theorem paperLiNegative_observations_eq_iff_weights (b c : PaperLiBudget) :
    (∀ x, lpSolidObservation (paperLiNegativeOperator b) x =
      lpSolidObservation (paperLiNegativeOperator c) x) ↔
        ∀ n, paperLiNegativeWeight b n = paperLiNegativeWeight c n := by
  simpa only [paperLiNegativeWeight_complex_norm] using
    forall_lpSolidObservation_eq_iff _ _ _ _
      (paperLiNegativeOperator_apply b) (paperLiNegativeOperator_apply c)

theorem paperLiNegative_observations_eq_iff_budget_or_rh (b c : PaperLiBudget) :
    (∀ x, lpSolidObservation (paperLiNegativeOperator b) x =
      lpSolidObservation (paperLiNegativeOperator c) x) ↔ b = c ∨ RiemannHypothesis := by
  classical
  constructor
  · intro h
    by_cases hbc : b = c
    · exact Or.inl hbc
    · right
      have hw := (paperLiNegative_observations_eq_iff_weights b c).mp h
      have hm : ∀ n, paperLiNegativeMass n = 0 := fun n =>
        ((paperLiNegativeWeight_budget_eq_iff b c n).mp (hw n)).resolve_left hbc
      have hz : paperLiNegativeOperator b = 0 := by
        ext x n
        simp [paperLiNegativeWeight, hm]
      apply (paperLiNegativeOperator_compact_iff b).mp
      rw [hz]
      exact isCompactOperator_zero
  · rintro (h | h)
    · rw [h]
      exact fun _ => rfl
    · intro x
      rw [paperLiNegativeOperator_of_RH h b, paperLiNegativeOperator_of_RH h c]

theorem paperLiNegativeOperator_eq_iff_budget_or_rh (b c : PaperLiBudget) :
    paperLiNegativeOperator b = paperLiNegativeOperator c ↔ b = c ∨ RiemannHypothesis := by
  constructor
  · intro h
    exact (paperLiNegative_observations_eq_iff_budget_or_rh b c).mp (fun x => by rw [h])
  · rintro (h | h)
    · rw [h]
    · rw [paperLiNegativeOperator_of_RH h b, paperLiNegativeOperator_of_RH h c]

end
end RHTower
