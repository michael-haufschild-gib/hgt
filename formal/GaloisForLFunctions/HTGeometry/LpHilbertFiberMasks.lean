import GaloisForLFunctions.HTGeometry.LpFiberMasks
import Mathlib.Analysis.InnerProductSpace.LinearMap

/-! # Full dominated Hilbert histories are exactly contraction masks

Rank-one contractions realize every allowed fiber value. Thus the attained
largest response of the full hull is attained by actual channel operators.
-/

namespace GaloisForLFunctions.HTGeometry
noncomputable section

theorem exists_hilbertContraction_apply_eq {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℂ F] {x y : F} (hy : ‖y‖ ≤ ‖x‖) :
    ∃ M : Metric.closedBall (0 : F →L[ℂ] F) 1, M.val x = y := by
  by_cases hx : x = 0
  · have hz : y = 0 := norm_le_zero_iff.mp (by simpa only [hx, norm_zero] using hy)
    exact ⟨⟨0, by simp⟩, by simp [hz]⟩
  · have hpos : 0 < ‖x‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hx)
    let T : F →L[ℂ] F := (((‖x‖ ^ 2 : ℝ) : ℂ)⁻¹) • InnerProductSpace.rankOne ℂ y x
    refine ⟨⟨T, ?_⟩, ?_⟩
    · rw [Metric.mem_closedBall, dist_zero_right]
      dsimp [T]
      rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg hpos.le, InnerProductSpace.norm_rankOne]
      calc
        (‖x‖ ^ 2)⁻¹ * (‖y‖ * ‖x‖) ≤ (‖x‖ ^ 2)⁻¹ * (‖x‖ * ‖x‖) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hy (norm_nonneg x))
            (inv_nonneg.mpr hpos.le)
        _ = 1 := by rw [← pow_two, inv_mul_cancel₀ hpos.ne']
    · change (((‖x‖ ^ 2 : ℝ) : ℂ)⁻¹) • (InnerProductSpace.rankOne ℂ y x x) = y
      rw [InnerProductSpace.rankOne_apply, inner_self_eq_norm_sq_to_K, smul_smul]
      change (((‖x‖ ^ 2 : ℝ) : ℂ)⁻¹ * (‖x‖ : ℂ) ^ 2) • y = y
      rw [← Complex.ofReal_pow, inv_mul_cancel₀ (by exact_mod_cast hpos.ne'), one_smul]

variable {I Y : Type*} {E : I → Type*} [∀ i, NormedAddCommGroup (E i)]
  [∀ i, InnerProductSpace ℂ (E i)] [NormedAddCommGroup Y] [NormedSpace ℂ Y]

theorem range_lpFiberMaskedHistory (x : lp E 2) :
    Set.range (lpFiberMaskedHistory x) = lpFiberSolidHull x := by
  classical
  ext y
  constructor
  · rintro ⟨m, rfl⟩
    exact lpFiberMaskedHistory_mem x m
  · intro hy
    choose m hm using fun i => exists_hilbertContraction_apply_eq (hy i)
    exact ⟨m, lp.ext (funext hm)⟩

theorem lpFiberObservation_mask_attained [∀ i, ProperSpace (E i)]
    (T : lp E 2 →L[ℂ] Y) (x : lp E 2) :
    ∃ m : LpFiberMask E, ‖T (lpFiberMaskedHistory x m)‖ = lpFiberObservation T x := by
  obtain ⟨y, hy, he⟩ := lpFiberObservation_attained T x
  rw [← range_lpFiberMaskedHistory] at hy
  obtain ⟨m, rfl⟩ := hy
  exact ⟨m, he⟩

end
end GaloisForLFunctions.HTGeometry
