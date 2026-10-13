import GaloisForLFunctions.RHTower.PaperWoldPrimePhaseColumn
import GaloisForLFunctions.RHTower.PaperWoldWalshDomain

/-! # Exact phase-admission boundary of the full arithmetic Wold matrix

One fixed Walsh sign pattern attains the entire possible bounded-admission
domain. Prime column energy excludes every unit phase at its endpoint.
-/

namespace RHTower
noncomputable section
open Filter Topology GaloisForLFunctions GaloisForLFunctions.HTGeometry

theorem paperWoldPhaseRealization_not_nonempty_of_threeQuarters_le
    (t : {t : ℝ // 3 / 4 ≤ t}) (u : PaperWoldUnitPhase) :
    ¬ Nonempty (PaperWoldPhaseRealization t u) := by
  rintro ⟨T⟩
  have hg : Tendsto (fun N : ℕ => Real.log N ^ 3 / (2 * 4096 ^ 2)) atTop atTop := by
    have hlog := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
    have hp := ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 3)).comp hlog).atTop_div_const
      (by norm_num : (0 : ℝ) < 2 * 4096 ^ 2)
    simpa only [Function.comp_def,
      show ∀ x : ℝ, x ^ (3 : ℝ) = x ^ 3 from fun x => Real.rpow_natCast x 3] using hp
  obtain ⟨N, hN, hlarge⟩ := ((paperWoldPhaseRealization_eventual_prime_norm_lower t u T).and
    (hg.eventually (eventually_gt_atTop (‖T.val‖ ^ 2)))).exists
  exact (not_lt_of_ge hN) hlarge

theorem paperWoldWalsh_exists_bounded_realization_iff (t : ℝ) :
    Nonempty (PaperWoldPhaseRealization t paperWoldFullWalshPhase) ↔ t < 3 / 4 := by
  constructor
  · intro h
    by_contra ht
    exact paperWoldPhaseRealization_not_nonempty_of_threeQuarters_le ⟨t, le_of_not_gt ht⟩ _ h
  · intro ht
    exact ⟨paperWoldWalshFullRealization ⟨t, ht⟩⟩

/-- No unit phases admit exponents outside the interval attained by the explicit Walsh signs. -/
theorem paperWold_exists_phase_bounded_realization_iff (t : ℝ) :
    (∃ u : PaperWoldUnitPhase, Nonempty (PaperWoldPhaseRealization t u)) ↔ t < 3 / 4 := by
  constructor
  · rintro ⟨u, h⟩
    by_contra ht
    exact paperWoldPhaseRealization_not_nonempty_of_threeQuarters_le ⟨t, le_of_not_gt ht⟩ u h
  · intro ht
    exact ⟨paperWoldFullWalshPhase, (paperWoldWalsh_exists_bounded_realization_iff t).mpr ht⟩

theorem paperWoldWalshRealization_compact (t : ℝ)
    (T : PaperWoldPhaseRealization t paperWoldFullWalshPhase) : IsCompactOperator T.val := by
  have ht := (paperWoldWalsh_exists_bounded_realization_iff t).mp ⟨T⟩
  have he : T.val = paperWoldWalshFullOperator ⟨t, ht⟩ :=
    HasLpMatrix.ext T.property (paperWoldWalshFullRealization ⟨t, ht⟩).property
  rw [he]
  exact paperWoldWalshFullOperator_compact _

theorem paperWoldWalshRealization_traceCost_zero (t : ℝ)
    (T : PaperWoldPhaseRealization t paperWoldFullWalshPhase) :
    compactOperatorTraceCost PaperWoldHistory T.val = 0 :=
  (compactOperatorTraceCost_eq_zero_iff _).mpr (paperWoldWalshRealization_compact t T)

end
end RHTower
