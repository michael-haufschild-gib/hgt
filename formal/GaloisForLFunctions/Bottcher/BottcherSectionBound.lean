/-
# The section far-field upper norm bound

The mixed-tower norm bound (`two_lt_norm_of_reach_thresh`, task B8) needs the section image confined
to `(‖c‖+4, T)`.  The lower bound is the `exists_tower_anchor` export `Rinj < ‖S.T w‖` (`Rinj = R`);
the upper bound comes from the quantitative `φ_c(z) ≈ z` asymptotic
`norm_bottcherCoord_sub_id_le : ‖bottcherCoord c z − z‖ ≤ 4‖c‖/‖z‖` (`PolyAsymptotic`), so a far
preimage (`φ_c w' = w`) has `‖w'‖ < ‖w‖ + 1`.

* `norm_preimage_lt_of_bottcher` — the section far-field upper bound `‖w'‖ < ‖w‖ + 1`.

Axiom-clean.
-/
import GaloisForLFunctions.Bottcher.PolyAsymptotic

namespace Bottcher

/-- **Section far-field upper bound.**  A far Böttcher preimage (`φ_c w' = w`, `‖w'‖ > max 2 ‖c‖`,
`4‖c‖ < ‖w'‖`) satisfies `‖w'‖ < ‖w‖ + 1` — the section upper bound `hsec_hi` of
`two_lt_norm_of_reach_thresh`, combining with `‖w‖ < R₀` and `R₀ + 1 ≤ T` to give `‖S.T w‖ < T`. -/
theorem norm_preimage_lt_of_bottcher {c w' w : ℂ} (heq : bottcherCoord c w' = w)
    (hz : max 2 ‖c‖ < ‖w'‖) (h4c : 4 * ‖c‖ < ‖w'‖) : ‖w'‖ < ‖w‖ + 1 := by
  have hcle : ‖c‖ ≤ ‖w'‖ := le_of_lt (lt_of_le_of_lt (le_max_right _ _) hz)
  have h2 : 2 < ‖w'‖ := lt_of_le_of_lt (le_max_left _ _) hz
  have hpos : (0 : ℝ) < ‖w'‖ := by linarith
  have hb := norm_bottcherCoord_sub_id_le hcle h2
  rw [heq] at hb
  have hdiv : 4 * ‖c‖ / ‖w'‖ < 1 := by rw [div_lt_one hpos]; exact h4c
  have hwsub : ‖w' - w‖ < 1 := by rw [norm_sub_rev]; linarith
  have := norm_sub_norm_le w' w
  linarith

end Bottcher
