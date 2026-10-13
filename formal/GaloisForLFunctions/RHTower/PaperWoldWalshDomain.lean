import GaloisForLFunctions.RHTower.PaperWoldPhaseColumn
import GaloisForLFunctions.RHTower.PaperWoldWalshFullOperator
import GaloisForLFunctions.RHTower.PaperWoldBoundedDomain

/-! # Exact unit-phase compact-admission domain of the full Wold matrix

Walsh signs construct a compact realization below three quarters. Every
unit-modulus mask is excluded at and above that boundary by column energy.
-/

namespace RHTower
noncomputable section
open Filter Topology GaloisForLFunctions GaloisForLFunctions.HTGeometry

theorem paperWoldPhaseRealization_not_compact (t : {t : ℝ // 3 / 4 ≤ t})
    (u : PaperWoldUnitPhase) (T : PaperWoldPhaseRealization t u) : ¬ IsCompactOperator T.val := by
  intro hT
  have hi : Tendsto (fun n : ℕ => 4 * (n + 1) + 2) atTop atTop :=
    tendsto_atTop_mono (fun n => by change n ≤ 4 * (n + 1) + 2; omega) tendsto_id
  have hz := tendsto_norm_compact_of_weaklyNull T.val hT
    (fun n => lp.single 2 (4 * (n + 1) + 2) (1 : ℂ))
    (fun n => by rw [lp.norm_single (by norm_num : (0 : ENNReal) < 2), norm_one])
    (fun z => (tendsto_inner_lp_single z).comp hi)
  have hsq : Tendsto (fun n => ‖T.val (lp.single 2 (4 * (n + 1) + 2) 1)‖ ^ 2) atTop (𝓝 0) := by
    simpa only [norm_zero, zero_pow (by omega : 2 ≠ 0)] using hz.norm.pow 2
  have hbad : (1 / 2304 : ℝ) ≤ 0 := ge_of_tendsto hsq
    (Eventually.of_forall fun n => paperWoldPhase_column_energy_floor t u T (n + 1) (by omega))
  norm_num at hbad

/-- Strictly above three quarters, no unit-phase mask even admits a bounded operator. -/
theorem paperWoldPhaseRealization_not_nonempty (t : {t : ℝ // 3 / 4 < t})
    (u : PaperWoldUnitPhase) : ¬ Nonempty (PaperWoldPhaseRealization t u) := by
  rintro ⟨T⟩
  have hg : Tendsto (fun N : ℕ => (N : ℝ) ^ (4 * t.val - 3) / 2304) atTop atTop :=
    ((tendsto_rpow_atTop (by linarith [t.property] : 0 < 4 * t.val - 3)).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))).atTop_div_const (by norm_num)
  obtain ⟨N, hN, hlarge⟩ := ((eventually_ge_atTop 1).and
    (hg.eventually (eventually_gt_atTop (‖T.val‖ ^ 2)))).exists
  have hl := paperWoldPhase_column_energy_lower ⟨t.val, t.property.le⟩ u T N hN
  have hb : ‖T.val (lp.single 2 (4 * N + 2) 1)‖ ≤ ‖T.val‖ := by
    simpa only [lp.norm_single (by norm_num : (0 : ENNReal) < 2), norm_one, mul_one] using
      T.val.le_opNorm (lp.single 2 (4 * N + 2) 1)
  exact (not_lt_of_ge (hl.trans (pow_le_pow_left₀ (norm_nonneg _) hb 2))) hlarge

def paperWoldWalshFullRealization (t : {t : ℝ // t < 3 / 4}) :
    PaperWoldPhaseRealization t paperWoldFullWalshPhase :=
  ⟨paperWoldWalshFullOperator t, fun n j => paperWoldWalshFullOperator_single t n j⟩

/-- One fixed sign pattern attains the entire compact-admission interval. -/
theorem paperWoldWalsh_exists_compact_realization_iff (t : ℝ) :
    (∃ T : PaperWoldPhaseRealization t paperWoldFullWalshPhase, IsCompactOperator T.val) ↔
      t < 3 / 4 := by
  constructor
  · rintro ⟨T, hT⟩
    by_contra ht
    exact paperWoldPhaseRealization_not_compact ⟨t, le_of_not_gt ht⟩ _ T hT
  · intro ht
    exact ⟨paperWoldWalshFullRealization ⟨t, ht⟩, paperWoldWalshFullOperator_compact ⟨t, ht⟩⟩

/-- Allowing arbitrary unit phases cannot enlarge the Walsh compact-admission interval. -/
theorem paperWold_exists_phase_compact_realization_iff (t : ℝ) :
    (∃ (u : PaperWoldUnitPhase) (T : PaperWoldPhaseRealization t u), IsCompactOperator T.val) ↔
      t < 3 / 4 := by
  constructor
  · rintro ⟨u, T, hT⟩
    by_contra ht
    exact paperWoldPhaseRealization_not_compact ⟨t, le_of_not_gt ht⟩ u T hT
  · intro ht
    exact ⟨paperWoldFullWalshPhase, (paperWoldWalsh_exists_compact_realization_iff t).mpr ht⟩

/-- Signs alone turn an unadmitted full matrix into an actual compact, non-HS operator. -/
theorem paperWoldWalshBand_admission_change (t : PaperWoldWalshBand) :
    ¬ Nonempty (PaperWoldRealization t.val) ∧
      IsCompactOperator (paperWoldWalshFullOperator ⟨t.val, t.property.2⟩) ∧
        ¬ (paperWoldWalshFullOperator ⟨t.val, t.property.2⟩).IsHilbertSchmidt :=
  ⟨paperWoldRealization_not_nonempty ⟨t.val, t.property.1⟩,
    paperWoldWalshFullOperator_compact _, paperWoldWalshFullOperator_not_hilbertSchmidt t⟩

end
end RHTower
