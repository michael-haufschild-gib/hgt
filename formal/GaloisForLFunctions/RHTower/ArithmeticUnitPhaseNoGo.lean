import GaloisForLFunctions.RHTower.ArithmeticUnitPhaseRigidity
import GaloisForLFunctions.RHTower.HardyTheorem

/-!
# No global or finite-cover holomorphic arithmetic unit-phase factorization

Every connected phase chart contains at most one positive-height zero. The corpus's analytic
Hardy theorem supplies zeros above every height, excluding both a single multiplier on the
whole strip and a finite exhaustive cover by connected phase charts. The exact local and
zero-free positive survivors are formalized in `ArithmeticUnitPhaseRigidity`.
-/

open Complex Filter Set
open scoped Topology

namespace RHTower.DeletionMixedRefinement
noncomputable section

/-- Hardy's analytic corpus theorem supplies positive-height strip zeros above every height. -/
theorem exists_unitPhase_positive_zero_above (T : ℝ) :
    ∃ s : ℂ, s ∈ minimumStrip ∧ T < s.im ∧ 0 < s.im ∧ riemannZeta s = 0 := by
  obtain ⟨t, ht, hz⟩ := RHTower.exists_Xi_zero_gt (max T 0)
  let s : ℂ := 1 / 2 + (t : ℂ) * Complex.I
  have hs : s ∈ minimumStrip := by norm_num [s, minimumStrip]
  have him : s.im = t := by simp [s]
  refine ⟨s, hs, ?_, ?_, ?_⟩
  · rw [him]; exact lt_of_le_of_lt (le_max_left _ _) ht
  · rw [him]; exact lt_of_le_of_lt (le_max_right _ _) ht
  · have hd := unitPhaseStrip_denominators hs
    have hxi : RHTower.xi s = 0 := by
      change RHTower.XiC (t : ℂ) = 0
      rw [RHTower.XiC_ofReal, hz, Complex.ofReal_zero]
    rw [RHTower.xi_eq_archFactor_mul_zeta hd.1 hd.2.1
      (Complex.Gammaℝ_ne_zero_of_re_pos hs.1)] at hxi
    exact (mul_eq_zero.mp hxi).resolve_left (RHTower.archFactor_ne_zero_strip hs)

/-- No finite family of connected holomorphic phase charts covers all positive strip zeros.
Empty domains are allowed through `IsPreconnected`. -/
theorem not_finite_unitPhaseIdentity_cover (n : ℕ) :
    ¬ ∃ (U : Fin n → Set ℂ) (H : Fin n → ℂ → ℂ),
      (∀ i, U i ⊆ minimumStrip ∧ IsOpen (U i) ∧ IsPreconnected (U i) ∧
        AnalyticOnNhd ℂ (H i) (U i) ∧ UnitPhaseIdentity (U i) (H i)) ∧
      (∀ s ∈ minimumStrip, 0 < s.im → riemannZeta s = 0 → ∃ i, s ∈ U i) := by
  rintro ⟨U, H, hcharts, hcover⟩
  let S : Set ℂ := ⋃ i, {s | s ∈ U i ∧ 0 < s.im ∧ riemannZeta s = 0}
  have hfinite : S.Finite := Set.finite_iUnion fun i => by
    by_cases hne : (U i).Nonempty
    · exact (unitPhaseIdentity_positive_zeros_subsingleton (hcharts i).1 (hcharts i).2.1
        ⟨hne, (hcharts i).2.2.1⟩ (hcharts i).2.2.2.1 (hcharts i).2.2.2.2).finite
    · have he : U i = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
      simp [he]
  obtain ⟨b, hb⟩ := (hfinite.image Complex.im).bddAbove
  obtain ⟨s, hs, hgt, ht, hz⟩ := exists_unitPhase_positive_zero_above b
  obtain ⟨i, hi⟩ := hcover s hs ht hz
  have hin : s ∈ S := Set.mem_iUnion.mpr ⟨i, hi, ht, hz⟩
  have hle := hb ⟨s, hin, rfl⟩
  linarith

/-- The proposed single holomorphic multiplier on the entire strip does not exist. -/
theorem not_unitPhaseIdentity_strip :
    ¬ ∃ H : ℂ → ℂ, AnalyticOnNhd ℂ H minimumStrip ∧ UnitPhaseIdentity minimumStrip H := by
  rintro ⟨H, hH, hi⟩
  apply not_finite_unitPhaseIdentity_cover 1
  refine ⟨fun _ => minimumStrip, fun _ => H, ?_, ?_⟩
  · intro i
    exact ⟨Set.Subset.rfl, unitPhaseStrip_open, unitPhaseStrip_connected.isPreconnected, hH, hi⟩
  · intro s hs ht hz
    exact ⟨0, hs⟩

end
end RHTower.DeletionMixedRefinement
