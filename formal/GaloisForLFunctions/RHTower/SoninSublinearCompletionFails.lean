import GaloisForLFunctions.RHTower.SoninLogCappedCompletionFails

/-!
# No sublinear completion restores the floor

The schedule's energy grows linearly in the scale, so the comparison that defeats a logarithmic cap
defeats any cap growing more slowly than the scale itself.  What the argument consumes is only that
the contribution divided by the scale tends to zero.

This is the widest class the linear rate reaches: a completion may grow, and grow without bound, and
still fail, provided it grows sublinearly.
-/

noncomputable section

set_option maxHeartbeats 1000000

namespace RHTower

open Filter ContinuousLinearMap
open scoped Topology

/-- **No sublinear completion restores the floor.** -/
theorem not_bddBelow_soninCompletedPacketValueVar_of_sublinear (N₀ : ℕ) (hN₀ : 1 ≤ N₀)
    (a b c q : ℝ) (hbc : b < c) (ha : 0 < a) (hab : a < b) (hb : 0 < b) (haq : a < q)
    (hqb : 2 * q ≤ b) (f : ℝ → ℝ)
    (hsub : Tendsto (fun r : ℝ => f r / r) atTop (𝓝 0)) :
    ∃ (κ : ℝ) (Nstart : ℕ) (hp : ∀ i : ℕ, 1 < soninShellCutScale b c (Nstart + i) κ),
      ¬ ∃ M : ℝ, ∀ s : Finset ℕ,
        M ≤ soninCompletedPacketValueVar s a b c
          (fun i => soninShellCutScale b c (Nstart + i) κ) hp
          (fun i => f (soninShellCutScale b c (Nstart + i) κ)) := by
  obtain ⟨κ, Nstart, hp, hκ, hcp, henergy⟩ :=
    exists_scale_sequence_of_schedule N₀ hN₀ a b c q hbc ha hab.le hb haq hqb
  refine ⟨κ, Nstart, hp, ?_⟩
  set Dis : ℝ := 2 * hsNormSq (evenSoninProjectionCorrection b) +
    hsNormSq (evenSoninProjectionCorrection a - evenSoninProjectionCorrection b) with hDis
  set slope : ℝ := (c - b) / (8 * κ) with hslope
  have hslopepos : 0 < slope := by
    have : (0 : ℝ) < c - b := by linarith
    rw [hslope]
    positivity
  have hadd : Tendsto (fun i : ℕ => Nstart + i) atTop atTop := by
    simpa [Nat.add_comm] using tendsto_add_atTop_nat Nstart
  have hdiv : Tendsto (fun i : ℕ => soninShellCutScale b c (Nstart + i) κ) atTop atTop :=
    (tendsto_soninShellCutScale_atTop b c hbc hκ).comp hadd
  have hshort : ∀ᶠ i : ℕ in atTop,
      f (soninShellCutScale b c (Nstart + i) κ) + 1 ≤
        hsNormSq (evenSoninApertureSuccessiveLayerTransition a b c
          (soninShellCutScale b c (Nstart + i) κ) (hp i)) := by
    filter_upwards [hdiv.eventually
      (GaloisForLFunctions.HTGeometry.eventually_sublinear_add_le_linear hslopepos hsub
        (36 * Dis) 1)] with i hi
    have hlin : ((Nstart + i : ℕ) : ℝ) / 4 =
        slope * soninShellCutScale b c (Nstart + i) κ := by
      have hmul := soninShellCutScale_mul_slope b c hbc
        (show 0 < Nstart + i by
          rcases Nat.eq_zero_or_pos (Nstart + i) with h0 | hpos
          · exfalso
            have h1 := hp i
            rw [h0, soninShellCutScale] at h1
            norm_num at h1
          · exact hpos) hκ
      rw [hslope]
      calc ((Nstart + i : ℕ) : ℝ) / 4
          = ((c - b) / (2 * κ) * soninShellCutScale b c (Nstart + i) κ) / 4 := by rw [hmul]
        _ = (c - b) / (8 * κ) * soninShellCutScale b c (Nstart + i) κ := by ring
    have hE := henergy i
    rw [hlin] at hE
    linarith [hi, hE]
  exact not_bddBelow_soninCompletedPacketValueVar_of_shortfall ha hab hbc
    (fun i => soninShellCutScale b c (Nstart + i) κ) hp hcp
    (fun i => f (soninShellCutScale b c (Nstart + i) κ)) 1 one_pos hshort

end RHTower
