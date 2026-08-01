import GaloisForLFunctions.HTGeometry.LogBelowLinear
import GaloisForLFunctions.RHTower.SoninScheduleSequence
import GaloisForLFunctions.RHTower.SoninCompletionRateTest

/-!
# A logarithmically capped completion cannot restore the floor

Along the schedule the coupling's energy is a positive slope times the scale, less a constant, while
a completion capped by the logarithm of the scale contributes at most that logarithm.  A logarithm
falls short of every positive slope, so the contribution eventually trails the energy by a fixed
amount.

That is exactly the rate test's hypothesis, so no completion obeying such a cap gives the packet
channel a floor.
-/

noncomputable section

set_option maxHeartbeats 1000000

namespace RHTower

open Filter ContinuousLinearMap
open scoped Topology

/-- **No logarithmically capped completion restores the floor.**  For a completion whose
contribution at each scale is at most the logarithm of that scale, the schedule's sequence of scales
witnesses the failure. -/
theorem not_bddBelow_soninCompletedPacketValueVar_of_log_cap (N₀ : ℕ) (hN₀ : 1 ≤ N₀)
    (a b c q : ℝ) (hbc : b < c) (ha : 0 < a) (hab : a < b) (hb : 0 < b) (haq : a < q)
    (hqb : 2 * q ≤ b) (f : ℝ → ℝ) (hcap : ∀ r : ℝ, 1 < r → f r ≤ Real.log r) :
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
  -- the scale diverges along the sequence
  have hdiv : Tendsto (fun i : ℕ => soninShellCutScale b c (Nstart + i) κ) atTop atTop :=
    (tendsto_soninShellCutScale_atTop b c hbc hκ).comp (tendsto_add_atTop_nat Nstart)
  -- the cap trails the energy by one, eventually
  have hshort : ∀ᶠ i : ℕ in atTop,
      f (soninShellCutScale b c (Nstart + i) κ) + 1 ≤
        hsNormSq (evenSoninApertureSuccessiveLayerTransition a b c
          (soninShellCutScale b c (Nstart + i) κ) (hp i)) := by
    filter_upwards [hdiv.eventually
      (GaloisForLFunctions.HTGeometry.eventually_log_add_le_linear hslopepos (36 * Dis) 1)]
      with i hi
    have hN : 0 < Nstart + i ∨ True := Or.inr trivial
    have hlin : ((Nstart + i : ℕ) : ℝ) / 4 =
        slope * soninShellCutScale b c (Nstart + i) κ := by
      have hmul := soninShellCutScale_mul_slope b c hbc
        (show 0 < Nstart + i from by
          by_contra hcon
          push Not at hcon
          have : Nstart + i = 0 := Nat.le_zero.mp hcon
          have h1 := hp i
          rw [this] at h1
          rw [soninShellCutScale] at h1
          norm_num at h1
          nlinarith [h1, hκ, hbc]) hκ
      rw [hslope]
      calc ((Nstart + i : ℕ) : ℝ) / 4
          = ((c - b) / (2 * κ) * soninShellCutScale b c (Nstart + i) κ) / 4 := by rw [hmul]
        _ = (c - b) / (8 * κ) * soninShellCutScale b c (Nstart + i) κ := by ring
    have hE := henergy i
    rw [hlin] at hE
    have hcapi := hcap _ (hp i)
    linarith [hi, hE, hcapi]
  exact not_bddBelow_soninCompletedPacketValueVar_of_shortfall ha hab hbc
    (fun i => soninShellCutScale b c (Nstart + i) κ) hp hcp
    (fun i => f (soninShellCutScale b c (Nstart + i) κ)) 1 one_pos hshort

end RHTower
