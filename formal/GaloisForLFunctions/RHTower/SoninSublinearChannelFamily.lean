import GaloisForLFunctions.RHTower.SoninLinearThresholdCompletionFails
import GaloisForLFunctions.RHTower.SoninChannelCutIndex

/-!
# A channel family of sublinear size is excluded

The failure of a sublinear completion needs only that the contribution be *dominated* by a sublinear
function of the scale, not equal to one.  Isolating the schedule's eventual shortfall makes that
explicit, and the dominated form is what an operator family supplies: the pairing of a vector with a
channel's image is at most the vector's norm times the image's, so a family whose images grow
sublinearly in the scale contributes a dominated sequence.

This covers channels that are unbounded — the operator norms may grow without limit — provided they
grow more slowly than the scale.
-/

noncomputable section

set_option maxHeartbeats 1000000

namespace RHTower

open Filter ContinuousLinearMap
open scoped Topology InnerProduct InnerProductSpace

/-- **The schedule's eventual shortfall against a sublinear cap.**  For one product and all fine
enough cuts, the energy exceeds the cap at the scale by more than one. -/
theorem exists_schedule_eventually_sublinear_add_le_hsNormSq (N₀ : ℕ) (hN₀ : 1 ≤ N₀)
    (a b c q : ℝ) (hbc : b < c) (ha : 0 < a) (hab : a ≤ b) (hb : 0 < b) (haq : a < q)
    (hqb : 2 * q ≤ b) (f : ℝ → ℝ) (hsub : Tendsto (fun r : ℝ => f r / r) atTop (𝓝 0)) :
    ∃ (κ : ℝ) (Nstart : ℕ) (hp : ∀ i : ℕ, 1 < soninShellCutScale b c (Nstart + i) κ),
      (∀ i : ℕ, c < soninShellCutScale b c (Nstart + i) κ * a) ∧
        ∀ᶠ i : ℕ in atTop, f (soninShellCutScale b c (Nstart + i) κ) + 1 ≤
          hsNormSq (evenSoninApertureSuccessiveLayerTransition a b c
            (soninShellCutScale b c (Nstart + i) κ) (hp i)) := by
  obtain ⟨κ, Nstart, hp, hκ, hcp, henergy⟩ :=
    exists_scale_sequence_of_schedule N₀ hN₀ a b c q hbc ha hab hb haq hqb
  refine ⟨κ, Nstart, hp, hcp, ?_⟩
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

/-- **No completion dominated by a sublinear cap restores the floor.**  The contribution need only
stay below a sublinear function of the scale. -/
theorem not_bddBelow_soninCompletedPacketValueVar_of_sublinear_dominated (N₀ : ℕ) (hN₀ : 1 ≤ N₀)
    (a b c q : ℝ) (hbc : b < c) (ha : 0 < a) (hab : a < b) (hb : 0 < b) (haq : a < q)
    (hqb : 2 * q ≤ b) (f : ℝ → ℝ) (hsub : Tendsto (fun r : ℝ => f r / r) atTop (𝓝 0)) :
    ∃ (κ : ℝ) (Nstart : ℕ) (hp : ∀ i : ℕ, 1 < soninShellCutScale b c (Nstart + i) κ),
      ∀ g : ℕ → ℝ, (∀ i, g i ≤ f (soninShellCutScale b c (Nstart + i) κ)) →
        ¬ ∃ M : ℝ, ∀ s : Finset ℕ,
          M ≤ soninCompletedPacketValueVar s a b c
            (fun i => soninShellCutScale b c (Nstart + i) κ) hp g := by
  obtain ⟨κ, Nstart, hp, hcp, hshort⟩ :=
    exists_schedule_eventually_sublinear_add_le_hsNormSq N₀ hN₀ a b c q hbc ha hab.le hb haq hqb
      f hsub
  refine ⟨κ, Nstart, hp, fun g hg => ?_⟩
  refine not_bddBelow_soninCompletedPacketValueVar_of_shortfall ha hab hbc
    (fun i => soninShellCutScale b c (Nstart + i) κ) hp hcp g 1 one_pos ?_
  filter_upwards [hshort] with i hi
  exact le_trans (by linarith [hg i]) hi

/-- **A channel family of sublinear size is excluded.**  If the images of vectors of bounded norm
grow more slowly than the scale, the completion they assemble leaves the packet channel without a
floor — the channels themselves may be unbounded. -/
theorem not_bddBelow_soninCompletedPacketValueVar_of_sublinear_channel (N₀ : ℕ) (hN₀ : 1 ≤ N₀)
    (a b c q : ℝ) (hbc : b < c) (ha : 0 < a) (hab : a < b) (hb : 0 < b) (haq : a < q)
    (hqb : 2 * q ≤ b) (B : ℝ → ℝ) {W : ℝ} (hW : 0 ≤ W)
    (hsub : Tendsto (fun r : ℝ => B r / r) atTop (𝓝 0)) :
    ∃ (κ : ℝ) (Nstart : ℕ) (hp : ∀ i : ℕ, 1 < soninShellCutScale b c (Nstart + i) κ),
      ∀ (v : ℕ → evenSubspace) (C : ℕ → (evenSubspace →L[ℂ] evenSubspace)),
        (∀ i, ‖v i‖ ≤ W) →
        (∀ i, ‖C i (v i)‖ ≤ B (soninShellCutScale b c (Nstart + i) κ)) →
        ¬ ∃ M : ℝ, ∀ s : Finset ℕ,
          M ≤ soninCompletedPacketValueVar s a b c
            (fun i => soninShellCutScale b c (Nstart + i) κ) hp
            (fun i => (⟪v i, C i (v i)⟫_ℂ).re) := by
  have hscaled : Tendsto (fun r : ℝ => W * B r / r) atTop (𝓝 0) := by
    have h := hsub.const_mul W
    rw [mul_zero] at h
    exact h.congr fun r => by rw [mul_div_assoc]
  obtain ⟨κ, Nstart, hp, hmain⟩ :=
    not_bddBelow_soninCompletedPacketValueVar_of_sublinear_dominated N₀ hN₀ a b c q hbc ha hab hb
      haq hqb (fun r => W * B r) hscaled
  refine ⟨κ, Nstart, hp, fun v C hv hC => hmain _ fun i => ?_⟩
  have h1 : (⟪v i, C i (v i)⟫_ℂ).re ≤ ‖(⟪v i, C i (v i)⟫_ℂ)‖ := Complex.re_le_norm _
  have h2 : ‖(⟪v i, C i (v i)⟫_ℂ)‖ ≤ ‖v i‖ * ‖C i (v i)‖ := norm_inner_le_norm _ _
  have h3 : ‖v i‖ * ‖C i (v i)‖ ≤ W * B (soninShellCutScale b c (Nstart + i) κ) :=
    mul_le_mul (hv i) (hC i) (norm_nonneg _) hW
  exact le_trans (le_trans h1 h2) h3

end RHTower

