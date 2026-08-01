import GaloisForLFunctions.RHTower.SoninBoundedFamilyCompletionFails

/-!
# A definite slope below which every completion fails

The schedule's energy grows with a positive slope in the scale, so a completion is defeated not only
when its contribution is sublinear but whenever it stays below any fixed fraction of that slope.
Half the energy slope is such a threshold: the remaining half of the energy outruns the contribution
by more than a fixed amount at every large scale.

Read as a necessary condition on a surviving completion this is sharper than sublinearity: the
contribution must exceed a definite positive multiple of the scale infinitely often, not merely fail
to be small compared with it.
-/

noncomputable section

set_option maxHeartbeats 1000000

namespace RHTower

open Filter ContinuousLinearMap
open scoped Topology

/-- **A positive slope threshold.**  One schedule defeats every completion whose contribution stays
below a fixed positive multiple of the scale; the multiple is half the energy's own slope. -/
theorem exists_slope_not_bddBelow_soninCompletedPacketValueVar (N₀ : ℕ) (hN₀ : 1 ≤ N₀)
    (a b c q : ℝ) (hbc : b < c) (ha : 0 < a) (hab : a < b) (hb : 0 < b) (haq : a < q)
    (hqb : 2 * q ≤ b) :
    ∃ (s κ : ℝ) (Nstart : ℕ) (hp : ∀ i : ℕ, 1 < soninShellCutScale b c (Nstart + i) κ),
      0 < s ∧ ∀ f : ℝ → ℝ, (∀ᶠ r : ℝ in atTop, f r ≤ s * r) →
        ¬ ∃ M : ℝ, ∀ t : Finset ℕ,
          M ≤ soninCompletedPacketValueVar t a b c
            (fun i => soninShellCutScale b c (Nstart + i) κ) hp
            (fun i => f (soninShellCutScale b c (Nstart + i) κ)) := by
  obtain ⟨κ, Nstart, hp, hκ, hcp, henergy⟩ :=
    exists_scale_sequence_of_schedule N₀ hN₀ a b c q hbc ha hab.le hb haq hqb
  set Dis : ℝ := 2 * hsNormSq (evenSoninProjectionCorrection b) +
    hsNormSq (evenSoninProjectionCorrection a - evenSoninProjectionCorrection b) with hDis
  set slope : ℝ := (c - b) / (8 * κ) with hslope
  have hslopepos : 0 < slope := by
    have : (0 : ℝ) < c - b := by linarith
    rw [hslope]
    positivity
  refine ⟨slope / 2, κ, Nstart, hp, by positivity, ?_⟩
  intro f hf
  have hadd : Tendsto (fun i : ℕ => Nstart + i) atTop atTop := by
    simpa [Nat.add_comm] using tendsto_add_atTop_nat Nstart
  have hdiv : Tendsto (fun i : ℕ => soninShellCutScale b c (Nstart + i) κ) atTop atTop :=
    (tendsto_soninShellCutScale_atTop b c hbc hκ).comp hadd
  have hshort : ∀ᶠ i : ℕ in atTop,
      f (soninShellCutScale b c (Nstart + i) κ) + 1 ≤
        hsNormSq (evenSoninApertureSuccessiveLayerTransition a b c
          (soninShellCutScale b c (Nstart + i) κ) (hp i)) := by
    filter_upwards [hdiv.eventually hf,
      hdiv.eventually_ge_atTop ((1 + 36 * Dis) / (slope / 2))] with i hcap hbig
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
    have hthr : 1 + 36 * Dis ≤ slope / 2 * soninShellCutScale b c (Nstart + i) κ := by
      have hx := (div_le_iff₀ (half_pos hslopepos)).mp hbig
      rwa [mul_comm (soninShellCutScale b c (Nstart + i) κ) (slope / 2)] at hx
    have hsplit : slope / 2 * soninShellCutScale b c (Nstart + i) κ +
        slope / 2 * soninShellCutScale b c (Nstart + i) κ =
        slope * soninShellCutScale b c (Nstart + i) κ := by ring
    have hE := henergy i
    rw [hlin] at hE
    linarith [hcap, hthr, hsplit, hE]
  exact not_bddBelow_soninCompletedPacketValueVar_of_shortfall ha hab hbc
    (fun i => soninShellCutScale b c (Nstart + i) κ) hp hcp
    (fun i => f (soninShellCutScale b c (Nstart + i) κ)) 1 one_pos hshort

/-- **A surviving completion must outgrow a definite slope infinitely often.**  If the floor is
restored at every schedule of the shell cut, the contribution exceeds a fixed positive multiple of
the scale at arbitrarily large scales. -/
theorem frequently_slope_lt_of_forall_bddBelow (N₀ : ℕ) (hN₀ : 1 ≤ N₀)
    (a b c q : ℝ) (hbc : b < c) (ha : 0 < a) (hab : a < b) (hb : 0 < b) (haq : a < q)
    (hqb : 2 * q ≤ b) :
    ∃ s : ℝ, 0 < s ∧ ∀ f : ℝ → ℝ,
      (∀ (κ : ℝ) (Nstart : ℕ) (hp : ∀ i : ℕ, 1 < soninShellCutScale b c (Nstart + i) κ),
        ∃ M : ℝ, ∀ t : Finset ℕ,
          M ≤ soninCompletedPacketValueVar t a b c
            (fun i => soninShellCutScale b c (Nstart + i) κ) hp
            (fun i => f (soninShellCutScale b c (Nstart + i) κ))) →
        ∃ᶠ r : ℝ in atTop, s * r < f r := by
  obtain ⟨s, κ, Nstart, hp, hs, hmain⟩ :=
    exists_slope_not_bddBelow_soninCompletedPacketValueVar N₀ hN₀ a b c q hbc ha hab hb haq hqb
  refine ⟨s, hs, fun f hfloor => ?_⟩
  by_contra hcon
  have hcap : ∀ᶠ r : ℝ in atTop, f r ≤ s * r := by
    filter_upwards [Filter.not_frequently.mp hcon] with r hr
    exact not_lt.mp hr
  exact hmain f hcap (hfloor κ Nstart hp)

end RHTower

