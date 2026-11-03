import GaloisForLFunctions.GrowingWindowsOfSpecZ.TheTwoCollarFormOfAStage

/-!
# The two-collar form is born zero

Fix a stage `N + 1`, `ℓ = log(N + 1)`, and let the window length `A = ℓ + ε` grow through the stage.
The interior `[−ℓ, ℓ − A]` shrinks as `A` grows, so the two-collar form
`S^N_A(H) = inf_h Q_N(H + h)` is an infimum over fewer perturbations:

* **Monotone growth** (`twoCollarForm_mono`): `S^N_A(H) ≤ S^N_{A'}(H)` for `A ≤ A'`.
* **Birth at zero** (`twoCollarForm_birth`, `corr_birth`): at `A = ℓ` the interior is the whole window,
  the kick reads nothing (`c_H(ℓ) = 0` on `W_ℓ`), and if the window `W_ℓ` is nonnegative then
  `S^N_ℓ(H) = 0` for every `H ∈ W_ℓ`.

So within each stage two quantities are born at zero and grow with the collar width: the two-collar
form of the frozen datum and the kick `2w c_H(ℓ)`. Positivity through the stage is the statement that
the first stays above the second on every collar class (`stage_criterion`): a race between two
functionals of collar data, restarted at every prime power.
-/

noncomputable section

open MeasureTheory Set Filter Topology

namespace GaloisForLFunctions.GrowingWindowsOfSpecZ

open CohomologyOfWindowsOfSpecZ DimensionZeroGeometryOfSpecZ WindowTowerOfSpecZ
  SpacingScaleHarmonicAnalysis RHTower.WeilMarkovPole

variable {H : ℝ → ℝ}

/-- Interior tests of a longer window are interior tests of a shorter one. -/
theorem IsInteriorTest.mono {A A' ℓ : ℝ} {h : ℝ → ℝ} (hh : IsInteriorTest A' ℓ h) (hAA' : A ≤ A') :
    IsInteriorTest A ℓ h :=
  ⟨hh.contDiff, fun y hy => hh.vanish y fun hm => hy ⟨hm.1, by linarith [hm.2]⟩⟩

/-- **The two-collar form grows with the collar width.** -/
theorem twoCollarForm_mono (N : ℕ) {A A' : ℝ} (hAA' : A ≤ A') (H : ℝ → ℝ) :
    twoCollarForm N A H ≤ twoCollarForm N A' H :=
  le_iInf fun h => iInf_le_of_le ⟨h.1, h.2.mono hAA'⟩ le_rfl

theorem windowLevel_log_succ (N : ℕ) : windowLevel (Real.log (N + 1 : ℕ)) = N + 1 := by
  rw [windowLevel, Real.exp_log (by positivity), Nat.floor_natCast]

/-- **At birth the kick reads nothing**: `c_H(ℓ) = 0` on the window `W_ℓ`. -/
theorem corr_birth (N : ℕ) (hH : IsWindowTest (Real.log (N + 1 : ℕ)) H) :
    corr H (Real.log (N + 1 : ℕ)) = 0 := by
  rw [corr_eq_intervalIntegral hH le_rfl, intervalIntegral.integral_same]

/-- **The two-collar form is born zero.** If the window `W_ℓ`, `ℓ = log(N + 1)`, is nonnegative, then
`S^N_ℓ(H) = 0` for every window test `H` of length `ℓ`. -/
theorem twoCollarForm_birth {N : ℕ} (hN : 1 ≤ N)
    (hpos : ∀ G : ℝ → ℝ, IsWindowTest (Real.log (N + 1 : ℕ)) G → 0 ≤ weilQuad G)
    (hH : IsWindowTest (Real.log (N + 1 : ℕ)) H) :
    twoCollarForm N (Real.log (N + 1 : ℕ)) H = 0 := by
  have hA := windowLevel_log_succ N
  -- on `W_ℓ` the frozen form is Weil's form
  have hfrozen : ∀ G : ℝ → ℝ, IsWindowTest (Real.log (N + 1 : ℕ)) G →
      stageForm N G = weilQuad G := fun G hG => by
    rw [weilQuad_eq_stageForm_sub_corr hG hN hA, corr_birth N hG]; ring
  apply le_antisymm
  · -- the perturbation `−H` reaches `0`
    have hneg : IsInteriorTest (Real.log (N + 1 : ℕ)) (Real.log (N + 1 : ℕ)) (fun u => -H u) :=
      ⟨hH.contDiff.neg, fun y hy => by rw [hH.vanish y fun hm => hy ⟨hm.1, by linarith [hm.2]⟩,
        neg_zero]⟩
    refine (iInf_le _ ⟨_, hneg⟩).trans (le_of_eq ?_)
    have h0 : (fun u => H u + -H u) = fun _ => (0 : ℝ) := by funext u; ring
    simp only [h0]
    have hz : IsWindowTest (Real.log (N + 1 : ℕ)) (fun _ => (0 : ℝ)) :=
      ⟨contDiff_const, fun _ _ => rfl⟩
    have := weilQuad_mul_left 0 H
    simp only [zero_mul] at this
    rw [hfrozen _ hz, this]
    simp
  · refine le_iInf fun h => ?_
    have hHh := isWindowTest_add hH (h.2.isWindowTest le_rfl)
    rw [hfrozen _ hHh]
    exact EReal.coe_nonneg.mpr (hpos _ hHh)

end GaloisForLFunctions.GrowingWindowsOfSpecZ
