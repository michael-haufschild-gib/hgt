import GaloisForLFunctions.DimensionZeroGeometryOfSpecZ.TheGroundStateRepresentationOfAStage
import GaloisForLFunctions.DimensionZeroGeometryOfSpecZ.HeckeSimilitudesOfAWindowAreScalars

/-!
# The two-collar form of a stage

Let `A` be a window length of level `N + 1` (`log(N+1) ≤ A < log(N+2)`), `ℓ = log(N+1)` and
`w = Λ(N+1)/√(N+1)`. Crossing the stage adds one correlation (DZG `weilQuad_eq_stageForm_sub_corr`):

`Q(H) = Q_N(H) − 2w c_H(ℓ)`, `c_H(ℓ) = ∫ H(u)H(u + ℓ) du`.

The window splits into the **left collar** `[−A, −ℓ]`, the **interior** `[−ℓ, ℓ − A]` and the
**right collar** `[ℓ − A, 0]`. An *interior test* is a `C²` function supported in the interior.

* **The kick reads collar data only** (`corr_add_interior`): `c_{H+h}(ℓ) = c_H(ℓ)` for every interior
  test `h`. A jump of length `ℓ` from the interior leaves the window, and one into it starts outside.
* **The two-collar form** `S^N_A(H) = inf_h Q_N(H + h) ∈ [−∞, ∞)` (`twoCollarForm`) is the frozen form
  seen from the collars: it depends only on the class of `H` modulo interior tests
  (`twoCollarForm_add_interior`).
* **Kick law** (`iInf_weilQuad_add_interior`): the infimum over interior perturbations commutes with the
  kick, `inf_h Q(H + h) = S^N_A(H) − 2w c_H(ℓ)`.
* **Stage criterion** (`stage_criterion`): Weil's form is nonnegative on the window iff
  `2w c_H(ℓ) ≤ S^N_A(H)` for every window test `H`. Positivity of a window is a statement about
  collar data alone: the frozen form, minimized over the interior, must dominate the one new
  correlation between the two collars.
* **Reflection** (`twoCollarForm_windowInvolution`): the window involution `σ_A H(u) = H(−A − u)`
  swaps the collars, fixes the interior and the kick, and leaves the two-collar form invariant.
-/

noncomputable section

open MeasureTheory Set Filter Topology

namespace GaloisForLFunctions.GrowingWindowsOfSpecZ

open CohomologyOfWindowsOfSpecZ DimensionZeroGeometryOfSpecZ WindowTowerOfSpecZ
  SpacingScaleHarmonicAnalysis RHTower.WeilMarkovPole

variable {A ℓ : ℝ} {H h : ℝ → ℝ}

/-! ### Interior tests -/

/-- An **interior test** for the fold of length `ℓ` on a window of length `A`: a `C²` function
supported in `[−ℓ, ℓ − A]`, the part of the window that a jump of length `ℓ` cannot join to the
window. -/
structure IsInteriorTest (A ℓ : ℝ) (h : ℝ → ℝ) : Prop where
  contDiff : ContDiff ℝ 2 h
  vanish : ∀ y, y ∉ Icc (-ℓ) (ℓ - A) → h y = 0

namespace IsInteriorTest

theorem continuous (hh : IsInteriorTest A ℓ h) : Continuous h := hh.contDiff.continuous

theorem isWindowTest (hh : IsInteriorTest A ℓ h) (hℓA : ℓ ≤ A) : IsWindowTest A h :=
  ⟨hh.contDiff, fun y hy => hh.vanish y fun hm => hy ⟨by linarith [hm.1], by linarith [hm.2]⟩⟩

/-- An interior test vanishes at the left end `−ℓ` of the interior. -/
theorem left_end (hh : IsInteriorTest A ℓ h) : h (-ℓ) = 0 := by
  have hcl : IsClosed {u | h u = 0} := isClosed_eq hh.continuous continuous_const
  have hsub : Iio (-ℓ) ⊆ {u | h u = 0} := fun u hu =>
    hh.vanish u fun hm => absurd hm.1 (not_le.mpr hu)
  have hc := hcl.closure_subset_iff.mpr hsub
  rw [closure_Iio] at hc
  exact hc self_mem_Iic

/-- An interior test vanishes at the right end `ℓ − A` of the interior. -/
theorem right_end (hh : IsInteriorTest A ℓ h) : h (ℓ - A) = 0 := by
  have hcl : IsClosed {u | h u = 0} := isClosed_eq hh.continuous continuous_const
  have hsub : Ioi (ℓ - A) ⊆ {u | h u = 0} := fun u hu =>
    hh.vanish u fun hm => absurd hm.2 (not_le.mpr hu)
  have hc := hcl.closure_subset_iff.mpr hsub
  rw [closure_Ioi] at hc
  exact hc self_mem_Ici

end IsInteriorTest

theorem isInteriorTest_zero : IsInteriorTest A ℓ (fun _ => 0) := ⟨contDiff_const, fun _ _ => rfl⟩

/-- Interior tests form a vector space. -/
theorem isInteriorTest_lin {h₁ h₂ : ℝ → ℝ} (h₁i : IsInteriorTest A ℓ h₁)
    (h₂i : IsInteriorTest A ℓ h₂) (α β : ℝ) :
    IsInteriorTest A ℓ (fun u => α * h₁ u + β * h₂ u) :=
  ⟨(contDiff_const.mul h₁i.contDiff).add (contDiff_const.mul h₂i.contDiff), fun y hy => by
    rw [h₁i.vanish y hy, h₂i.vanish y hy]; ring⟩

/-- The window involution maps interior tests to interior tests. -/
theorem IsInteriorTest.windowInvolution (hh : IsInteriorTest A ℓ h) :
    IsInteriorTest A ℓ (windowInvolution A h) :=
  ⟨hh.contDiff.comp (contDiff_const.sub contDiff_id), fun y hy => hh.vanish _ fun hm =>
    hy ⟨by linarith [hm.2], by linarith [hm.1]⟩⟩

theorem isWindowTest_add {G : ℝ → ℝ} (hH : IsWindowTest A H) (hG : IsWindowTest A G) :
    IsWindowTest A (fun u => H u + G u) :=
  ⟨hH.contDiff.add hG.contDiff, fun y hy => by rw [hH.vanish y hy, hG.vanish y hy, add_zero]⟩

/-! ### The kick reads collar data only -/

/-- **Collar locality, pointwise.** Adding an interior test does not change the products
`H(u)H(u + ℓ)` that the fold of length `ℓ` integrates. -/
theorem mul_shift_add_interior (hH : IsWindowTest A H) (hh : IsInteriorTest A ℓ h)
    (hℓA : ℓ ≤ A) (u : ℝ) :
    (H u + h u) * (H (u + ℓ) + h (u + ℓ)) = H u * H (u + ℓ) := by
  -- the interior is never joined to the window by a jump of length `ℓ`
  have t1 : h u * H (u + ℓ) = 0 := by
    rcases lt_trichotomy u (-ℓ) with hu | hu | hu
    · rw [hh.vanish u fun hm => absurd hm.1 (not_le.mpr hu), zero_mul]
    · rw [hu, hh.left_end, zero_mul]
    · rw [hH.vanish (u + ℓ) fun hm => by linarith [hm.2], mul_zero]
  have t2 : H u * h (u + ℓ) = 0 := by
    rcases lt_trichotomy u (-A) with hu | hu | hu
    · rw [hH.vanish u fun hm => absurd hm.1 (not_le.mpr hu), zero_mul]
    · rw [hu, show -A + ℓ = ℓ - A by ring, hh.right_end, mul_zero]
    · rw [hh.vanish (u + ℓ) fun hm => by linarith [hm.2], mul_zero]
  have t3 : h u * h (u + ℓ) = 0 := by
    rcases lt_trichotomy u (-ℓ) with hu | hu | hu
    · rw [hh.vanish u fun hm => absurd hm.1 (not_le.mpr hu), zero_mul]
    · rw [hu, hh.left_end, zero_mul]
    · rw [hh.vanish (u + ℓ) fun hm => by linarith [hm.2], mul_zero]
  linear_combination t1 + t2 + t3

/-- **The kick reads collar data only**: `c_{H+h}(ℓ) = c_H(ℓ)` for every interior test `h`. -/
theorem corr_add_interior (hH : IsWindowTest A H) (hh : IsInteriorTest A ℓ h) (hℓA : ℓ ≤ A) :
    corr (fun u => H u + h u) ℓ = corr H ℓ := by
  simp only [corr]
  congr 1
  funext u
  exact mul_shift_add_interior hH hh hℓA u

/-- **The kick on a collar class.** On a window of level `N + 1`,
`Q(H + h) = Q_N(H + h) − 2w c_H(ℓ)` for every interior test `h`: the frozen part sees the whole
test, the kick only its collar data. -/
theorem weilQuad_add_interior {N : ℕ} (hN : 1 ≤ N) (hA : windowLevel A = N + 1)
    (hH : IsWindowTest A H) (hh : IsInteriorTest A (Real.log (N + 1 : ℕ)) h) :
    weilQuad (fun u => H u + h u) = stageForm N (fun u => H u + h u) -
      2 * primeJumpWeight (N + 1) * corr H (Real.log (N + 1 : ℕ)) := by
  have hℓA := log_succ_le_of_windowLevel hA
  rw [weilQuad_eq_stageForm_sub_corr (isWindowTest_add hH (hh.isWindowTest hℓA)) hN hA,
    corr_add_interior hH hh hℓA]

/-! ### The two-collar form -/

/-- The **two-collar form** of the stage `N + 1` on a window of length `A`:
`S^N_A(H) = inf_h Q_N(H + h)`, the infimum of the frozen form over interior perturbations, a value
in `[−∞, ∞)` that depends only on the collar data of `H`. -/
def twoCollarForm (N : ℕ) (A : ℝ) (H : ℝ → ℝ) : EReal :=
  ⨅ h : {h : ℝ → ℝ // IsInteriorTest A (Real.log (N + 1 : ℕ)) h},
    ((stageForm N (fun u => H u + h.1 u) : ℝ) : EReal)

/-- The two-collar form is at most the frozen form. -/
theorem twoCollarForm_le_stageForm (N : ℕ) (A : ℝ) (H : ℝ → ℝ) :
    twoCollarForm N A H ≤ ((stageForm N H : ℝ) : EReal) := by
  refine (iInf_le _ ⟨fun _ => 0, isInteriorTest_zero⟩).trans (le_of_eq ?_)
  simp only [add_zero]

/-- **The two-collar form depends only on collar data.** -/
theorem twoCollarForm_add_interior (N : ℕ) (A : ℝ) (H : ℝ → ℝ) {h₀ : ℝ → ℝ}
    (h₀i : IsInteriorTest A (Real.log (N + 1 : ℕ)) h₀) :
    twoCollarForm N A (fun u => H u + h₀ u) = twoCollarForm N A H := by
  apply le_antisymm
  · refine le_iInf fun h => ?_
    have hi := isInteriorTest_lin h.2 h₀i 1 (-1)
    refine (iInf_le _ ⟨_, hi⟩).trans (le_of_eq ?_)
    congr 2
    funext u
    ring
  · refine le_iInf fun h => ?_
    have hi := isInteriorTest_lin h₀i h.2 1 1
    refine (iInf_le _ ⟨_, hi⟩).trans (le_of_eq ?_)
    congr 2
    funext u
    ring

/-- Subtracting a real number is an order automorphism of `[−∞, ∞]`. -/
def subRealOrderIso (c : ℝ) : EReal ≃o EReal where
  toFun x := x - c
  invFun x := x + c
  left_inv _ := EReal.sub_add_cancel
  right_inv _ := EReal.add_sub_cancel_right
  map_rel_iff' := by
    intro x y
    constructor
    · intro hxy
      have h2 : x - c + c ≤ y - c + c := add_le_add_left hxy _
      rwa [EReal.sub_add_cancel, EReal.sub_add_cancel] at h2
    · intro hxy
      exact EReal.sub_le_sub hxy le_rfl

/-- **Kick law.** The infimum of Weil's form over a collar class is the two-collar form minus the
kick: `inf_h Q(H + h) = S^N_A(H) − 2w c_H(ℓ)`. -/
theorem iInf_weilQuad_add_interior {N : ℕ} (hN : 1 ≤ N) (hA : windowLevel A = N + 1)
    (hH : IsWindowTest A H) :
    (⨅ h : {h : ℝ → ℝ // IsInteriorTest A (Real.log (N + 1 : ℕ)) h},
      ((weilQuad (fun u => H u + h.1 u) : ℝ) : EReal)) =
      twoCollarForm N A H -
        ((2 * primeJumpWeight (N + 1) * corr H (Real.log (N + 1 : ℕ)) : ℝ) : EReal) := by
  set c := 2 * primeJumpWeight (N + 1) * corr H (Real.log (N + 1 : ℕ))
  have hterm : ∀ h : {h : ℝ → ℝ // IsInteriorTest A (Real.log (N + 1 : ℕ)) h},
      ((weilQuad (fun u => H u + h.1 u) : ℝ) : EReal) =
        subRealOrderIso c ((stageForm N (fun u => H u + h.1 u) : ℝ) : EReal) := fun h => by
    rw [weilQuad_add_interior hN hA hH h.2]
    rfl
  simp_rw [hterm]
  rw [← OrderIso.map_iInf]
  rfl

/-- **Stage criterion.** On a window of level `N + 1` Weil's form is nonnegative iff on every window
test the two-collar form dominates the kick: `2w c_H(log(N+1)) ≤ S^N_A(H)`. -/
theorem stage_criterion {N : ℕ} (hN : 1 ≤ N) (hA : windowLevel A = N + 1) :
    (∀ G : ℝ → ℝ, IsWindowTest A G → 0 ≤ weilQuad G) ↔
      ∀ H : ℝ → ℝ, IsWindowTest A H →
        ((2 * primeJumpWeight (N + 1) * corr H (Real.log (N + 1 : ℕ)) : ℝ) : EReal) ≤
          twoCollarForm N A H := by
  have hℓA := log_succ_le_of_windowLevel hA
  constructor
  · intro hpos H hH
    refine le_iInf fun h => ?_
    have hq := hpos _ (isWindowTest_add hH (h.2.isWindowTest hℓA))
    rw [weilQuad_add_interior hN hA hH h.2] at hq
    exact EReal.coe_le_coe_iff.mpr (by linarith)
  · intro hcol G hG
    have h1 := (hcol G hG).trans (twoCollarForm_le_stageForm N A G)
    have h2 := EReal.coe_le_coe_iff.mp h1
    rw [weilQuad_eq_stageForm_sub_corr hG hN hA]
    linarith

/-! ### Reflection -/

/-- The kick is invariant under the window involution: `c_{σH}(ℓ) = c_H(ℓ)`. -/
theorem corr_windowInvolution (A ℓ : ℝ) (H : ℝ → ℝ) :
    corr (windowInvolution A H) ℓ = corr H ℓ := by
  simp only [corr, windowInvolution]
  have h : ∫ u, H (-A - ℓ - u + ℓ) * H (-A - ℓ - u) = ∫ v, H (v + ℓ) * H v :=
    integral_sub_left_eq_self (μ := volume) (fun v => H (v + ℓ) * H v) (-A - ℓ)
  rw [show (∫ u, H u * H (u + ℓ)) = ∫ v, H (v + ℓ) * H v by
    congr 1; funext v; ring, ← h]
  congr 1
  funext u
  rw [show -A - ℓ - u + ℓ = -A - u by ring, show -A - (u + ℓ) = -A - ℓ - u by ring]

/-- The frozen form is invariant under the window involution on window tests of level `N + 1`. -/
theorem stageForm_windowInvolution {N : ℕ} (hN : 1 ≤ N) (hA : windowLevel A = N + 1)
    (hH : IsWindowTest A H) : stageForm N (windowInvolution A H) = stageForm N H := by
  have e1 := weilQuad_eq_stageForm_sub_corr hH hN hA
  have e2 := weilQuad_eq_stageForm_sub_corr hH.windowInvolution hN hA
  rw [weilQuad_windowInvolution, corr_windowInvolution] at e2
  linarith

/-- **The two-collar form is reflection invariant**: `S^N_A(σ_AH) = S^N_A(H)`. -/
theorem twoCollarForm_windowInvolution {N : ℕ} (hN : 1 ≤ N) (hA : windowLevel A = N + 1)
    (hH : IsWindowTest A H) : twoCollarForm N A (windowInvolution A H) = twoCollarForm N A H := by
  have hℓA := log_succ_le_of_windowLevel hA
  -- `σ(H + h) = σH + σh`, and `σ` is an involution of the interior tests
  have key : ∀ {F : ℝ → ℝ}, IsWindowTest A F → ∀ h : ℝ → ℝ,
      IsInteriorTest A (Real.log (N + 1 : ℕ)) h →
      stageForm N (fun u => windowInvolution A F u + windowInvolution A h u) =
        stageForm N (fun u => F u + h u) := fun {F} hF h hh => by
    have hFh := isWindowTest_add hF (hh.isWindowTest hℓA)
    rw [← stageForm_windowInvolution hN hA hFh]
    rfl
  apply le_antisymm
  · refine le_iInf fun h => ?_
    refine (iInf_le _ ⟨_, h.2.windowInvolution⟩).trans (le_of_eq ?_)
    exact congrArg (fun x : ℝ => (x : EReal)) (key hH h.1 h.2)
  · refine le_iInf fun h => ?_
    refine (iInf_le _ ⟨_, h.2.windowInvolution⟩).trans (le_of_eq ?_)
    have e := key hH _ h.2.windowInvolution
    rw [windowInvolution_windowInvolution] at e
    exact congrArg (fun x : ℝ => (x : EReal)) e.symm

end GaloisForLFunctions.GrowingWindowsOfSpecZ
