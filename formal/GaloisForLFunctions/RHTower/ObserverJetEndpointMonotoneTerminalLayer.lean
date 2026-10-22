import GaloisForLFunctions.RHTower.WeilLagPowerGapExceptionalSampling
import GaloisForLFunctions.RHTower.Suzuki.SuzukiObserverJetTerminalLayer
import GaloisForLFunctions.RHTower.SquareSampleObserverJetOneSidedStrip

/-!
# Endpoint-Monotone Observer-Jet Terminal Layer and Polynomial-Schedule Interior Criteria

This file combines the mass-tail representation and `lagBracketSlope` bridge of
`SquareSampleObserverJetOneSidedStrip` with the terminal/interior layer decomposition of
`SuzukiObserverJetTerminalLayer` and the power-gap strip bootstrap of
`MobiusDivisorOneSidedPowerGapBootstrap` and `MobiusDivisorLowerStripPowerGapBootstrap`:

1. **Exact separation of the moving endpoint mass from the `M`-independent prefix-mass sum:**
   For `3 ≤ M` and `j < M - 3`,
   `completedSourceObserverJetHistory M j = (M - 3 - j) * completedSourceObserverJetMass M - ∑_{k ∈ Ico (j+1) (M-2)} completedSourceObserverJetMass (k + 2)`
   (`completedSourceObserverJetHistory_eq_mass_mul_sub_sum_mass`).
   Consequently, at every aperture `M`, for at least one of the two one-sided history actions
   (positive if `completedSourceObserverJetMass M ≤ 0`, negative if `0 ≤ completedSourceObserverJetMass M`),
   the moving-aperture drift `(M - 3 - j) * completedSourceObserverJetMass M` is nonpositive and
   drops out of the one-sided action (`completedSourceObserverJetHistory_le_neg_sum_mass_of_nonpos`,
   `neg_completedSourceObserverJetHistory_le_sum_mass_of_nonneg`).

2. **Negative-history terminal/interior decomposition and polynomial-schedule (`M = N^6, L = N^5`)
   RH criteria and strip laws:**
   * Completes the negative-history counterpart of `SuzukiObserverJetTerminalLayer`:
     `completedSourceObserverJetTerminalNegativeAction_le_cubic`,
     `completedSourceObserverJetTerminalNegativeAction_le_linear`,
     `completedSourceObserverJetTerminalNegativeAction_sixth_fifth_le`,
     `completedSourceObserverJetNegativeHistoryAction_eq_interior_add_terminal`, and
     `riemannHypothesis_of_completedSourceObserverJetInteriorNegative_linear`.
   * Combines the terminal cubic/linear bounds with the `m`-th power one-sided strip laws
     (`riemannHypothesis_iff_mobiusDivisorSquareRootAbel_pow_bddAbove` and
     `riemannHypothesis_iff_mobiusDivisorSquareRootAbel_pow_bddBelow`) to close the
     explicit polynomial schedule `M = N^6, L = N^5`: a linear bound on
     `completedSourceObserverJetInteriorPositiveAction (N^6) (N^5)` or
     `completedSourceObserverJetInteriorNegativeAction (N^6) (N^5)` unconditionally implies
     `RiemannHypothesis`
     (`riemannHypothesis_of_completedSourceObserverJetInteriorPositive_sixth_fifth_linear`,
     `riemannHypothesis_of_completedSourceObserverJetInteriorNegative_sixth_fifth_linear`).

3. **Endpoint-monotone `O(L^4 / (M^2 √M))` terminal layer bounds (boosting `M^{5/6}` to `M^{7/8}`):**
   In `SuzukiObserverJetTerminalLayer`, bounding `|q(k)| ≤ A/(k+1)` at every interior step `k`
   gave `|completedSourceObserverJetHistory M j| ≤ 4 A L^2 / M` and terminal action
   `O(L^3 / (M √M))`. Using the monotonicity of `ψ` on `[M - 2 - L, M]` via
   `lagBracketSlope_sub_bounds_of_monotone` and the prime-free bridge
   `abs_observerJetMass_completedHarmonic_sub_lagBracketSlope_sub_le`, we prove that all interior
   prime dependence cancels:
   * Upper bound (`completedSourceObserverJetHistory_terminal_le_of_endpoint`): depends ONLY on the
     single outer endpoint `max (psiRemainder M) 0`:
     `completedSourceObserverJetHistory M j ≤ (2 * max (psiRemainder M) 0 + 2 * L + 2 * (1 + |2γ|)) * L^2 / M^2`.
   * Lower bound (`neg_completedSourceObserverJetHistory_terminal_le_of_endpoint`): depends ONLY on
     the single left edge `max (-psiRemainder (M - 2 - L)) 0`:
     `-completedSourceObserverJetHistory M j ≤ (2 * max (-psiRemainder (M - 2 - L)) 0 + 2 * (L + 2) + 2 * (1 + |2γ|)) * L^2 / M^2`.
   * Whenever `psiRemainder M ≤ K * L` (in particular whenever `psiRemainder M ≤ 0`), the terminal
     positive action is bounded by `O(L^4 / (M^2 √M))`
     (`completedSourceObserverJetTerminalPositiveAction_le_quartic_of_endpoint`), which is linear in
     `M` up to `L^4 ≤ M^3 √M` (`L ≤ M^{7/8}`, including the explicit schedule `M = N^8, L = N^7`,
     and `riemannHypothesis_of_completedSourceObserverJetInteriorPositive_eighth_seventh_linear`).
-/

open Set Filter Topology
open scoped BigOperators
noncomputable section

namespace GaloisForLFunctions.RHTower

open _root_.RHTower GaloisForLFunctions.HTGeometry

/-! ## Section 1: Exact separation of moving-aperture mass and `M`-independent prefix sum -/

/-- Exact decomposition of `completedSourceObserverJetHistory M j` into the moving-endpoint mass
term `((M - 3 - j : ℕ) : ℝ) * completedSourceObserverJetMass M` minus the `M`-independent sum of
prefix masses `∑ k ∈ Finset.Ico (j + 1) (M - 2), completedSourceObserverJetMass (k + 2)`. -/
theorem completedSourceObserverJetHistory_eq_mass_mul_sub_sum_mass
    {M j : ℕ} (hM : 3 ≤ M) (hj : j ∈ Finset.range (M - 3)) :
    completedSourceObserverJetHistory M j =
      ((M - 3 - j : ℕ) : ℝ) * completedSourceObserverJetMass M -
        ∑ k ∈ Finset.Ico (j + 1) (M - 2), completedSourceObserverJetMass (k + 2) := by
  have hj' : j < M - 3 := Finset.mem_range.mp hj
  rw [completedSourceObserverJetHistory_eq_sum_mass_sub hM hj, Finset.sum_sub_distrib,
    Finset.sum_const, Nat.card_Ico, nsmul_eq_mul,
    show M - 2 - (j + 1) = M - 3 - j by omega]

/-- At any aperture `M` where `completedSourceObserverJetMass M ≤ 0`, the moving-endpoint drift is
nonpositive and drops out of the upper bound on `completedSourceObserverJetHistory M j`. -/
theorem completedSourceObserverJetHistory_le_neg_sum_mass_of_nonpos
    {M j : ℕ} (hM : 3 ≤ M) (hj : j ∈ Finset.range (M - 3))
    (hmass : completedSourceObserverJetMass M ≤ 0) :
    completedSourceObserverJetHistory M j ≤
      -∑ k ∈ Finset.Ico (j + 1) (M - 2), completedSourceObserverJetMass (k + 2) := by
  rw [completedSourceObserverJetHistory_eq_mass_mul_sub_sum_mass hM hj]
  have hnonpos : ((M - 3 - j : ℕ) : ℝ) * completedSourceObserverJetMass M ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) hmass
  linarith

/-- At any aperture `M` where `0 ≤ completedSourceObserverJetMass M`, the moving-endpoint drift is
nonnegative and drops out of the upper bound on `-completedSourceObserverJetHistory M j`. -/
theorem neg_completedSourceObserverJetHistory_le_sum_mass_of_nonneg
    {M j : ℕ} (hM : 3 ≤ M) (hj : j ∈ Finset.range (M - 3))
    (hmass : 0 ≤ completedSourceObserverJetMass M) :
    -completedSourceObserverJetHistory M j ≤
      ∑ k ∈ Finset.Ico (j + 1) (M - 2), completedSourceObserverJetMass (k + 2) := by
  rw [completedSourceObserverJetHistory_eq_mass_mul_sub_sum_mass hM hj]
  have hnonneg : 0 ≤ ((M - 3 - j : ℕ) : ℝ) * completedSourceObserverJetMass M :=
    mul_nonneg (Nat.cast_nonneg _) hmass
  linarith

/-! ## Section 2: Negative-history terminal/interior decomposition and polynomial schedules -/

/-- Terminal negative-history action over the last `L` coordinates `M - 3 - L ≤ j < M - 3`. -/
def completedSourceObserverJetTerminalNegativeAction (M L : ℕ) : ℝ :=
  ∑ j ∈ Finset.Ico (M - 3 - L) (M - 3),
    max (-completedSourceObserverJetHistory M j) 0 / Real.sqrt (j + 1 : ℕ)

/-- Interior negative-history action over the prefix `0 ≤ j < M - 3 - L`. -/
def completedSourceObserverJetInteriorNegativeAction (M L : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (M - 3 - L),
    max (-completedSourceObserverJetHistory M j) 0 / Real.sqrt (j + 1 : ℕ)

theorem completedSourceObserverJetNegativeHistoryAction_eq_interior_add_terminal
    (M L : ℕ) :
    completedSourceObserverJetNegativeHistoryAction M =
      completedSourceObserverJetInteriorNegativeAction M L +
        completedSourceObserverJetTerminalNegativeAction M L := by
  unfold completedSourceObserverJetNegativeHistoryAction
    completedSourceObserverJetInteriorNegativeAction
    completedSourceObserverJetTerminalNegativeAction
  exact (Finset.sum_range_add_sum_Ico _ (Nat.sub_le (M - 3) L)).symm

theorem completedSourceObserverJetTerminalNegativeAction_le_cubic
    {M L : ℕ} (hwindow : 2 * (L + 2) ≤ M) :
    completedSourceObserverJetTerminalNegativeAction M L ≤
      8 * completedSourceObserverJetChargeConstant * (L : ℝ) ^ 3 /
        ((M : ℝ) * Real.sqrt (M : ℝ)) := by
  have hA := completedSourceObserverJetChargeConstant_nonneg
  have hM : 0 < (M : ℝ) := by exact_mod_cast (show 0 < M by omega)
  have hsM : 0 < Real.sqrt (M : ℝ) := Real.sqrt_pos.mpr hM
  have hLle : L ≤ M - 3 := by omega
  have hterm (j : ℕ) (hj : j ∈ Finset.Ico (M - 3 - L) (M - 3)) :
      max (-completedSourceObserverJetHistory M j) 0 / Real.sqrt (j + 1 : ℕ) ≤
        8 * completedSourceObserverJetChargeConstant * (L : ℝ) ^ 2 /
          ((M : ℝ) * Real.sqrt (M : ℝ)) := by
    have hj' := Finset.mem_Ico.mp hj
    have hhalf : (M : ℝ) ≤ 2 * (j + 1 : ℕ) := by
      exact_mod_cast (show M ≤ 2 * (j + 1) by omega)
    have hsj : 0 < Real.sqrt (j + 1 : ℕ) := Real.sqrt_pos.mpr (by positivity)
    have hsqrt : Real.sqrt (M : ℝ) ≤ 2 * Real.sqrt (j + 1 : ℕ) := by
      apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
      rw [mul_pow, Real.sq_sqrt hM.le, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ (j + 1 : ℕ))]
      nlinarith
    have hinv : 1 / Real.sqrt (j + 1 : ℕ) ≤ 2 / Real.sqrt (M : ℝ) := by
      apply (div_le_div_iff₀ hsj hsM).mpr
      simpa using hsqrt
    have hhist : max (-completedSourceObserverJetHistory M j) 0 ≤
        4 * completedSourceObserverJetChargeConstant * (L : ℝ) ^ 2 / (M : ℝ) := by
      apply max_le
      · exact (neg_le_abs _).trans (abs_completedSourceObserverJetHistory_terminal_le hwindow hj)
      · positivity
    calc
      _ = max (-completedSourceObserverJetHistory M j) 0 *
          (1 / Real.sqrt (j + 1 : ℕ)) := by ring
      _ ≤ (4 * completedSourceObserverJetChargeConstant * (L : ℝ) ^ 2 / (M : ℝ)) *
          (2 / Real.sqrt (M : ℝ)) := mul_le_mul hhist hinv (by positivity) (by positivity)
      _ = _ := by ring
  unfold completedSourceObserverJetTerminalNegativeAction
  calc
    _ ≤ ∑ _j ∈ Finset.Ico (M - 3 - L) (M - 3),
        8 * completedSourceObserverJetChargeConstant * (L : ℝ) ^ 2 /
          ((M : ℝ) * Real.sqrt (M : ℝ)) := Finset.sum_le_sum hterm
    _ = (L : ℝ) * (8 * completedSourceObserverJetChargeConstant * (L : ℝ) ^ 2 /
        ((M : ℝ) * Real.sqrt (M : ℝ))) := by simp [Nat.sub_sub_self hLle]
    _ = _ := by ring

theorem completedSourceObserverJetTerminalNegativeAction_le_linear
    {M L : ℕ} (hwindow : 2 * (L + 2) ≤ M)
    (hscale : (L : ℝ) ^ 3 ≤ (M : ℝ) ^ 2 * Real.sqrt (M : ℝ)) :
    completedSourceObserverJetTerminalNegativeAction M L ≤
      8 * completedSourceObserverJetChargeConstant * (M : ℝ) := by
  have hA := completedSourceObserverJetChargeConstant_nonneg
  have hM : 0 < (M : ℝ) := by exact_mod_cast (show 0 < M by omega)
  have hsM : 0 < Real.sqrt (M : ℝ) := Real.sqrt_pos.mpr hM
  calc
    _ ≤ 8 * completedSourceObserverJetChargeConstant * (L : ℝ) ^ 3 /
        ((M : ℝ) * Real.sqrt (M : ℝ)) :=
      completedSourceObserverJetTerminalNegativeAction_le_cubic hwindow
    _ ≤ 8 * completedSourceObserverJetChargeConstant *
        ((M : ℝ) ^ 2 * Real.sqrt (M : ℝ)) /
          ((M : ℝ) * Real.sqrt (M : ℝ)) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_left hscale (by positivity)
    _ = _ := by field_simp

theorem completedSourceObserverJetTerminalNegativeAction_sixth_fifth_le
    {N : ℕ} (hN : 3 ≤ N) :
    completedSourceObserverJetTerminalNegativeAction (N ^ 6) (N ^ 5) ≤
      8 * completedSourceObserverJetChargeConstant * (N ^ 6 : ℕ) := by
  have hwindow : 2 * (N ^ 5 + 2) ≤ N ^ 6 := by
    have hN5 : 4 ≤ N ^ 5 := by
      calc 4 ≤ (3 : ℕ) ^ 5 := by norm_num
        _ ≤ N ^ 5 := by gcongr
    rw [show N ^ 6 = N * N ^ 5 by ring]
    have hmul := Nat.mul_le_mul_right (N ^ 5) hN
    nlinarith
  have hsqrt : Real.sqrt (N ^ 6 : ℕ) = (N : ℝ) ^ 3 := by
    rw [Nat.cast_pow, show (N : ℝ) ^ 6 = ((N : ℝ) ^ 3) ^ 2 by ring,
      Real.sqrt_sq (by positivity)]
  apply completedSourceObserverJetTerminalNegativeAction_le_linear hwindow
  apply le_of_eq
  rw [hsqrt]
  push_cast
  ring

theorem riemannHypothesis_of_completedSourceObserverJetInteriorNegative_linear
    {L : ℕ → ℕ} {C : ℝ}
    (hwindow : ∀ M : ℕ, 4 ≤ M → 2 * (L M + 2) ≤ M)
    (hscale : ∀ M : ℕ, 4 ≤ M →
      (L M : ℝ) ^ 3 ≤ (M : ℝ) ^ 2 * Real.sqrt (M : ℝ))
    (hinterior : ∀ M : ℕ, 4 ≤ M →
      completedSourceObserverJetInteriorNegativeAction M (L M) ≤ C * (M : ℝ)) :
    RiemannHypothesis := by
  obtain ⟨K, hK3, hK4⟩ :
      ∃ K : ℝ, completedSourceObserverJetNegativeHistoryAction 3 / 3 ≤ K ∧
        C + 8 * completedSourceObserverJetChargeConstant ≤ K :=
    ⟨max (completedSourceObserverJetNegativeHistoryAction 3 / 3)
      (C + 8 * completedSourceObserverJetChargeConstant),
      le_max_left _ _, le_max_right _ _⟩
  apply riemannHypothesis_of_completedSourceObserverJetNegativeHistory_linear (C := K)
  intro M hM
  by_cases hM3 : M = 3
  · subst M
    have hmul := mul_le_mul_of_nonneg_right hK3 (by positivity : (0 : ℝ) ≤ 3)
    rw [div_mul_cancel₀ _ (by norm_num : (3 : ℝ) ≠ 0)] at hmul
    simpa using hmul
  · clear hK3
    have hM4 : 4 ≤ M := by omega
    have htail := completedSourceObserverJetTerminalNegativeAction_le_linear
      (hwindow M hM4) (hscale M hM4)
    have hi := hinterior M hM4
    have hfull : completedSourceObserverJetNegativeHistoryAction M ≤
        (C + 8 * completedSourceObserverJetChargeConstant) * (M : ℝ) := by
      rw [completedSourceObserverJetNegativeHistoryAction_eq_interior_add_terminal M (L M)]
      linarith
    exact hfull.trans (mul_le_mul_of_nonneg_right hK4 (Nat.cast_nonneg M))

/-- **Polynomial-schedule (`M = N^6, L = N^5`) positive interior action criterion for RH.**
Combining `completedSourceObserverJetTerminalPositiveAction_sixth_fifth_le` with the `m = 6` case
of `riemannHypothesis_iff_mobiusDivisorSquareRootAbel_pow_bddAbove` closes RH from a linear bound
on the interior positive action along the single polynomial sequence `M = N^6, L = N^5`. -/
theorem riemannHypothesis_of_completedSourceObserverJetInteriorPositive_sixth_fifth_linear
    {C : ℝ}
    (hinterior : ∀ N : ℕ, 3 ≤ N →
      completedSourceObserverJetInteriorPositiveAction (N ^ 6) (N ^ 5) ≤ C * (N ^ 6 : ℕ)) :
    RiemannHypothesis := by
  obtain ⟨B, _hB0, hB⟩ := exists_mobiusDivisorSquareRootAbel_upper_positiveHistory
  rw [riemannHypothesis_iff_mobiusDivisorSquareRootAbel_pow_bddAbove (m := 6) (by omega)]
  obtain ⟨K, hK2, hK3⟩ :
      ∃ K : ℝ, mobiusDivisorSquareRootAbelMoment (2 ^ 6) / (2 ^ 6 : ℕ) ≤ K ∧
        B + (3 / 8 : ℝ) * (max 0 C + 8 * completedSourceObserverJetChargeConstant) ≤ K :=
    ⟨max (mobiusDivisorSquareRootAbelMoment (2 ^ 6) / (2 ^ 6 : ℕ))
      (B + (3 / 8 : ℝ) * (max 0 C + 8 * completedSourceObserverJetChargeConstant)),
      le_max_left _ _, le_max_right _ _⟩
  refine ⟨K, fun N hN2 => ?_⟩
  have hN_ge_2 : 2 ≤ N := by
    by_contra hlt
    have hle1 : N ≤ 1 := by omega
    have hpow : N ^ 6 ≤ 1 ^ 6 := Nat.pow_le_pow_left hle1 6
    omega
  by_cases hN_eq_2 : N = 2
  · subst N
    exact hK2
  · clear hK2
    have hN : 3 ≤ N := by omega
    have hN6 : 3 ≤ N ^ 6 := by
      calc 3 ≤ 3 ^ 6 := by norm_num
        _ ≤ N ^ 6 := Nat.pow_le_pow_left hN 6
    have hpos : (0 : ℝ) < (N ^ 6 : ℕ) := by exact_mod_cast (show 0 < N ^ 6 by omega)
    have htail := completedSourceObserverJetTerminalPositiveAction_sixth_fifth_le hN
    have hi : completedSourceObserverJetInteriorPositiveAction (N ^ 6) (N ^ 5) ≤
        max 0 C * (N ^ 6 : ℕ) :=
      (hinterior N hN).trans (mul_le_mul_of_nonneg_right (le_max_right 0 C) (Nat.cast_nonneg _))
    have hfull : completedSourceObserverJetPositiveHistoryAction (N ^ 6) ≤
        (max 0 C + 8 * completedSourceObserverJetChargeConstant) * (N ^ 6 : ℕ) := by
      rw [completedSourceObserverJetPositiveHistoryAction_eq_interior_add_terminal (N ^ 6) (N ^ 5)]
      linarith
    have h1 := hB (N ^ 6) hN6
    have hdiv : mobiusDivisorSquareRootAbelMoment (N ^ 6) / (N ^ 6 : ℕ) ≤
        B + (3 / 8 : ℝ) * (max 0 C + 8 * completedSourceObserverJetChargeConstant) :=
      (div_le_iff₀ hpos).mpr (by linarith)
    exact hdiv.trans hK3

/-- **Polynomial-schedule (`M = N^6, L = N^5`) negative interior action criterion for RH.** -/
theorem riemannHypothesis_of_completedSourceObserverJetInteriorNegative_sixth_fifth_linear
    {C : ℝ}
    (hinterior : ∀ N : ℕ, 3 ≤ N →
      completedSourceObserverJetInteriorNegativeAction (N ^ 6) (N ^ 5) ≤ C * (N ^ 6 : ℕ)) :
    RiemannHypothesis := by
  obtain ⟨B, _hB0, hB⟩ := exists_mobiusDivisorSquareRootAbel_lower_negativeHistory
  rw [riemannHypothesis_iff_mobiusDivisorSquareRootAbel_pow_bddBelow (m := 6) (by omega)]
  obtain ⟨K, hK2, hK3⟩ :
      ∃ K : ℝ, -K ≤ mobiusDivisorSquareRootAbelMoment (2 ^ 6) / (2 ^ 6 : ℕ) ∧
        B + (3 / 8 : ℝ) * (max 0 C + 8 * completedSourceObserverJetChargeConstant) ≤ K :=
    ⟨max (-mobiusDivisorSquareRootAbelMoment (2 ^ 6) / (2 ^ 6 : ℕ))
      (B + (3 / 8 : ℝ) * (max 0 C + 8 * completedSourceObserverJetChargeConstant)),
      by
        have h := neg_le_neg (le_max_left (-mobiusDivisorSquareRootAbelMoment (2 ^ 6) / (2 ^ 6 : ℕ))
          (B + (3 / 8 : ℝ) * (max 0 C + 8 * completedSourceObserverJetChargeConstant)))
        simpa [neg_div] using h,
      le_max_right _ _⟩
  refine ⟨-K, fun N hN2 => ?_⟩
  have hN_ge_2 : 2 ≤ N := by
    by_contra hlt
    have hle1 : N ≤ 1 := by omega
    have hpow : N ^ 6 ≤ 1 ^ 6 := Nat.pow_le_pow_left hle1 6
    omega
  by_cases hN_eq_2 : N = 2
  · subst N
    exact hK2
  · clear hK2
    have hN : 3 ≤ N := by omega
    have hN6 : 3 ≤ N ^ 6 := by
      calc 3 ≤ 3 ^ 6 := by norm_num
        _ ≤ N ^ 6 := Nat.pow_le_pow_left hN 6
    have hpos : (0 : ℝ) < (N ^ 6 : ℕ) := by exact_mod_cast (show 0 < N ^ 6 by omega)
    have htail := completedSourceObserverJetTerminalNegativeAction_sixth_fifth_le hN
    have hi : completedSourceObserverJetInteriorNegativeAction (N ^ 6) (N ^ 5) ≤
        max 0 C * (N ^ 6 : ℕ) :=
      (hinterior N hN).trans (mul_le_mul_of_nonneg_right (le_max_right 0 C) (Nat.cast_nonneg _))
    have hfull : completedSourceObserverJetNegativeHistoryAction (N ^ 6) ≤
        (max 0 C + 8 * completedSourceObserverJetChargeConstant) * (N ^ 6 : ℕ) := by
      rw [completedSourceObserverJetNegativeHistoryAction_eq_interior_add_terminal (N ^ 6) (N ^ 5)]
      linarith
    have h1 := hB (N ^ 6) hN6
    have hdiv : -(B + (3 / 8 : ℝ) * (max 0 C + 8 * completedSourceObserverJetChargeConstant)) ≤
        mobiusDivisorSquareRootAbelMoment (N ^ 6) / (N ^ 6 : ℕ) :=
      (le_div_iff₀ hpos).mpr (by linarith)
    exact (neg_le_neg hK3).trans hdiv

/-! ## Section 3: Endpoint-monotone `O(L^4 / (M^2 √M))` terminal layer bounds -/

/-- Exact endpoint-monotone upper step bound on `lagBracketSlope M - lagBracketSlope d`:
because `ψ` is nondecreasing on `[d, M)` and `log(M/d) ≥ (M - d)/M`, the slope increment depends
only on the right-endpoint remainder `psiRemainder M` plus the linear shift `M - d`. -/
theorem lagBracketSlope_sub_le_psiRemainder_add_sub {d M : ℕ} (hd : 1 ≤ d) (hdM : d ≤ M) :
    lagBracketSlope M - lagBracketSlope d ≤
      (psiRemainder M + ((M : ℝ) - d)) * (((M : ℝ) - d) / ((d : ℝ) * M)) := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hM0 : (0 : ℝ) < M := by exact_mod_cast (le_trans hd hdM)
  obtain ⟨_, hm2⟩ := lagBracketSlope_sub_bounds_of_monotone hd hdM
  obtain ⟨hl1, _⟩ := sub_le_log_div_and_log_div_le hd hdM
  have hpsi : Chebyshev.psi M = psiRemainder M + M := by
    rw [psiRemainder, chebyshevPsi_eq_psi]
    ring
  have heq : Chebyshev.psi M * (((M : ℝ) - d) / ((d : ℝ) * M)) - ((M : ℝ) - d) / M =
      (psiRemainder M + ((M : ℝ) - d)) * (((M : ℝ) - d) / ((d : ℝ) * M)) := by
    rw [hpsi]
    field_simp
    ring
  linarith

/-- Exact endpoint-monotone lower step bound on `lagBracketSlope M - lagBracketSlope d`:
for any `1 ≤ m ≤ d ≤ M`, because `ψ(d) ≥ ψ(m)` and `log(M/d) ≤ (M - d)/d`, the negated slope
increment depends only on the left-edge remainder `psiRemainder m` plus `M - m`. -/
theorem neg_lagBracketSlope_sub_le_of_le {m d M : ℕ} (hm : 1 ≤ m) (hmd : m ≤ d) (hdM : d ≤ M) :
    -(lagBracketSlope M - lagBracketSlope d) ≤
      (((M : ℝ) - m) - psiRemainder m) * (((M : ℝ) - d) / ((d : ℝ) * M)) := by
  have hd1 : 1 ≤ d := le_trans hm hmd
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd1
  have hM0 : (0 : ℝ) < M := by exact_mod_cast (le_trans hd1 hdM)
  obtain ⟨hm1, _⟩ := lagBracketSlope_sub_bounds_of_monotone hd1 hdM
  obtain ⟨_, hl2⟩ := sub_le_log_div_and_log_div_le hd1 hdM
  have hmono : Chebyshev.psi m * (((M : ℝ) - d) / ((d : ℝ) * M)) ≤
      Chebyshev.psi d * (((M : ℝ) - d) / ((d : ℝ) * M)) := by
    have hsub0 : (0 : ℝ) ≤ (M : ℝ) - d := sub_nonneg.mpr (by exact_mod_cast hdM)
    exact mul_le_mul_of_nonneg_right (Chebyshev.psi_mono (by exact_mod_cast hmd)) (by positivity)
  have hpsi : Chebyshev.psi m = psiRemainder m + m := by
    rw [psiRemainder, chebyshevPsi_eq_psi]
    ring
  have heq : ((M : ℝ) - d) / d - Chebyshev.psi m * (((M : ℝ) - d) / ((d : ℝ) * M)) =
      (((M : ℝ) - m) - psiRemainder m) * (((M : ℝ) - d) / ((d : ℝ) * M)) := by
    rw [hpsi]
    field_simp
    ring
  linarith

/-- **Endpoint-monotone upper bound on `completedSourceObserverJetHistory M j` in the terminal
layer.** Unlike `abs_completedSourceObserverJetHistory_terminal_le`, which loses `O(L^2 / M)` by
applying Chebyshev's bound at every interior step `k`, this bound uses the monotonicity of `ψ` to
collapse all arithmetic dependence onto the single outer endpoint `max (psiRemainder M) 0`, with
denominator `M^2`. -/
theorem completedSourceObserverJetHistory_terminal_le_of_endpoint
    {M L j : ℕ} (hwindow : 2 * (L + 2) ≤ M)
    (hj : j ∈ Finset.Ico (M - 3 - L) (M - 3)) :
    completedSourceObserverJetHistory M j ≤
      (2 * max (psiRemainder M) 0 + 2 * (L : ℝ) +
          2 * (1 + |2 * Real.eulerMascheroniConstant|)) *
        (L : ℝ) ^ 2 / (M : ℝ) ^ 2 := by
  have hj' := Finset.mem_Ico.mp hj
  have hM3 : 3 ≤ M := by omega
  have hMpos : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hjrange : j ∈ Finset.range (M - 3) := Finset.mem_range.mpr hj'.2
  rw [completedSourceObserverJetHistory_eq_sum_mass_sub hM3 hjrange]
  have hterm (k : ℕ) (hk : k ∈ Finset.Ico (j + 1) (M - 2)) :
      completedSourceObserverJetMass M - completedSourceObserverJetMass (k + 2) ≤
        (2 * max (psiRemainder M) 0 + 2 * (L : ℝ) +
            2 * (1 + |2 * Real.eulerMascheroniConstant|)) *
          (L : ℝ) / (M : ℝ) ^ 2 := by
    have hk' := Finset.mem_Ico.mp hk
    have harch := (abs_le.mp
      (abs_observerJetMass_completedHarmonic_sub_lagBracketSlope_sub_le
        (k := k) (N := M - 2) (by omega))).2
    rw [show M - 2 + 2 = M by omega] at harch
    change (completedSourceObserverJetMass M - completedSourceObserverJetMass (k + 2)) -
      (lagBracketSlope M - lagBracketSlope (k + 2)) ≤
      (1 + |2 * Real.eulerMascheroniConstant|) *
        (1 / ((k : ℝ) + 2) - 1 / ((M - 2 : ℕ) + 2 : ℝ)) at harch
    have hMcast : ((M - 2 : ℕ) + 2 : ℝ) = (M : ℝ) := by
      exact_mod_cast (show M - 2 + 2 = M by omega)
    rw [hMcast] at harch
    have hk2pos : (0 : ℝ) < ((k + 2 : ℕ) : ℝ) := by positivity
    have hstep := lagBracketSlope_sub_le_psiRemainder_add_sub
      (d := k + 2) (M := M) (by omega) (by omega)
    have hgap_eq : 1 / ((k : ℝ) + 2) - 1 / (M : ℝ) =
        ((M : ℝ) - (k + 2 : ℕ)) / (((k + 2 : ℕ) : ℝ) * M) := by
      push_cast
      field_simp [hk2pos.ne', hMpos.ne']
    have hsubL : (M : ℝ) - (k + 2 : ℕ) ≤ L := by
      have hle : M ≤ L + (k + 2) := by omega
      have hcast : (M : ℝ) ≤ (L : ℝ) + (k + 2 : ℕ) := by exact_mod_cast hle
      linarith
    have hgap_le : ((M : ℝ) - (k + 2 : ℕ)) / (((k + 2 : ℕ) : ℝ) * M) ≤
        2 * (L : ℝ) / (M : ℝ) ^ 2 := by
      have hden : (M : ℝ) ^ 2 ≤ 2 * (((k + 2 : ℕ) : ℝ) * M) := by
        have hhalf : (M : ℝ) ≤ 2 * (k + 2 : ℕ) := by
          exact_mod_cast (show M ≤ 2 * (k + 2) by omega)
        nlinarith
      rw [div_le_div_iff₀ (mul_pos hk2pos hMpos) (sq_pos_of_pos hMpos)]
      have hsub0 : (0 : ℝ) ≤ (M : ℝ) - (k + 2 : ℕ) :=
        sub_nonneg.mpr (by exact_mod_cast (show k + 2 ≤ M by omega))
      nlinarith
    have hgap0 : 0 ≤ ((M : ℝ) - (k + 2 : ℕ)) / (((k + 2 : ℕ) : ℝ) * M) := by
      have : (0 : ℝ) ≤ (M : ℝ) - (k + 2 : ℕ) :=
        sub_nonneg.mpr (by exact_mod_cast (show k + 2 ≤ M by omega))
      positivity
    have hpsi_le : psiRemainder M + ((M : ℝ) - (k + 2 : ℕ)) ≤
        max (psiRemainder M) 0 + L := by
      linarith [le_max_left (psiRemainder M) 0]
    have hlag_bound : lagBracketSlope M - lagBracketSlope (k + 2) ≤
        (max (psiRemainder M) 0 + L) * (2 * (L : ℝ) / (M : ℝ) ^ 2) := by
      refine hstep.trans ?_
      exact mul_le_mul hpsi_le hgap_le hgap0 (by positivity)
    have harch_bound : (1 + |2 * Real.eulerMascheroniConstant|) *
        (1 / ((k : ℝ) + 2) - 1 / (M : ℝ)) ≤
        (1 + |2 * Real.eulerMascheroniConstant|) * (2 * (L : ℝ) / (M : ℝ) ^ 2) := by
      rw [hgap_eq]
      exact mul_le_mul_of_nonneg_left hgap_le (by positivity)
    calc
      completedSourceObserverJetMass M - completedSourceObserverJetMass (k + 2) ≤
          (lagBracketSlope M - lagBracketSlope (k + 2)) +
            (1 + |2 * Real.eulerMascheroniConstant|) * (1 / ((k : ℝ) + 2) - 1 / (M : ℝ)) := by
        linarith
      _ ≤ (max (psiRemainder M) 0 + L) * (2 * (L : ℝ) / (M : ℝ) ^ 2) +
            (1 + |2 * Real.eulerMascheroniConstant|) * (2 * (L : ℝ) / (M : ℝ) ^ 2) :=
        add_le_add hlag_bound harch_bound
      _ = (2 * max (psiRemainder M) 0 + 2 * (L : ℝ) +
            2 * (1 + |2 * Real.eulerMascheroniConstant|)) *
          (L : ℝ) / (M : ℝ) ^ 2 := by ring
  have hcard : ((M - 2 - (j + 1) : ℕ) : ℝ) ≤ L := by
    exact_mod_cast (show M - 2 - (j + 1) ≤ L by omega)
  calc
    ∑ k ∈ Finset.Ico (j + 1) (M - 2),
        (completedSourceObserverJetMass M - completedSourceObserverJetMass (k + 2)) ≤
      ∑ _k ∈ Finset.Ico (j + 1) (M - 2),
        (2 * max (psiRemainder M) 0 + 2 * (L : ℝ) +
            2 * (1 + |2 * Real.eulerMascheroniConstant|)) *
          (L : ℝ) / (M : ℝ) ^ 2 := Finset.sum_le_sum hterm
    _ = ((M - 2 - (j + 1) : ℕ) : ℝ) *
        ((2 * max (psiRemainder M) 0 + 2 * (L : ℝ) +
            2 * (1 + |2 * Real.eulerMascheroniConstant|)) *
          (L : ℝ) / (M : ℝ) ^ 2) := by simp
    _ ≤ (L : ℝ) *
        ((2 * max (psiRemainder M) 0 + 2 * (L : ℝ) +
            2 * (1 + |2 * Real.eulerMascheroniConstant|)) *
          (L : ℝ) / (M : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = (2 * max (psiRemainder M) 0 + 2 * (L : ℝ) +
          2 * (1 + |2 * Real.eulerMascheroniConstant|)) *
        (L : ℝ) ^ 2 / (M : ℝ) ^ 2 := by ring

/-- **Endpoint-monotone lower bound on `completedSourceObserverJetHistory M j` in the terminal
layer.** Collapses all arithmetic dependence onto the single left-edge remainder
`max (-psiRemainder (M - 2 - L)) 0`, with denominator `M^2`. -/
theorem neg_completedSourceObserverJetHistory_terminal_le_of_endpoint
    {M L j : ℕ} (hwindow : 2 * (L + 2) ≤ M)
    (hj : j ∈ Finset.Ico (M - 3 - L) (M - 3)) :
    -completedSourceObserverJetHistory M j ≤
      (2 * max (-psiRemainder (M - 2 - L)) 0 + 2 * ((L : ℝ) + 2) +
          2 * (1 + |2 * Real.eulerMascheroniConstant|)) *
        (L : ℝ) ^ 2 / (M : ℝ) ^ 2 := by
  have hj' := Finset.mem_Ico.mp hj
  have hM3 : 3 ≤ M := by omega
  have hMpos : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hjrange : j ∈ Finset.range (M - 3) := Finset.mem_range.mpr hj'.2
  rw [completedSourceObserverJetHistory_eq_sum_mass_sub hM3 hjrange, ← Finset.sum_neg_distrib]
  have hterm (k : ℕ) (hk : k ∈ Finset.Ico (j + 1) (M - 2)) :
      -(completedSourceObserverJetMass M - completedSourceObserverJetMass (k + 2)) ≤
        (2 * max (-psiRemainder (M - 2 - L)) 0 + 2 * ((L : ℝ) + 2) +
            2 * (1 + |2 * Real.eulerMascheroniConstant|)) *
          (L : ℝ) / (M : ℝ) ^ 2 := by
    have hk' := Finset.mem_Ico.mp hk
    have harch := (abs_le.mp
      (abs_observerJetMass_completedHarmonic_sub_lagBracketSlope_sub_le
        (k := k) (N := M - 2) (by omega))).1
    rw [show M - 2 + 2 = M by omega] at harch
    change -((1 + |2 * Real.eulerMascheroniConstant|) *
        (1 / ((k : ℝ) + 2) - 1 / ((M - 2 : ℕ) + 2 : ℝ))) ≤
      (completedSourceObserverJetMass M - completedSourceObserverJetMass (k + 2)) -
        (lagBracketSlope M - lagBracketSlope (k + 2)) at harch
    have hMcast : ((M - 2 : ℕ) + 2 : ℝ) = (M : ℝ) := by
      exact_mod_cast (show M - 2 + 2 = M by omega)
    rw [hMcast] at harch
    have hk2pos : (0 : ℝ) < ((k + 2 : ℕ) : ℝ) := by positivity
    have hstep := neg_lagBracketSlope_sub_le_of_le
      (m := M - 2 - L) (d := k + 2) (M := M) (by omega) (by omega) (by omega)
    have hgap_eq : 1 / ((k : ℝ) + 2) - 1 / (M : ℝ) =
        ((M : ℝ) - (k + 2 : ℕ)) / (((k + 2 : ℕ) : ℝ) * M) := by
      push_cast
      field_simp [hk2pos.ne', hMpos.ne']
    have hsubL : (M : ℝ) - (k + 2 : ℕ) ≤ L := by
      have hle : M ≤ L + (k + 2) := by omega
      have hcast : (M : ℝ) ≤ (L : ℝ) + (k + 2 : ℕ) := by exact_mod_cast hle
      linarith
    have hgap_le : ((M : ℝ) - (k + 2 : ℕ)) / (((k + 2 : ℕ) : ℝ) * M) ≤
        2 * (L : ℝ) / (M : ℝ) ^ 2 := by
      have hden : (M : ℝ) ^ 2 ≤ 2 * (((k + 2 : ℕ) : ℝ) * M) := by
        have hhalf : (M : ℝ) ≤ 2 * (k + 2 : ℕ) := by
          exact_mod_cast (show M ≤ 2 * (k + 2) by omega)
        nlinarith
      rw [div_le_div_iff₀ (mul_pos hk2pos hMpos) (sq_pos_of_pos hMpos)]
      have hsub0 : (0 : ℝ) ≤ (M : ℝ) - (k + 2 : ℕ) :=
        sub_nonneg.mpr (by exact_mod_cast (show k + 2 ≤ M by omega))
      nlinarith
    have hgap0 : 0 ≤ ((M : ℝ) - (k + 2 : ℕ)) / (((k + 2 : ℕ) : ℝ) * M) := by
      have : (0 : ℝ) ≤ (M : ℝ) - (k + 2 : ℕ) :=
        sub_nonneg.mpr (by exact_mod_cast (show k + 2 ≤ M by omega))
      positivity
    have hsubM : (M : ℝ) - (M - 2 - L : ℕ) = (L : ℝ) + 2 := by
      have hle : L + 2 ≤ M := by omega
      have hcast : ((M - 2 - L : ℕ) : ℝ) = (M : ℝ) - ((L : ℝ) + 2) := by
        rw [show M - 2 - L = M - (L + 2) by omega, Nat.cast_sub hle]
        push_cast
        ring
      linarith
    have hpsi_le : ((M : ℝ) - (M - 2 - L : ℕ)) - psiRemainder (M - 2 - L) ≤
        max (-psiRemainder (M - 2 - L)) 0 + ((L : ℝ) + 2) := by
      linarith [hsubM, le_max_left (-psiRemainder (M - 2 - L)) 0]
    have hlag_bound : -(lagBracketSlope M - lagBracketSlope (k + 2)) ≤
        (max (-psiRemainder (M - 2 - L)) 0 + ((L : ℝ) + 2)) * (2 * (L : ℝ) / (M : ℝ) ^ 2) := by
      refine hstep.trans ?_
      exact mul_le_mul hpsi_le hgap_le hgap0 (by positivity)
    have harch_bound : (1 + |2 * Real.eulerMascheroniConstant|) *
        (1 / ((k : ℝ) + 2) - 1 / (M : ℝ)) ≤
        (1 + |2 * Real.eulerMascheroniConstant|) * (2 * (L : ℝ) / (M : ℝ) ^ 2) := by
      rw [hgap_eq]
      exact mul_le_mul_of_nonneg_left hgap_le (by positivity)
    calc
      -(completedSourceObserverJetMass M - completedSourceObserverJetMass (k + 2)) ≤
          -(lagBracketSlope M - lagBracketSlope (k + 2)) +
            (1 + |2 * Real.eulerMascheroniConstant|) * (1 / ((k : ℝ) + 2) - 1 / (M : ℝ)) := by
        linarith
      _ ≤ (max (-psiRemainder (M - 2 - L)) 0 + ((L : ℝ) + 2)) * (2 * (L : ℝ) / (M : ℝ) ^ 2) +
            (1 + |2 * Real.eulerMascheroniConstant|) * (2 * (L : ℝ) / (M : ℝ) ^ 2) :=
        add_le_add hlag_bound harch_bound
      _ = (2 * max (-psiRemainder (M - 2 - L)) 0 + 2 * ((L : ℝ) + 2) +
            2 * (1 + |2 * Real.eulerMascheroniConstant|)) *
          (L : ℝ) / (M : ℝ) ^ 2 := by ring
  have hcard : ((M - 2 - (j + 1) : ℕ) : ℝ) ≤ L := by
    exact_mod_cast (show M - 2 - (j + 1) ≤ L by omega)
  calc
    ∑ k ∈ Finset.Ico (j + 1) (M - 2),
        -(completedSourceObserverJetMass M - completedSourceObserverJetMass (k + 2)) ≤
      ∑ _k ∈ Finset.Ico (j + 1) (M - 2),
        (2 * max (-psiRemainder (M - 2 - L)) 0 + 2 * ((L : ℝ) + 2) +
            2 * (1 + |2 * Real.eulerMascheroniConstant|)) *
          (L : ℝ) / (M : ℝ) ^ 2 := Finset.sum_le_sum hterm
    _ = ((M - 2 - (j + 1) : ℕ) : ℝ) *
        ((2 * max (-psiRemainder (M - 2 - L)) 0 + 2 * ((L : ℝ) + 2) +
            2 * (1 + |2 * Real.eulerMascheroniConstant|)) *
          (L : ℝ) / (M : ℝ) ^ 2) := by simp
    _ ≤ (L : ℝ) *
        ((2 * max (-psiRemainder (M - 2 - L)) 0 + 2 * ((L : ℝ) + 2) +
            2 * (1 + |2 * Real.eulerMascheroniConstant|)) *
          (L : ℝ) / (M : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = (2 * max (-psiRemainder (M - 2 - L)) 0 + 2 * ((L : ℝ) + 2) +
          2 * (1 + |2 * Real.eulerMascheroniConstant|)) *
        (L : ℝ) ^ 2 / (M : ℝ) ^ 2 := by ring

/-- **Quartic terminal positive-action bound depending only on the single outer endpoint
`max (psiRemainder M) 0`.** -/
theorem completedSourceObserverJetTerminalPositiveAction_le_quartic_of_endpoint
    {M L : ℕ} (hwindow : 2 * (L + 2) ≤ M) :
    completedSourceObserverJetTerminalPositiveAction M L ≤
      4 * (max (psiRemainder M) 0 + (L : ℝ) + (1 + |2 * Real.eulerMascheroniConstant|)) *
        (L : ℝ) ^ 3 / ((M : ℝ) ^ 2 * Real.sqrt (M : ℝ)) := by
  have hM : 0 < (M : ℝ) := by exact_mod_cast (show 0 < M by omega)
  have hsM : 0 < Real.sqrt (M : ℝ) := Real.sqrt_pos.mpr hM
  have hLle : L ≤ M - 3 := by omega
  have hterm (j : ℕ) (hj : j ∈ Finset.Ico (M - 3 - L) (M - 3)) :
      max (completedSourceObserverJetHistory M j) 0 / Real.sqrt (j + 1 : ℕ) ≤
        4 * (max (psiRemainder M) 0 + (L : ℝ) + (1 + |2 * Real.eulerMascheroniConstant|)) *
          (L : ℝ) ^ 2 / ((M : ℝ) ^ 2 * Real.sqrt (M : ℝ)) := by
    have hj' := Finset.mem_Ico.mp hj
    have hhalf : (M : ℝ) ≤ 2 * (j + 1 : ℕ) := by
      exact_mod_cast (show M ≤ 2 * (j + 1) by omega)
    have hsj : 0 < Real.sqrt (j + 1 : ℕ) := Real.sqrt_pos.mpr (by positivity)
    have hsqrt : Real.sqrt (M : ℝ) ≤ 2 * Real.sqrt (j + 1 : ℕ) := by
      apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
      rw [mul_pow, Real.sq_sqrt hM.le, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ (j + 1 : ℕ))]
      nlinarith
    have hinv : 1 / Real.sqrt (j + 1 : ℕ) ≤ 2 / Real.sqrt (M : ℝ) :=
      (div_le_div_iff₀ hsj hsM).mpr (by simpa using hsqrt)
    have hhist : max (completedSourceObserverJetHistory M j) 0 ≤
        (2 * max (psiRemainder M) 0 + 2 * (L : ℝ) +
            2 * (1 + |2 * Real.eulerMascheroniConstant|)) *
          (L : ℝ) ^ 2 / (M : ℝ) ^ 2 := by
      apply max_le
      · exact completedSourceObserverJetHistory_terminal_le_of_endpoint hwindow hj
      · positivity
    calc
      _ = max (completedSourceObserverJetHistory M j) 0 * (1 / Real.sqrt (j + 1 : ℕ)) := by ring
      _ ≤ ((2 * max (psiRemainder M) 0 + 2 * (L : ℝ) +
              2 * (1 + |2 * Real.eulerMascheroniConstant|)) *
            (L : ℝ) ^ 2 / (M : ℝ) ^ 2) * (2 / Real.sqrt (M : ℝ)) :=
        mul_le_mul hhist hinv (by positivity) (by positivity)
      _ = _ := by ring
  unfold completedSourceObserverJetTerminalPositiveAction
  calc
    _ ≤ ∑ _j ∈ Finset.Ico (M - 3 - L) (M - 3),
        4 * (max (psiRemainder M) 0 + (L : ℝ) + (1 + |2 * Real.eulerMascheroniConstant|)) *
          (L : ℝ) ^ 2 / ((M : ℝ) ^ 2 * Real.sqrt (M : ℝ)) := Finset.sum_le_sum hterm
    _ = (L : ℝ) *
        (4 * (max (psiRemainder M) 0 + (L : ℝ) + (1 + |2 * Real.eulerMascheroniConstant|)) *
          (L : ℝ) ^ 2 / ((M : ℝ) ^ 2 * Real.sqrt (M : ℝ))) := by simp [Nat.sub_sub_self hLle]
    _ = _ := by ring

/-- **Quartic terminal negative-action bound depending only on the single left-edge remainder
`max (-psiRemainder (M - 2 - L)) 0`.** -/
theorem completedSourceObserverJetTerminalNegativeAction_le_quartic_of_endpoint
    {M L : ℕ} (hwindow : 2 * (L + 2) ≤ M) :
    completedSourceObserverJetTerminalNegativeAction M L ≤
      4 * (max (-psiRemainder (M - 2 - L)) 0 + ((L : ℝ) + 2) +
          (1 + |2 * Real.eulerMascheroniConstant|)) *
        (L : ℝ) ^ 3 / ((M : ℝ) ^ 2 * Real.sqrt (M : ℝ)) := by
  have hM : 0 < (M : ℝ) := by exact_mod_cast (show 0 < M by omega)
  have hsM : 0 < Real.sqrt (M : ℝ) := Real.sqrt_pos.mpr hM
  have hLle : L ≤ M - 3 := by omega
  have hterm (j : ℕ) (hj : j ∈ Finset.Ico (M - 3 - L) (M - 3)) :
      max (-completedSourceObserverJetHistory M j) 0 / Real.sqrt (j + 1 : ℕ) ≤
        4 * (max (-psiRemainder (M - 2 - L)) 0 + ((L : ℝ) + 2) +
            (1 + |2 * Real.eulerMascheroniConstant|)) *
          (L : ℝ) ^ 2 / ((M : ℝ) ^ 2 * Real.sqrt (M : ℝ)) := by
    have hj' := Finset.mem_Ico.mp hj
    have hhalf : (M : ℝ) ≤ 2 * (j + 1 : ℕ) := by
      exact_mod_cast (show M ≤ 2 * (j + 1) by omega)
    have hsj : 0 < Real.sqrt (j + 1 : ℕ) := Real.sqrt_pos.mpr (by positivity)
    have hsqrt : Real.sqrt (M : ℝ) ≤ 2 * Real.sqrt (j + 1 : ℕ) := by
      apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
      rw [mul_pow, Real.sq_sqrt hM.le, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ (j + 1 : ℕ))]
      nlinarith
    have hinv : 1 / Real.sqrt (j + 1 : ℕ) ≤ 2 / Real.sqrt (M : ℝ) :=
      (div_le_div_iff₀ hsj hsM).mpr (by simpa using hsqrt)
    have hhist : max (-completedSourceObserverJetHistory M j) 0 ≤
        (2 * max (-psiRemainder (M - 2 - L)) 0 + 2 * ((L : ℝ) + 2) +
            2 * (1 + |2 * Real.eulerMascheroniConstant|)) *
          (L : ℝ) ^ 2 / (M : ℝ) ^ 2 := by
      apply max_le
      · exact neg_completedSourceObserverJetHistory_terminal_le_of_endpoint hwindow hj
      · positivity
    calc
      _ = max (-completedSourceObserverJetHistory M j) 0 * (1 / Real.sqrt (j + 1 : ℕ)) := by ring
      _ ≤ ((2 * max (-psiRemainder (M - 2 - L)) 0 + 2 * ((L : ℝ) + 2) +
              2 * (1 + |2 * Real.eulerMascheroniConstant|)) *
            (L : ℝ) ^ 2 / (M : ℝ) ^ 2) * (2 / Real.sqrt (M : ℝ)) :=
        mul_le_mul hhist hinv (by positivity) (by positivity)
      _ = _ := by ring
  unfold completedSourceObserverJetTerminalNegativeAction
  calc
    _ ≤ ∑ _j ∈ Finset.Ico (M - 3 - L) (M - 3),
        4 * (max (-psiRemainder (M - 2 - L)) 0 + ((L : ℝ) + 2) +
            (1 + |2 * Real.eulerMascheroniConstant|)) *
          (L : ℝ) ^ 2 / ((M : ℝ) ^ 2 * Real.sqrt (M : ℝ)) := Finset.sum_le_sum hterm
    _ = (L : ℝ) *
        (4 * (max (-psiRemainder (M - 2 - L)) 0 + ((L : ℝ) + 2) +
            (1 + |2 * Real.eulerMascheroniConstant|)) *
          (L : ℝ) ^ 2 / ((M : ℝ) ^ 2 * Real.sqrt (M : ℝ))) := by simp [Nat.sub_sub_self hLle]
    _ = _ := by ring

/-- **Linear terminal positive-action bound up to `L^4 ≤ M^3 √M` (`L ≤ M^{7/8}`) whenever
`psiRemainder M ≤ K * L`.** In particular, at every aperture `M` where `psiRemainder M ≤ 0`
(`K = 0`), the terminal positive action is linear in `M` for widths up to `M^{7/8}` (including the
explicit schedule `M = N^8, L = N^7`), strictly surpassing the `M^{5/6}` (`M = N^6, L = N^5`)
barrier of `SuzukiObserverJetTerminalLayer`. -/
theorem completedSourceObserverJetTerminalPositiveAction_le_linear_of_psiRemainder_le_mul
    {M L : ℕ} {K : ℝ} (hK0 : 0 ≤ K) (hL1 : 1 ≤ L) (hwindow : 2 * (L + 2) ≤ M)
    (hpsi : psiRemainder M ≤ K * (L : ℝ))
    (hscale : (L : ℝ) ^ 4 ≤ (M : ℝ) ^ 3 * Real.sqrt (M : ℝ)) :
    completedSourceObserverJetTerminalPositiveAction M L ≤
      4 * (K + 2 + |2 * Real.eulerMascheroniConstant|) * (M : ℝ) := by
  have hM : 0 < (M : ℝ) := by exact_mod_cast (show 0 < M by omega)
  have hsM : 0 < Real.sqrt (M : ℝ) := Real.sqrt_pos.mpr hM
  have hLpos : (1 : ℝ) ≤ L := by exact_mod_cast hL1
  have hmax : max (psiRemainder M) 0 ≤ K * (L : ℝ) :=
    max_le hpsi (mul_nonneg hK0 (Nat.cast_nonneg L))
  have hcoeff : max (psiRemainder M) 0 + (L : ℝ) + (1 + |2 * Real.eulerMascheroniConstant|) ≤
      (K + 2 + |2 * Real.eulerMascheroniConstant|) * (L : ℝ) := by
    have : 1 + |2 * Real.eulerMascheroniConstant| ≤
        (1 + |2 * Real.eulerMascheroniConstant|) * (L : ℝ) := by
      nlinarith [abs_nonneg (2 * Real.eulerMascheroniConstant)]
    linarith
  calc
    completedSourceObserverJetTerminalPositiveAction M L ≤
        4 * (max (psiRemainder M) 0 + (L : ℝ) + (1 + |2 * Real.eulerMascheroniConstant|)) *
          (L : ℝ) ^ 3 / ((M : ℝ) ^ 2 * Real.sqrt (M : ℝ)) :=
      completedSourceObserverJetTerminalPositiveAction_le_quartic_of_endpoint hwindow
    _ ≤ 4 * ((K + 2 + |2 * Real.eulerMascheroniConstant|) * (L : ℝ)) *
          (L : ℝ) ^ 3 / ((M : ℝ) ^ 2 * Real.sqrt (M : ℝ)) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      nlinarith [pow_nonneg (Nat.cast_nonneg L : (0 : ℝ) ≤ L) 3]
    _ = 4 * (K + 2 + |2 * Real.eulerMascheroniConstant|) * (L : ℝ) ^ 4 /
          ((M : ℝ) ^ 2 * Real.sqrt (M : ℝ)) := by ring
    _ ≤ 4 * (K + 2 + |2 * Real.eulerMascheroniConstant|) *
          ((M : ℝ) ^ 3 * Real.sqrt (M : ℝ)) / ((M : ℝ) ^ 2 * Real.sqrt (M : ℝ)) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_left hscale (by positivity)
    _ = 4 * (K + 2 + |2 * Real.eulerMascheroniConstant|) * (M : ℝ) := by
      field_simp

/-- Explicit `M = N^8, L = N^7` specialization of the `M^{7/8}` terminal positive-action bound. -/
theorem completedSourceObserverJetTerminalPositiveAction_eighth_seventh_le
    {N : ℕ} {K : ℝ} (hK0 : 0 ≤ K) (hN : 3 ≤ N)
    (hpsi : psiRemainder (N ^ 8) ≤ K * (N ^ 7 : ℕ)) :
    completedSourceObserverJetTerminalPositiveAction (N ^ 8) (N ^ 7) ≤
      4 * (K + 2 + |2 * Real.eulerMascheroniConstant|) * (N ^ 8 : ℕ) := by
  have hN7 : 4 ≤ N ^ 7 := by
    calc 4 ≤ (3 : ℕ) ^ 7 := by norm_num
      _ ≤ N ^ 7 := by gcongr
  have hwindow : 2 * (N ^ 7 + 2) ≤ N ^ 8 := by
    rw [show N ^ 8 = N * N ^ 7 by ring]
    have hmul := Nat.mul_le_mul_right (N ^ 7) hN
    nlinarith
  have hsqrt : Real.sqrt (N ^ 8 : ℕ) = (N : ℝ) ^ 4 := by
    rw [Nat.cast_pow, show (N : ℝ) ^ 8 = ((N : ℝ) ^ 4) ^ 2 by ring,
      Real.sqrt_sq (by positivity)]
  apply completedSourceObserverJetTerminalPositiveAction_le_linear_of_psiRemainder_le_mul
    hK0 (by omega) hwindow hpsi
  apply le_of_eq
  rw [hsqrt]
  push_cast
  ring

/-- **Polynomial-schedule (`M = N^8, L = N^7`) positive interior action criterion for RH**
under `psiRemainder (N^8) ≤ K * N^7`. -/
theorem riemannHypothesis_of_completedSourceObserverJetInteriorPositive_eighth_seventh_linear
    {C K : ℝ} (hK0 : 0 ≤ K)
    (hpsi : ∀ N : ℕ, 3 ≤ N → psiRemainder (N ^ 8) ≤ K * (N ^ 7 : ℕ))
    (hinterior : ∀ N : ℕ, 3 ≤ N →
      completedSourceObserverJetInteriorPositiveAction (N ^ 8) (N ^ 7) ≤ C * (N ^ 8 : ℕ)) :
    RiemannHypothesis := by
  obtain ⟨B, _hB0, hB⟩ := exists_mobiusDivisorSquareRootAbel_upper_positiveHistory
  rw [riemannHypothesis_iff_mobiusDivisorSquareRootAbel_pow_bddAbove (m := 8) (by omega)]
  obtain ⟨M₀, hM2, hM3⟩ :
      ∃ M₀ : ℝ, mobiusDivisorSquareRootAbelMoment (2 ^ 8) / (2 ^ 8 : ℕ) ≤ M₀ ∧
        B + (3 / 8 : ℝ) * (max 0 C + 4 * (K + 2 + |2 * Real.eulerMascheroniConstant|)) ≤ M₀ :=
    ⟨max (mobiusDivisorSquareRootAbelMoment (2 ^ 8) / (2 ^ 8 : ℕ))
      (B + (3 / 8 : ℝ) * (max 0 C + 4 * (K + 2 + |2 * Real.eulerMascheroniConstant|))),
      le_max_left _ _, le_max_right _ _⟩
  refine ⟨M₀, fun N hN2 => ?_⟩
  have hN_ge_2 : 2 ≤ N := by
    by_contra hlt
    have hle1 : N ≤ 1 := by omega
    have hpow : N ^ 8 ≤ 1 ^ 8 := Nat.pow_le_pow_left hle1 8
    omega
  by_cases hN_eq_2 : N = 2
  · subst N
    exact hM2
  · clear hM2
    have hN : 3 ≤ N := by omega
    have hN8 : 3 ≤ N ^ 8 := by
      calc 3 ≤ 3 ^ 8 := by norm_num
        _ ≤ N ^ 8 := Nat.pow_le_pow_left hN 8
    have hpos : (0 : ℝ) < (N ^ 8 : ℕ) := by exact_mod_cast (show 0 < N ^ 8 by omega)
    have htail := completedSourceObserverJetTerminalPositiveAction_eighth_seventh_le
      hK0 hN (hpsi N hN)
    have hi : completedSourceObserverJetInteriorPositiveAction (N ^ 8) (N ^ 7) ≤
        max 0 C * (N ^ 8 : ℕ) :=
      (hinterior N hN).trans (mul_le_mul_of_nonneg_right (le_max_right 0 C) (Nat.cast_nonneg _))
    have hfull : completedSourceObserverJetPositiveHistoryAction (N ^ 8) ≤
        (max 0 C + 4 * (K + 2 + |2 * Real.eulerMascheroniConstant|)) * (N ^ 8 : ℕ) := by
      rw [completedSourceObserverJetPositiveHistoryAction_eq_interior_add_terminal (N ^ 8) (N ^ 7)]
      linarith
    have h1 := hB (N ^ 8) hN8
    have hdiv : mobiusDivisorSquareRootAbelMoment (N ^ 8) / (N ^ 8 : ℕ) ≤
        B + (3 / 8 : ℝ) * (max 0 C + 4 * (K + 2 + |2 * Real.eulerMascheroniConstant|)) :=
      (div_le_iff₀ hpos).mpr (by linarith)
    exact hdiv.trans hM3

/-- **Linear terminal negative-action bound up to `L^4 ≤ M^3 √M` (`L ≤ M^{7/8}`) whenever
`-psiRemainder (M - 2 - L) ≤ K * L`.** -/
theorem completedSourceObserverJetTerminalNegativeAction_le_linear_of_neg_psiRemainder_le_mul
    {M L : ℕ} {K : ℝ} (hK0 : 0 ≤ K) (hL1 : 1 ≤ L) (hwindow : 2 * (L + 2) ≤ M)
    (hpsi : -psiRemainder (M - 2 - L) ≤ K * (L : ℝ))
    (hscale : (L : ℝ) ^ 4 ≤ (M : ℝ) ^ 3 * Real.sqrt (M : ℝ)) :
    completedSourceObserverJetTerminalNegativeAction M L ≤
      4 * (K + 4 + |2 * Real.eulerMascheroniConstant|) * (M : ℝ) := by
  have hM : 0 < (M : ℝ) := by exact_mod_cast (show 0 < M by omega)
  have hsM : 0 < Real.sqrt (M : ℝ) := Real.sqrt_pos.mpr hM
  have hLpos : (1 : ℝ) ≤ L := by exact_mod_cast hL1
  have hmax : max (-psiRemainder (M - 2 - L)) 0 ≤ K * (L : ℝ) :=
    max_le hpsi (mul_nonneg hK0 (Nat.cast_nonneg L))
  have hcoeff : max (-psiRemainder (M - 2 - L)) 0 + ((L : ℝ) + 2) +
        (1 + |2 * Real.eulerMascheroniConstant|) ≤
      (K + 4 + |2 * Real.eulerMascheroniConstant|) * (L : ℝ) := by
    have : 1 + |2 * Real.eulerMascheroniConstant| ≤
        (1 + |2 * Real.eulerMascheroniConstant|) * (L : ℝ) := by
      nlinarith [abs_nonneg (2 * Real.eulerMascheroniConstant)]
    linarith
  calc
    completedSourceObserverJetTerminalNegativeAction M L ≤
        4 * (max (-psiRemainder (M - 2 - L)) 0 + ((L : ℝ) + 2) +
            (1 + |2 * Real.eulerMascheroniConstant|)) *
          (L : ℝ) ^ 3 / ((M : ℝ) ^ 2 * Real.sqrt (M : ℝ)) :=
      completedSourceObserverJetTerminalNegativeAction_le_quartic_of_endpoint hwindow
    _ ≤ 4 * ((K + 4 + |2 * Real.eulerMascheroniConstant|) * (L : ℝ)) *
          (L : ℝ) ^ 3 / ((M : ℝ) ^ 2 * Real.sqrt (M : ℝ)) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      nlinarith [pow_nonneg (Nat.cast_nonneg L : (0 : ℝ) ≤ L) 3]
    _ = 4 * (K + 4 + |2 * Real.eulerMascheroniConstant|) * (L : ℝ) ^ 4 /
          ((M : ℝ) ^ 2 * Real.sqrt (M : ℝ)) := by ring
    _ ≤ 4 * (K + 4 + |2 * Real.eulerMascheroniConstant|) *
          ((M : ℝ) ^ 3 * Real.sqrt (M : ℝ)) / ((M : ℝ) ^ 2 * Real.sqrt (M : ℝ)) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_left hscale (by positivity)
    _ = 4 * (K + 4 + |2 * Real.eulerMascheroniConstant|) * (M : ℝ) := by
      field_simp

/-- Explicit `M = N^8, L = N^7` specialization of the `M^{7/8}` terminal negative-action bound. -/
theorem completedSourceObserverJetTerminalNegativeAction_eighth_seventh_le
    {N : ℕ} {K : ℝ} (hK0 : 0 ≤ K) (hN : 3 ≤ N)
    (hpsi : -psiRemainder (N ^ 8 - 2 - N ^ 7) ≤ K * (N ^ 7 : ℕ)) :
    completedSourceObserverJetTerminalNegativeAction (N ^ 8) (N ^ 7) ≤
      4 * (K + 4 + |2 * Real.eulerMascheroniConstant|) * (N ^ 8 : ℕ) := by
  have hN7 : 4 ≤ N ^ 7 := by
    calc 4 ≤ (3 : ℕ) ^ 7 := by norm_num
      _ ≤ N ^ 7 := by gcongr
  have hwindow : 2 * (N ^ 7 + 2) ≤ N ^ 8 := by
    rw [show N ^ 8 = N * N ^ 7 by ring]
    have hmul := Nat.mul_le_mul_right (N ^ 7) hN
    nlinarith
  have hsqrt : Real.sqrt (N ^ 8 : ℕ) = (N : ℝ) ^ 4 := by
    rw [Nat.cast_pow, show (N : ℝ) ^ 8 = ((N : ℝ) ^ 4) ^ 2 by ring,
      Real.sqrt_sq (by positivity)]
  apply completedSourceObserverJetTerminalNegativeAction_le_linear_of_neg_psiRemainder_le_mul
    hK0 (by omega) hwindow hpsi
  apply le_of_eq
  rw [hsqrt]
  push_cast
  ring

/-- **Polynomial-schedule (`M = N^8, L = N^7`) negative interior action criterion for RH**
under `-psiRemainder (N^8 - 2 - N^7) ≤ K * N^7`. -/
theorem riemannHypothesis_of_completedSourceObserverJetInteriorNegative_eighth_seventh_linear
    {C K : ℝ} (hK0 : 0 ≤ K)
    (hpsi : ∀ N : ℕ, 3 ≤ N → -psiRemainder (N ^ 8 - 2 - N ^ 7) ≤ K * (N ^ 7 : ℕ))
    (hinterior : ∀ N : ℕ, 3 ≤ N →
      completedSourceObserverJetInteriorNegativeAction (N ^ 8) (N ^ 7) ≤ C * (N ^ 8 : ℕ)) :
    RiemannHypothesis := by
  obtain ⟨B, _hB0, hB⟩ := exists_mobiusDivisorSquareRootAbel_lower_negativeHistory
  rw [riemannHypothesis_iff_mobiusDivisorSquareRootAbel_pow_bddBelow (m := 8) (by omega)]
  obtain ⟨M₀, hM2, hM3⟩ :
      ∃ M₀ : ℝ, -M₀ ≤ mobiusDivisorSquareRootAbelMoment (2 ^ 8) / (2 ^ 8 : ℕ) ∧
        B + (3 / 8 : ℝ) * (max 0 C + 4 * (K + 4 + |2 * Real.eulerMascheroniConstant|)) ≤ M₀ :=
    ⟨max (-mobiusDivisorSquareRootAbelMoment (2 ^ 8) / (2 ^ 8 : ℕ))
      (B + (3 / 8 : ℝ) * (max 0 C + 4 * (K + 4 + |2 * Real.eulerMascheroniConstant|))),
      by
        have h := neg_le_neg (le_max_left (-mobiusDivisorSquareRootAbelMoment (2 ^ 8) / (2 ^ 8 : ℕ))
          (B + (3 / 8 : ℝ) * (max 0 C + 4 * (K + 4 + |2 * Real.eulerMascheroniConstant|))))
        simpa [neg_div] using h,
      le_max_right _ _⟩
  refine ⟨-M₀, fun N hN2 => ?_⟩
  have hN_ge_2 : 2 ≤ N := by
    by_contra hlt
    have hle1 : N ≤ 1 := by omega
    have hpow : N ^ 8 ≤ 1 ^ 8 := Nat.pow_le_pow_left hle1 8
    omega
  by_cases hN_eq_2 : N = 2
  · subst N
    exact hM2
  · clear hM2
    have hN : 3 ≤ N := by omega
    have hN8 : 3 ≤ N ^ 8 := by
      calc 3 ≤ 3 ^ 8 := by norm_num
        _ ≤ N ^ 8 := Nat.pow_le_pow_left hN 8
    have hpos : (0 : ℝ) < (N ^ 8 : ℕ) := by exact_mod_cast (show 0 < N ^ 8 by omega)
    have htail := completedSourceObserverJetTerminalNegativeAction_eighth_seventh_le
      hK0 hN (hpsi N hN)
    have hi : completedSourceObserverJetInteriorNegativeAction (N ^ 8) (N ^ 7) ≤
        max 0 C * (N ^ 8 : ℕ) :=
      (hinterior N hN).trans (mul_le_mul_of_nonneg_right (le_max_right 0 C) (Nat.cast_nonneg _))
    have hfull : completedSourceObserverJetNegativeHistoryAction (N ^ 8) ≤
        (max 0 C + 4 * (K + 4 + |2 * Real.eulerMascheroniConstant|)) * (N ^ 8 : ℕ) := by
      rw [completedSourceObserverJetNegativeHistoryAction_eq_interior_add_terminal (N ^ 8) (N ^ 7)]
      linarith
    have h1 := hB (N ^ 8) hN8
    have hdiv : -(B + (3 / 8 : ℝ) * (max 0 C + 4 * (K + 4 + |2 * Real.eulerMascheroniConstant|))) ≤
        mobiusDivisorSquareRootAbelMoment (N ^ 8) / (N ^ 8 : ℕ) :=
      (le_div_iff₀ hpos).mpr (by linarith)
    exact (neg_le_neg hM3).trans hdiv

end GaloisForLFunctions.RHTower
