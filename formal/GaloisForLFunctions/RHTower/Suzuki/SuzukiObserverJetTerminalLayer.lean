import GaloisForLFunctions.RHTower.Suzuki.SuzukiObserverJetPositiveCurvature
import GaloisForLFunctions.RHTower.Suzuki.SuzukiObserverJetLinearActionClassification

/-!
# Unconditional control of a growing terminal history region

The elementary Chebyshev bound gives `|q(k)| <= A/(k+1)` for the literal
completed charge, with `A = 8 + |2 gamma|`. Its exact second-history tail then
controls the last `L` positive-history coordinates by `8 A L^3/(M sqrt M)`,
provided `2(L+2) <= M`.

This is linear in `M` when `L^3 <= M^2 sqrt M`, including the explicit growing
family `M=N^6`, `L=N^5`, `N>=3`. The full action splits into this controlled
terminal region and an interior prefix. A linear bound for the interior prefix
along a permitted width schedule implies RH. That interior bound remains open.
-/

open Set Filter Topology
open scoped BigOperators
noncomputable section


namespace GaloisForLFunctions.RHTower

open _root_.RHTower GaloisForLFunctions.HTGeometry

def completedSourceObserverJetChargeConstant : ℝ :=
  8 + |2 * Real.eulerMascheroniConstant|

theorem completedSourceObserverJetChargeConstant_nonneg :
    0 ≤ completedSourceObserverJetChargeConstant := by
  unfold completedSourceObserverJetChargeConstant
  positivity

theorem abs_completedPrimePolarGammaHarmonicCharge_le_reciprocal (k : ℕ) :
    |completedPrimePolarGammaHarmonicCharge k| ≤
      completedSourceObserverJetChargeConstant / ((k : ℝ) + 1) := by
  have h1 : 0 < (k : ℝ) + 1 := by positivity
  have h2 : 0 < (k : ℝ) + 2 := by positivity
  have hgap : 1 / ((k : ℝ) + 1) - 1 / ((k : ℝ) + 2) =
      1 / (((k : ℝ) + 1) * ((k : ℝ) + 2)) := by
    field_simp
    ring
  have hR := abs_psiRemainder_le (k + 1)
  have hnum : |psiRemainder (k + 1) + 2 * Real.eulerMascheroniConstant| ≤
      completedSourceObserverJetChargeConstant * ((k : ℝ) + 2) := by
    have htri := abs_add_le (psiRemainder (k + 1)) (2 * Real.eulerMascheroniConstant)
    have hg := mul_nonneg (abs_nonneg (2 * Real.eulerMascheroniConstant)) h1.le
    unfold completedSourceObserverJetChargeConstant
    push_cast at hR
    nlinarith
  rw [completedPrimePolarGammaHarmonicCharge, hgap, ← div_eq_mul_one_div,
    abs_div, abs_of_pos (mul_pos h1 h2)]
  calc
    _ ≤ (completedSourceObserverJetChargeConstant * ((k : ℝ) + 2)) /
        (((k : ℝ) + 1) * ((k : ℝ) + 2)) :=
      div_le_div_of_nonneg_right hnum (mul_pos h1 h2).le
    _ = _ := by field_simp

def completedSourceObserverJetTerminalPositiveAction (M L : ℕ) : ℝ :=
  ∑ j ∈ Finset.Ico (M - 3 - L) (M - 3),
    max (completedSourceObserverJetHistory M j) 0 / Real.sqrt (j + 1 : ℕ)

def completedSourceObserverJetInteriorPositiveAction (M L : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (M - 3 - L),
    max (completedSourceObserverJetHistory M j) 0 / Real.sqrt (j + 1 : ℕ)

theorem abs_completedSourceObserverJetHistory_terminal_le
    {M L j : ℕ} (hwindow : 2 * (L + 2) ≤ M)
    (hj : j ∈ Finset.Ico (M - 3 - L) (M - 3)) :
    |completedSourceObserverJetHistory M j| ≤
      4 * completedSourceObserverJetChargeConstant * (L : ℝ) ^ 2 / (M : ℝ) := by
  have hj' := Finset.mem_Ico.mp hj
  have hL : 1 ≤ L := by omega
  have hM : 0 < (M : ℝ) := by exact_mod_cast (show 0 < M by omega)
  have hA := completedSourceObserverJetChargeConstant_nonneg
  change |observerJetSecondHistory
    (observerJetResidual completedPrimePolarGammaHarmonicCharge (M - 2)) j| ≤ _
  rw [observerJetResidual_history_eq_tail _ _ _ (by omega) (by omega),
    show M - 2 + 1 = M - 1 by omega]
  have hterm (k : ℕ) (hk : k ∈ Finset.Ico (j + 1) (M - 1)) :
      |((k - (j + 1) : ℕ) : ℝ) * completedPrimePolarGammaHarmonicCharge k| ≤
        (L : ℝ) * (2 * completedSourceObserverJetChargeConstant / (M : ℝ)) := by
    have hk' := Finset.mem_Ico.mp hk
    have hw : ((k - (j + 1) : ℕ) : ℝ) ≤ (L : ℝ) := by
      exact_mod_cast (show k - (j + 1) ≤ L by omega)
    have hhalf : (M : ℝ) ≤ 2 * ((k : ℝ) + 1) := by
      exact_mod_cast (show M ≤ 2 * (k + 1) by omega)
    have hkpos : 0 < (k : ℝ) + 1 := by positivity
    have hq : |completedPrimePolarGammaHarmonicCharge k| ≤
        2 * completedSourceObserverJetChargeConstant / (M : ℝ) := by
      apply (abs_completedPrimePolarGammaHarmonicCharge_le_reciprocal k).trans
      apply (div_le_div_iff₀ hkpos hM).mpr
      nlinarith [mul_le_mul_of_nonneg_left hhalf hA]
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (k - (j + 1) : ℕ))]
    exact mul_le_mul hw hq (abs_nonneg _) (by positivity)
  calc
    _ ≤ ∑ k ∈ Finset.Ico (j + 1) (M - 1),
        |((k - (j + 1) : ℕ) : ℝ) * completedPrimePolarGammaHarmonicCharge k| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k ∈ Finset.Ico (j + 1) (M - 1),
        (L : ℝ) * (2 * completedSourceObserverJetChargeConstant / (M : ℝ)) :=
      Finset.sum_le_sum hterm
    _ = ((M - 1 - (j + 1) : ℕ) : ℝ) *
        ((L : ℝ) * (2 * completedSourceObserverJetChargeConstant / (M : ℝ))) := by simp
    _ ≤ ((L : ℝ) + 1) *
        ((L : ℝ) * (2 * completedSourceObserverJetChargeConstant / (M : ℝ))) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast (show M - 1 - (j + 1) ≤ L + 1 by omega)
    _ ≤ (2 * (L : ℝ)) *
        ((L : ℝ) * (2 * completedSourceObserverJetChargeConstant / (M : ℝ))) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      have hL' : (1 : ℝ) ≤ L := by exact_mod_cast hL
      linarith
    _ = _ := by ring

theorem completedSourceObserverJetTerminalPositiveAction_le_cubic
    {M L : ℕ} (hwindow : 2 * (L + 2) ≤ M) :
    completedSourceObserverJetTerminalPositiveAction M L ≤
      8 * completedSourceObserverJetChargeConstant * (L : ℝ) ^ 3 /
        ((M : ℝ) * Real.sqrt (M : ℝ)) := by
  have hA := completedSourceObserverJetChargeConstant_nonneg
  have hM : 0 < (M : ℝ) := by exact_mod_cast (show 0 < M by omega)
  have hsM : 0 < Real.sqrt (M : ℝ) := Real.sqrt_pos.mpr hM
  have hLle : L ≤ M - 3 := by omega
  have hterm (j : ℕ) (hj : j ∈ Finset.Ico (M - 3 - L) (M - 3)) :
      max (completedSourceObserverJetHistory M j) 0 / Real.sqrt (j + 1 : ℕ) ≤
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
    have hhist : max (completedSourceObserverJetHistory M j) 0 ≤
        4 * completedSourceObserverJetChargeConstant * (L : ℝ) ^ 2 / (M : ℝ) := by
      apply max_le
      · exact (le_abs_self _).trans (abs_completedSourceObserverJetHistory_terminal_le hwindow hj)
      · positivity
    calc
      _ = max (completedSourceObserverJetHistory M j) 0 *
          (1 / Real.sqrt (j + 1 : ℕ)) := by ring
      _ ≤ (4 * completedSourceObserverJetChargeConstant * (L : ℝ) ^ 2 / (M : ℝ)) *
          (2 / Real.sqrt (M : ℝ)) := mul_le_mul hhist hinv (by positivity) (by positivity)
      _ = _ := by ring
  unfold completedSourceObserverJetTerminalPositiveAction
  calc
    _ ≤ ∑ _j ∈ Finset.Ico (M - 3 - L) (M - 3),
        8 * completedSourceObserverJetChargeConstant * (L : ℝ) ^ 2 /
          ((M : ℝ) * Real.sqrt (M : ℝ)) := Finset.sum_le_sum hterm
    _ = (L : ℝ) * (8 * completedSourceObserverJetChargeConstant * (L : ℝ) ^ 2 /
        ((M : ℝ) * Real.sqrt (M : ℝ))) := by simp [Nat.sub_sub_self hLle]
    _ = _ := by ring

theorem completedSourceObserverJetTerminalPositiveAction_le_linear
    {M L : ℕ} (hwindow : 2 * (L + 2) ≤ M)
    (hscale : (L : ℝ) ^ 3 ≤ (M : ℝ) ^ 2 * Real.sqrt (M : ℝ)) :
    completedSourceObserverJetTerminalPositiveAction M L ≤
      8 * completedSourceObserverJetChargeConstant * (M : ℝ) := by
  have hA := completedSourceObserverJetChargeConstant_nonneg
  have hM : 0 < (M : ℝ) := by exact_mod_cast (show 0 < M by omega)
  have hsM : 0 < Real.sqrt (M : ℝ) := Real.sqrt_pos.mpr hM
  calc
    _ ≤ 8 * completedSourceObserverJetChargeConstant * (L : ℝ) ^ 3 /
        ((M : ℝ) * Real.sqrt (M : ℝ)) :=
      completedSourceObserverJetTerminalPositiveAction_le_cubic hwindow
    _ ≤ 8 * completedSourceObserverJetChargeConstant *
        ((M : ℝ) ^ 2 * Real.sqrt (M : ℝ)) /
          ((M : ℝ) * Real.sqrt (M : ℝ)) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_left hscale (by positivity)
    _ = _ := by field_simp

theorem completedSourceObserverJetTerminalPositiveAction_sixth_fifth_le
    {N : ℕ} (hN : 3 ≤ N) :
    completedSourceObserverJetTerminalPositiveAction (N ^ 6) (N ^ 5) ≤
      8 * completedSourceObserverJetChargeConstant * (N ^ 6 : ℕ) := by
  have hN5 : 4 ≤ N ^ 5 := by
    calc
      4 ≤ (3 : ℕ) ^ 5 := by norm_num
      _ ≤ N ^ 5 := by gcongr
  have hwindow : 2 * (N ^ 5 + 2) ≤ N ^ 6 := by
    rw [show N ^ 6 = N * N ^ 5 by ring]
    have hmul := Nat.mul_le_mul_right (N ^ 5) hN
    nlinarith
  have hsqrt : Real.sqrt (N ^ 6 : ℕ) = (N : ℝ) ^ 3 := by
    rw [Nat.cast_pow, show (N : ℝ) ^ 6 = ((N : ℝ) ^ 3) ^ 2 by ring,
      Real.sqrt_sq (by positivity)]
  apply completedSourceObserverJetTerminalPositiveAction_le_linear hwindow
  apply le_of_eq
  rw [hsqrt]
  push_cast
  ring

theorem completedSourceObserverJetPositiveHistoryAction_eq_interior_add_terminal
    (M L : ℕ) :
    completedSourceObserverJetPositiveHistoryAction M =
      completedSourceObserverJetInteriorPositiveAction M L +
        completedSourceObserverJetTerminalPositiveAction M L := by
  unfold completedSourceObserverJetPositiveHistoryAction
    completedSourceObserverJetInteriorPositiveAction
    completedSourceObserverJetTerminalPositiveAction
  exact (Finset.sum_range_add_sum_Ico _ (Nat.sub_le (M - 3) L)).symm

theorem riemannHypothesis_of_completedSourceObserverJetInterior_linear
    {L : ℕ → ℕ} {C : ℝ}
    (hwindow : ∀ M : ℕ, 4 ≤ M → 2 * (L M + 2) ≤ M)
    (hscale : ∀ M : ℕ, 4 ≤ M →
      (L M : ℝ) ^ 3 ≤ (M : ℝ) ^ 2 * Real.sqrt (M : ℝ))
    (hinterior : ∀ M : ℕ, 4 ≤ M →
      completedSourceObserverJetInteriorPositiveAction M (L M) ≤ C * (M : ℝ)) :
    RiemannHypothesis := by
  obtain ⟨B, _, hB⟩ := exists_mobiusDivisorSquareRootAbel_upper_positiveHistory
  apply riemannHypothesis_iff_mobiusDivisorSquareRootAbel_eventually_boundedAbove.mpr
  refine ⟨B + (3 / 8 : ℝ) * (C + 8 * completedSourceObserverJetChargeConstant), 4, ?_⟩
  intro M hM
  have hM4 : 4 ≤ M := by omega
  have hMpos : 0 < (M : ℝ) := by exact_mod_cast (show 0 < M by omega)
  have htail := completedSourceObserverJetTerminalPositiveAction_le_linear
    (hwindow M hM4) (hscale M hM4)
  have hfull : completedSourceObserverJetPositiveHistoryAction M ≤
      (C + 8 * completedSourceObserverJetChargeConstant) * (M : ℝ) := by
    rw [completedSourceObserverJetPositiveHistoryAction_eq_interior_add_terminal M (L M)]
    have hi := hinterior M hM4
    nlinarith
  apply (div_le_iff₀ hMpos).mpr
  have hr := hB M (by omega)
  nlinarith

end GaloisForLFunctions.RHTower
