import GaloisForLFunctions.RHTower.ObserverJetEndpointMonotoneTerminalLayer
import GaloisForLFunctions.RHTower.Suzuki.SuzukiObserverJetBoundaryAsymptotics

/-!
# Signed Curvature Asymptotics, Prefix-Mass Potential, and Unit-Step Terminal Telescoping

This module establishes three structural reductions for the completed-source observer-jet
hierarchy:

1. **Exact `3 / (8 √(j + 1))` Curvature Asymptotic and Signed History Action Equivalence:**
   In `SuzukiObserverJetPositiveCurvature`, the discrete curvature
   `observerJetCurvature completedRieszHarmonicClockRatio j` was bounded above by
   `3 / (8 * √(j + 1))`, which required replacing `completedSourceObserverJetHistory M j` by
   `max (completedSourceObserverJetHistory M j) 0` and discarding sign cancellation across `j`.
   Here we prove the sharp two-sided asymptotic
   `0 ≤ 3 / (8 * √(j + 1)) - observerJetCurvature completedRieszHarmonicClockRatio j ≤
     15 / (16 * (j + 1) * √(j + 1))`,
   together with the exact 1-variable prefix-mass decomposition
   `completedSourceObserverJetHistory M j =
     completedSourceObserverJetPrefixPotential j -
       (j + 1) * completedSourceObserverJetMass M + completedSourceObserverJetDrift M`.
   Because `|completedSourceObserverJetHistory M j - completedSourceObserverJetDrift M| ≤
   2 * S * (j + 1)` unconditionally and `∑ (j + 1)^{-3/2} ≤ 6`, the curvature remainder changes
   the total pairing by `O(|Drift M| + √M) = o(M)` unconditionally. Consequently, the **signed**
   history action
   `completedSourceObserverJetSignedHistoryAction M :=
     ∑ j ∈ Finset.range (M - 3), completedSourceObserverJetHistory M j / √(j + 1)`
   is asymptotically equivalent to `(8 / 3) * mobiusDivisorSquareRootAbelMoment M` up to `o(M)`
   (and within `O(M)` uniformly for all `M ≥ 3`), yielding exact one-sided and polynomial-schedule
   RH equivalences without `max` or `abs` inside the sum.

2. **Unconditional Initial-Prefix Control up to `J ≤ M^{2/3}`:**
   On any initial prefix `j ∈ Finset.range J`, the `M`-independent prefix potential and mass term
   contribute at most `2 * S * J * √J` unconditionally to the weighted history action, leaving only
   `2 * √J * max (±completedSourceObserverJetDrift M) 0`.

3. **Unit-Step Telescoping Monotonicity of `lagBracketSlope` and Full-Range 2-Zone Closure:**
   Partitioning `[k + 2, M]` into unit steps `m ↦ m + 1` eliminates the `O(L)` linear drift term in
   `ObserverJetEndpointMonotoneTerminalLayer`, replacing it by `1` while telescoping
   `∑ (1 / m - 1 / (m + 1)) = 1 / (k + 2) - 1 / M` exactly. This removes all sublinear width
   barriers (`M^{5/6}`, `M^{7/8}`) on `completedSourceObserverJetTerminalPositiveAction M L` up to
   the full half-aperture `2 * (L + 2) ≤ M`, and yields an arbitrary-cutoff tail bound
   `6 * (R + 2 + |2γ|) * M / √(J + 1)` on `[J, M - 3)` for any `J ≤ M - 3`. Combining the
   initial prefix `[0, J)` and the tail `[J, M - 3)` covers the entire range `[0, M - 3)` with
   no unanalyzed interior region.
-/

open Set Filter Topology
open scoped BigOperators
noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- Elementary telescoping majorant `1 / (x * √x) ≤ 6 * (1 / √x - 1 / √(x + 1))` for `1 ≤ x`. -/
theorem inv_mul_sqrt_le_six_mul_inv_sqrt_sub {x : ℝ} (hx : 1 ≤ x) :
    1 / (x * Real.sqrt x) ≤ 6 * (1 / Real.sqrt x - 1 / Real.sqrt (x + 1)) := by
  let a := Real.sqrt x
  let b := Real.sqrt (x + 1)
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have ha : 0 < a := Real.sqrt_pos.mpr hx0
  have hb : 0 < b := Real.sqrt_pos.mpr (by linarith)
  have ha2 : a ^ 2 = x := Real.sq_sqrt hx0.le
  have hb2 : b ^ 2 = x + 1 := Real.sq_sqrt (by linarith)
  have hab : a ≤ b := Real.sqrt_le_sqrt (by linarith)
  have hb2a : b ≤ 2 * a := by
    nlinarith [sq_nonneg (2 * a - b)]
  have hdiff : 1 / a - 1 / b = 1 / (a * b * (a + b)) := by
    have hba : (b - a) * (a + b) = 1 := by nlinarith
    have h1 : 1 / a - 1 / b = (b - a) / (a * b) := by
      field_simp [ha.ne', hb.ne']
    rw [h1, ← hba]
    field_simp [ha.ne', hb.ne']
  change 1 / (x * a) ≤ 6 * (1 / a - 1 / b)
  rw [hdiff, show 6 * (1 / (a * b * (a + b))) = 6 / (a * b * (a + b)) by ring]
  rw [div_le_div_iff₀ (by positivity : 0 < x * a) (by positivity : 0 < a * b * (a + b))]
  have hba_le : b * (a + b) ≤ 6 * x := by
    have h1 : a + b ≤ 3 * a := by linarith
    have h2 : b * (a + b) ≤ (2 * a) * (3 * a) :=
      mul_le_mul hb2a h1 (by positivity) (by positivity)
    nlinarith
  nlinarith

/-- Sharp upper bound on the gap `3 / (8 √x) - observerJetClockRealSecondDeriv x ≤ 9 / (16 x √x)`. -/
theorem three_eighths_div_sqrt_sub_observerJetClockRealSecondDeriv_le
    {x : ℝ} (hx : 0 < x) :
    3 / (8 * Real.sqrt x) - observerJetClockRealSecondDeriv x ≤
      9 / (16 * x * Real.sqrt x) := by
  let a := Real.sqrt x
  let b := Real.sqrt (x + 1)
  have ha : 0 < a := Real.sqrt_pos.mpr hx
  have hb : 0 < b := Real.sqrt_pos.mpr (by linarith)
  have ha2 : a ^ 2 = x := Real.sq_sqrt hx.le
  have hb2 : b ^ 2 = x + 1 := Real.sq_sqrt (by linarith)
  have hab : a ≤ b := Real.sqrt_le_sqrt (by linarith)
  have hxab : x ≤ a * b := by
    nlinarith [mul_le_mul_of_nonneg_left hab ha.le]
  rw [observerJetClockRealSecondDeriv_eq_cancelled hx]
  change 3 / (8 * a) - 3 * (3 * a * b - (2 * x + 1)) / (4 * a * b * (a + b)) ≤
    9 / (16 * x * a)
  have hsub : 3 / (8 * a) - 3 * (3 * a * b - (2 * x + 1)) / (4 * a * b * (a + b)) =
      3 * (b * (a + b) - 2 * (3 * a * b - (2 * x + 1))) / (8 * a * b * (a + b)) := by
    field_simp [ha.ne', hb.ne']
    ring
  rw [hsub]
  rw [div_le_div_iff₀ (by positivity : 0 < 8 * a * b * (a + b)) (by positivity : 0 < 16 * x * a)]
  have hnum : b * (a + b) - 2 * (3 * a * b - (2 * x + 1)) ≤ 3 := by
    nlinarith
  have hden : 2 * x ≤ b * (a + b) := by
    have h1 : 2 * a ≤ a + b := by linarith
    have h2 : a * (2 * a) ≤ b * (a + b) :=
      mul_le_mul hab h1 (by positivity) hb.le
    nlinarith
  have hdena : 2 * x * a ≤ a * b * (a + b) := by
    nlinarith [mul_le_mul_of_nonneg_right hden ha.le]
  have hnum_mul : 3 * (b * (a + b) - 2 * (3 * a * b - (2 * x + 1))) * (16 * x * a) ≤
      9 * (16 * x * a) := by
    nlinarith [mul_pos hx ha]
  linarith

/-- Two-sided asymptotic error for the discrete second difference of `observerJetClockReal`:
`0 ≤ 3 / (8 √x) - Δ² observerJetClockReal x ≤ 15 / (16 x √x)` for `1 ≤ x`. -/
theorem three_eighths_div_sqrt_sub_observerJetClockReal_secondDifference_le
    {x : ℝ} (hx : 1 ≤ x) :
    3 / (8 * Real.sqrt x) -
        (observerJetClockReal (x + 2) - 2 * observerJetClockReal (x + 1) +
          observerJetClockReal x) ≤
      15 / (16 * x * Real.sqrt x) := by
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  obtain ⟨d, hdx, hdx2, heq⟩ := observerJetClockReal_secondDifference_eq_secondDeriv hx0
  have hd0 : 0 < d := hx0.trans hdx
  rw [heq]
  have h2 := three_eighths_div_sqrt_sub_observerJetClockRealSecondDeriv_le hd0
  let a := Real.sqrt x
  let c := Real.sqrt d
  have ha : 0 < a := Real.sqrt_pos.mpr hx0
  have hc : 0 < c := Real.sqrt_pos.mpr hd0
  have ha2 : a ^ 2 = x := Real.sq_sqrt hx0.le
  have hc2 : c ^ 2 = d := Real.sq_sqrt hd0.le
  have hac : a ≤ c := Real.sqrt_le_sqrt hdx.le
  have h2' : 3 / (8 * c) - observerJetClockRealSecondDeriv d ≤ 9 / (16 * x * a) := by
    refine h2.trans ?_
    change 9 / (16 * d * c) ≤ 9 / (16 * x * a)
    gcongr
  have h1 : 3 / (8 * a) - 3 / (8 * c) ≤ 6 / (16 * x * a) := by
    have hdiff : 3 / (8 * a) - 3 / (8 * c) = 3 * (d - x) / (8 * a * c * (c + a)) := by
      have hca : (c - a) * (c + a) = d - x := by nlinarith
      rw [← hca]
      field_simp [ha.ne', hc.ne']
    rw [hdiff]
    rw [div_le_div_iff₀ (by positivity : 0 < 8 * a * c * (c + a)) (by positivity : 0 < 16 * x * a)]
    have hcx : 2 * x ≤ c * (c + a) := by
      have hsum : 2 * a ≤ c + a := by linarith
      have hprod : a * (2 * a) ≤ c * (c + a) :=
        mul_le_mul hac hsum (by positivity) hc.le
      nlinarith
    have hcxa : 2 * x * a ≤ a * c * (c + a) := by
      nlinarith [mul_le_mul_of_nonneg_right hcx ha.le]
    have hdx_mul : (d - x) * (x * a) ≤ 2 * (x * a) := by
      nlinarith [mul_pos hx0 ha]
    linarith
  calc
    3 / (8 * Real.sqrt x) - observerJetClockRealSecondDeriv d =
      (3 / (8 * a) - 3 / (8 * c)) + (3 / (8 * c) - observerJetClockRealSecondDeriv d) := by
        dsimp [a, c]; ring
    _ ≤ 6 / (16 * x * a) + 9 / (16 * x * a) := add_le_add h1 h2'
    _ = 15 / (16 * x * Real.sqrt x) := by dsimp [a]; ring

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.RHTower

open _root_.RHTower GaloisForLFunctions.HTGeometry

/-! ## Section 1: Exact `1 / √(j + 1)` Curvature Asymptotic and Signed History Action -/

private theorem sum_Ico_sub_succ {f : ℕ → ℝ} {J N : ℕ} (hJN : J ≤ N) :
    (∑ j ∈ Finset.Ico J N, (f j - f (j + 1))) = f J - f N := by
  induction N, hJN using Nat.le_induction with
  | base => simp
  | succ k hk ih =>
    rw [Finset.sum_Ico_succ_top hk, ih]
    ring

/-- Telescoping tail bound `∑_{j ∈ Ico J N} 1 / ((j + 1) √(j + 1)) ≤ 6 / √(J + 1)`. -/
theorem sum_Ico_inv_mul_sqrt_le (J N : ℕ) :
    (∑ j ∈ Finset.Ico J N,
        1 / (((j + 1 : ℕ) : ℝ) * Real.sqrt (j + 1 : ℕ))) ≤
      6 / Real.sqrt (J + 1 : ℕ) := by
  by_cases hJN : J ≤ N
  · calc
      (∑ j ∈ Finset.Ico J N,
          1 / (((j + 1 : ℕ) : ℝ) * Real.sqrt (j + 1 : ℕ))) ≤
        ∑ j ∈ Finset.Ico J N,
          (6 / Real.sqrt (j + 1 : ℕ) - 6 / Real.sqrt (j + 1 + 1 : ℕ)) := by
        apply Finset.sum_le_sum
        intro j _
        have hj1 : (1 : ℝ) ≤ (j + 1 : ℕ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le j)
        have hstep := inv_mul_sqrt_le_six_mul_inv_sqrt_sub hj1
        have hcast : ((j + 1 : ℕ) : ℝ) + 1 = ((j + 1 + 1 : ℕ) : ℝ) := by push_cast; ring
        rw [hcast] at hstep
        have hring : 6 * (1 / Real.sqrt (j + 1 : ℕ) - 1 / Real.sqrt (j + 1 + 1 : ℕ)) =
            6 / Real.sqrt (j + 1 : ℕ) - 6 / Real.sqrt (j + 1 + 1 : ℕ) := by ring
        linarith
      _ = 6 / Real.sqrt (J + 1 : ℕ) - 6 / Real.sqrt (N + 1 : ℕ) :=
        sum_Ico_sub_succ (f := fun j : ℕ => 6 / Real.sqrt (j + 1 : ℕ)) hJN
      _ ≤ 6 / Real.sqrt (J + 1 : ℕ) := by
        have : 0 ≤ 6 / Real.sqrt (N + 1 : ℕ) := by positivity
        linarith
  · rw [Finset.Ico_eq_empty (by omega : ¬ J < N), Finset.sum_empty]
    positivity

/-- Global prefix bound `∑_{j < N} 1 / ((j + 1) √(j + 1)) ≤ 6`. -/
theorem sum_range_inv_mul_sqrt_le (N : ℕ) :
    (∑ j ∈ Finset.range N,
        1 / (((j + 1 : ℕ) : ℝ) * Real.sqrt (j + 1 : ℕ))) ≤ 6 := by
  rw [Finset.range_eq_Ico]
  refine (sum_Ico_inv_mul_sqrt_le 0 N).trans ?_
  simp

/-- The discrete curvature of `completedRieszHarmonicClockRatio` is within
`15 / (16 (j + 1) √(j + 1))` of `3 / (8 √(j + 1))` from below and `0` from above. -/
theorem three_eighths_div_sqrt_sub_observerJetCurvature_nonneg (j : ℕ) :
    0 ≤ 3 / (8 * Real.sqrt (j + 1 : ℕ)) -
      observerJetCurvature completedRieszHarmonicClockRatio j :=
  sub_nonneg.mpr (observerJetCurvature_completedRieszHarmonicClockRatio_le_three_eighths j)

theorem three_eighths_div_sqrt_sub_observerJetCurvature_le (j : ℕ) :
    3 / (8 * Real.sqrt (j + 1 : ℕ)) -
        observerJetCurvature completedRieszHarmonicClockRatio j ≤
      15 / (16 * ((j + 1 : ℕ) : ℝ) * Real.sqrt (j + 1 : ℕ)) := by
  rw [observerJetCurvature, completedRieszHarmonicClockRatio_eq_observerJetClockReal,
    completedRieszHarmonicClockRatio_eq_observerJetClockReal,
    completedRieszHarmonicClockRatio_eq_observerJetClockReal]
  push_cast
  have h := three_eighths_div_sqrt_sub_observerJetClockReal_secondDifference_le
    (x := (j : ℝ) + 1) (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le j))
  simpa only [show (j : ℝ) + 2 + 1 = (j : ℝ) + 1 + 2 by ring] using h

/-- **1-Variable Prefix-Mass Potential:** the `M`-independent second-history prefix of the
completed harmonic charge `completedPrimePolarGammaHarmonicCharge`. -/
def completedSourceObserverJetPrefixPotential (j : ℕ) : ℝ :=
  observerJetSecondHistory completedPrimePolarGammaHarmonicCharge j

/-- The prefix-mass potential is the sum of `completedSourceObserverJetMass (k + 2)` for
`k ∈ Finset.range (j + 1)`. -/
theorem completedSourceObserverJetPrefixPotential_eq_sum_mass (j : ℕ) :
    completedSourceObserverJetPrefixPotential j =
      ∑ k ∈ Finset.range (j + 1), completedSourceObserverJetMass (k + 2) := by
  unfold completedSourceObserverJetPrefixPotential observerJetSecondHistory observerJetPrefix
  apply Finset.sum_congr rfl
  intro k _
  simp [completedSourceObserverJetMass, observerJetMass]

/-- Exact affine identity for the 1-variable prefix potential:
`P(j) = (j + 1) * completedSourceObserverJetMass (j + 2) - completedSourceObserverJetDrift (j + 2)`. -/
theorem completedSourceObserverJetPrefixPotential_eq_mass_mul_sub_drift (j : ℕ) :
    completedSourceObserverJetPrefixPotential j =
      ((j + 1 : ℕ) : ℝ) * completedSourceObserverJetMass (j + 2) -
        completedSourceObserverJetDrift (j + 2) := by
  rw [completedSourceObserverJetPrefixPotential_eq_sum_mass]
  have h := observerJetDrift_eq_mass_mul_succ_sub_prefixSum
    completedPrimePolarGammaHarmonicCharge j
  simp only [completedSourceObserverJetMass, completedSourceObserverJetDrift,
    Nat.add_sub_cancel]
  push_cast
  linarith

/-- **Exact 1-variable + affine decomposition of `completedSourceObserverJetHistory M j`:**
for `3 ≤ M` and `j < M - 3`,
`History M j = PrefixPotential j - (j + 1) * Mass M + Drift M`. -/
theorem completedSourceObserverJetHistory_eq_prefixPotential_sub_mass_add_drift
    {M j : ℕ} (hM : 3 ≤ M) (hj : j < M - 3) :
    completedSourceObserverJetHistory M j =
      completedSourceObserverJetPrefixPotential j -
        ((j + 1 : ℕ) : ℝ) * completedSourceObserverJetMass M +
        completedSourceObserverJetDrift M := by
  unfold completedSourceObserverJetHistory completedSourceObserverJetPrefixPotential
    completedSourceObserverJetMass completedSourceObserverJetDrift
  rw [observerJetResidual_history_eq_prefix_sub_mass_add_drift
    completedPrimePolarGammaHarmonicCharge (M - 2) j (by omega) (by omega),
    observerJetSecondHistory_eq_weightedPrefix]

/-- **Exact two-point drift-mass difference identity for `completedSourceObserverJetHistory M j`:**
for `3 ≤ M` and `j < M - 3`,
`History M j = (Drift M - Drift (j + 2)) - (j + 1) * (Mass M - Mass (j + 2))`. -/
theorem completedSourceObserverJetHistory_eq_drift_sub_sub_mass_sub
    {M j : ℕ} (hM : 3 ≤ M) (hj : j < M - 3) :
    completedSourceObserverJetHistory M j =
      (completedSourceObserverJetDrift M - completedSourceObserverJetDrift (j + 2)) -
        ((j + 1 : ℕ) : ℝ) *
          (completedSourceObserverJetMass M - completedSourceObserverJetMass (j + 2)) := by
  rw [completedSourceObserverJetHistory_eq_prefixPotential_sub_mass_add_drift hM hj,
    completedSourceObserverJetPrefixPotential_eq_mass_mul_sub_drift]
  ring

/-- Unconditional linear bound on the 1-variable prefix potential:
`|PrefixPotential j| ≤ (∑' k, |q k|) * (j + 1)`. -/
theorem abs_completedSourceObserverJetPrefixPotential_le (j : ℕ) :
    |completedSourceObserverJetPrefixPotential j| ≤
      (∑' k : ℕ, |completedPrimePolarGammaHarmonicCharge k|) * ((j + 1 : ℕ) : ℝ) := by
  rw [completedSourceObserverJetPrefixPotential_eq_sum_mass]
  calc
    |∑ k ∈ Finset.range (j + 1), completedSourceObserverJetMass (k + 2)| ≤
        ∑ k ∈ Finset.range (j + 1), |completedSourceObserverJetMass (k + 2)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k ∈ Finset.range (j + 1),
        (∑' m : ℕ, |completedPrimePolarGammaHarmonicCharge m|) :=
      Finset.sum_le_sum fun k _ => abs_completedSourceObserverJetMass_le (k + 2)
    _ = (∑' k : ℕ, |completedPrimePolarGammaHarmonicCharge k|) * ((j + 1 : ℕ) : ℝ) := by
      simp [mul_comm]

/-- **Unconditional linear bound on `|History M j - Drift M|`:**
for all `3 ≤ M` and `j < M - 3`,
`|completedSourceObserverJetHistory M j - completedSourceObserverJetDrift M| ≤ 2 * S * (j + 1)`. -/
theorem abs_completedSourceObserverJetHistory_sub_drift_le
    {M j : ℕ} (hM : 3 ≤ M) (hj : j < M - 3) :
    |completedSourceObserverJetHistory M j - completedSourceObserverJetDrift M| ≤
      2 * (∑' k : ℕ, |completedPrimePolarGammaHarmonicCharge k|) * ((j + 1 : ℕ) : ℝ) := by
  have heq : completedSourceObserverJetHistory M j - completedSourceObserverJetDrift M =
      completedSourceObserverJetPrefixPotential j -
        ((j + 1 : ℕ) : ℝ) * completedSourceObserverJetMass M := by
    rw [completedSourceObserverJetHistory_eq_prefixPotential_sub_mass_add_drift hM hj]
    ring
  rw [heq]
  have hP := abs_completedSourceObserverJetPrefixPotential_le j
  have hMmass := abs_completedSourceObserverJetMass_le M
  have hmul : |((j + 1 : ℕ) : ℝ) * completedSourceObserverJetMass M| ≤
      (∑' k : ℕ, |completedPrimePolarGammaHarmonicCharge k|) * ((j + 1 : ℕ) : ℝ) := by
    rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg (j + 1)), mul_comm]
    exact mul_le_mul_of_nonneg_right hMmass (Nat.cast_nonneg (j + 1))
  calc
    |completedSourceObserverJetPrefixPotential j -
        ((j + 1 : ℕ) : ℝ) * completedSourceObserverJetMass M| ≤
      |completedSourceObserverJetPrefixPotential j| +
        |((j + 1 : ℕ) : ℝ) * completedSourceObserverJetMass M| := abs_sub _ _
    _ ≤ (∑' k : ℕ, |completedPrimePolarGammaHarmonicCharge k|) * ((j + 1 : ℕ) : ℝ) +
        (∑' k : ℕ, |completedPrimePolarGammaHarmonicCharge k|) * ((j + 1 : ℕ) : ℝ) :=
      add_le_add hP hmul
    _ = 2 * (∑' k : ℕ, |completedPrimePolarGammaHarmonicCharge k|) * ((j + 1 : ℕ) : ℝ) := by ring

/-- Pointwise unconditional majorant for `|completedSourceObserverJetHistory M j|`. -/
theorem abs_completedSourceObserverJetHistory_le_abs_drift_add
    {M j : ℕ} (hM : 3 ≤ M) (hj : j < M - 3) :
    |completedSourceObserverJetHistory M j| ≤
      |completedSourceObserverJetDrift M| +
        2 * (∑' k : ℕ, |completedPrimePolarGammaHarmonicCharge k|) * ((j + 1 : ℕ) : ℝ) := by
  have h := abs_completedSourceObserverJetHistory_sub_drift_le hM hj
  have htri : |completedSourceObserverJetHistory M j| ≤
      |completedSourceObserverJetDrift M| +
        |completedSourceObserverJetHistory M j - completedSourceObserverJetDrift M| := by
    simpa [ add_sub_cancel] using abs_add_le (completedSourceObserverJetDrift M)
      (completedSourceObserverJetHistory M j - completedSourceObserverJetDrift M)
  linarith

/-- **Signed History Action:** the full signed second-history sum with the canonical asymptotic
weight `1 / √(j + 1)` and without `max (·, 0)` or `|·|` inside the sum. -/
def completedSourceObserverJetSignedHistoryAction (M : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (M - 3),
    completedSourceObserverJetHistory M j / Real.sqrt (j + 1 : ℕ)

/-- **Uniform `O(|Drift M| + √M)` bound between the exact curvature pairing and
`(3 / 8) * completedSourceObserverJetSignedHistoryAction M`.** -/
theorem abs_curvatureHistory_sub_three_eighths_signedHistory_le
    {M : ℕ} (hM : 3 ≤ M) :
    |(∑ j ∈ Finset.range (M - 3),
        completedSourceObserverJetHistory M j *
          observerJetCurvature completedRieszHarmonicClockRatio j) -
      (3 / 8 : ℝ) * completedSourceObserverJetSignedHistoryAction M| ≤
      6 * |completedSourceObserverJetDrift M| +
        4 * (∑' k : ℕ, |completedPrimePolarGammaHarmonicCharge k|) * Real.sqrt (M : ℝ) := by
  let S : ℝ := ∑' k : ℕ, |completedPrimePolarGammaHarmonicCharge k|
  have hS : 0 ≤ S := tsum_nonneg fun _ => abs_nonneg _
  rw [completedSourceObserverJetSignedHistoryAction, Finset.mul_sum, ← Finset.sum_sub_distrib]
  have hterm (j : ℕ) (hj : j ∈ Finset.range (M - 3)) :
      |completedSourceObserverJetHistory M j *
          observerJetCurvature completedRieszHarmonicClockRatio j -
        (3 / 8 : ℝ) * (completedSourceObserverJetHistory M j / Real.sqrt (j + 1 : ℕ))| ≤
      |completedSourceObserverJetDrift M| *
          (1 / (((j + 1 : ℕ) : ℝ) * Real.sqrt (j + 1 : ℕ))) +
        2 * S * (1 / Real.sqrt (j + 1 : ℕ)) := by
    have hjlt : j < M - 3 := Finset.mem_range.mp hj
    have hsj : 0 < Real.sqrt (j + 1 : ℕ) := Real.sqrt_pos.mpr (by positivity)
    have hj1 : 0 < ((j + 1 : ℕ) : ℝ) := by positivity
    have hrew :
        completedSourceObserverJetHistory M j *
            observerJetCurvature completedRieszHarmonicClockRatio j -
          (3 / 8 : ℝ) * (completedSourceObserverJetHistory M j / Real.sqrt (j + 1 : ℕ)) =
        -(completedSourceObserverJetHistory M j *
          (3 / (8 * Real.sqrt (j + 1 : ℕ)) -
            observerJetCurvature completedRieszHarmonicClockRatio j)) := by ring
    rw [hrew, abs_neg, abs_mul]
    have herr0 := three_eighths_div_sqrt_sub_observerJetCurvature_nonneg j
    have herr_le : |3 / (8 * Real.sqrt (j + 1 : ℕ)) -
        observerJetCurvature completedRieszHarmonicClockRatio j| ≤
        1 / (((j + 1 : ℕ) : ℝ) * Real.sqrt (j + 1 : ℕ)) := by
      rw [abs_of_nonneg herr0]
      refine (three_eighths_div_sqrt_sub_observerJetCurvature_le j).trans ?_
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [mul_pos hj1 hsj]
    have hhist := abs_completedSourceObserverJetHistory_le_abs_drift_add hM hjlt
    calc
      |completedSourceObserverJetHistory M j| *
          |3 / (8 * Real.sqrt (j + 1 : ℕ)) -
            observerJetCurvature completedRieszHarmonicClockRatio j| ≤
        (|completedSourceObserverJetDrift M| + 2 * S * ((j + 1 : ℕ) : ℝ)) *
          (1 / (((j + 1 : ℕ) : ℝ) * Real.sqrt (j + 1 : ℕ))) :=
        mul_le_mul hhist herr_le (abs_nonneg _) (by positivity)
      _ = |completedSourceObserverJetDrift M| *
            (1 / (((j + 1 : ℕ) : ℝ) * Real.sqrt (j + 1 : ℕ))) +
          2 * S * (1 / Real.sqrt (j + 1 : ℕ)) := by
        field_simp [hj1.ne', hsj.ne']
  have hsum1 := sum_range_inv_mul_sqrt_le (M - 3)
  have hsum2 : (∑ j ∈ Finset.range (M - 3), 1 / Real.sqrt (j + 1 : ℕ)) ≤
      2 * Real.sqrt (M : ℝ) := by
    have h := sum_one_div_sqrt_le (M - 3)
    rw [sum_Icc_eq_sum_range_shift] at h
    have hsqrt : Real.sqrt (M - 3 : ℕ) ≤ Real.sqrt (M : ℝ) :=
      Real.sqrt_le_sqrt (by exact_mod_cast Nat.sub_le M 3)
    linarith
  calc
    |∑ j ∈ Finset.range (M - 3),
        (completedSourceObserverJetHistory M j *
          observerJetCurvature completedRieszHarmonicClockRatio j -
        (3 / 8 : ℝ) * (completedSourceObserverJetHistory M j / Real.sqrt (j + 1 : ℕ)))| ≤
      ∑ j ∈ Finset.range (M - 3),
        |completedSourceObserverJetHistory M j *
          observerJetCurvature completedRieszHarmonicClockRatio j -
        (3 / 8 : ℝ) * (completedSourceObserverJetHistory M j / Real.sqrt (j + 1 : ℕ))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ Finset.range (M - 3),
        (|completedSourceObserverJetDrift M| *
            (1 / (((j + 1 : ℕ) : ℝ) * Real.sqrt (j + 1 : ℕ))) +
          2 * S * (1 / Real.sqrt (j + 1 : ℕ))) := Finset.sum_le_sum hterm
    _ = |completedSourceObserverJetDrift M| *
          (∑ j ∈ Finset.range (M - 3), 1 / (((j + 1 : ℕ) : ℝ) * Real.sqrt (j + 1 : ℕ))) +
        2 * S * (∑ j ∈ Finset.range (M - 3), 1 / Real.sqrt (j + 1 : ℕ)) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    _ ≤ |completedSourceObserverJetDrift M| * 6 + 2 * S * (2 * Real.sqrt (M : ℝ)) :=
      add_le_add
        (mul_le_mul_of_nonneg_left hsum1 (abs_nonneg _))
        (mul_le_mul_of_nonneg_left hsum2 (by positivity))
    _ = 6 * |completedSourceObserverJetDrift M| + 4 * S * Real.sqrt (M : ℝ) := by ring

/-- **Unconditional `o(M)` equivalence between `mobiusDivisorSquareRootAbelMoment M` and
`(3 / 8) * completedSourceObserverJetSignedHistoryAction M`.** -/
theorem tendsto_mobiusDivisorSquareRootAbel_sub_signedHistory_div_zero :
    Tendsto (fun M : ℕ => mobiusDivisorSquareRootAbelMoment M / (M : ℝ) -
      ((3 / 8 : ℝ) * completedSourceObserverJetSignedHistoryAction M) / (M : ℝ))
      atTop (𝓝 0) := by
  let S : ℝ := ∑' k : ℕ, |completedPrimePolarGammaHarmonicCharge k|
  have hcurv := tendsto_mobiusDivisorSquareRootAbel_sub_curvatureHistory_div_zero
  have hdrift0 := tendsto_completedSourceObserverJetDrift_div_aperture_zero.norm
  simp only [Real.norm_eq_abs, abs_div, abs_zero] at hdrift0
  have hsqrt0 : Tendsto (fun M : ℕ => Real.sqrt (M : ℝ) / (M : ℝ)) atTop (𝓝 0) := by
    have hinv : Tendsto (fun M : ℕ => (1 : ℝ) / Real.sqrt (M : ℝ)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
    apply hinv.congr'
    filter_upwards [eventually_ge_atTop 1] with M hM
    have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
    have hsM : 0 < Real.sqrt (M : ℝ) := Real.sqrt_pos.mpr hMpos
    have hsq : Real.sqrt (M : ℝ) * Real.sqrt (M : ℝ) = (M : ℝ) := Real.mul_self_sqrt hMpos.le
    rw [div_eq_div_iff hsM.ne' hMpos.ne']
    linarith
  have hbound0 : Tendsto (fun M : ℕ =>
      6 * (|completedSourceObserverJetDrift M| / |(M : ℝ)|) +
        4 * S * (Real.sqrt (M : ℝ) / (M : ℝ))) atTop (𝓝 0) := by
    simpa using (hdrift0.const_mul 6).add (hsqrt0.const_mul (4 * S))
  have hdiff0 : Tendsto (fun M : ℕ =>
      ((∑ j ∈ Finset.range (M - 3),
          completedSourceObserverJetHistory M j *
            observerJetCurvature completedRieszHarmonicClockRatio j) / (M : ℝ) -
        ((3 / 8 : ℝ) * completedSourceObserverJetSignedHistoryAction M) / (M : ℝ)))
      atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ hbound0
    filter_upwards [eventually_ge_atTop 3] with M hM
    have hMpos : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
    rw [Real.norm_eq_abs, ← sub_div, abs_div, abs_of_pos hMpos]
    have hmain :
        |(∑ j ∈ Finset.range (M - 3),
            completedSourceObserverJetHistory M j *
              observerJetCurvature completedRieszHarmonicClockRatio j) -
          (3 / 8 : ℝ) * completedSourceObserverJetSignedHistoryAction M| ≤
        6 * |completedSourceObserverJetDrift M| + 4 * S * Real.sqrt (M : ℝ) :=
      abs_curvatureHistory_sub_three_eighths_signedHistory_le hM
    have hdiv := div_le_div_of_nonneg_right hmain hMpos.le
    calc
      |(∑ j ∈ Finset.range (M - 3),
            completedSourceObserverJetHistory M j *
              observerJetCurvature completedRieszHarmonicClockRatio j) -
          (3 / 8 : ℝ) * completedSourceObserverJetSignedHistoryAction M| / (M : ℝ) ≤
        (6 * |completedSourceObserverJetDrift M| + 4 * S * Real.sqrt (M : ℝ)) / (M : ℝ) := hdiv
      _ = 6 * (|completedSourceObserverJetDrift M| / (M : ℝ)) +
          4 * S * (Real.sqrt (M : ℝ) / (M : ℝ)) := by ring
  simpa using hcurv.add hdiff0

/-- **Uniform `O(M)` comparison between `mobiusDivisorSquareRootAbelMoment M` and
`(3 / 8) * completedSourceObserverJetSignedHistoryAction M` for all `3 ≤ M`.** -/
theorem exists_abs_mobiusDivisorSquareRootAbel_sub_signedHistory_linear :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ M : ℕ, 3 ≤ M →
      |mobiusDivisorSquareRootAbelMoment M -
        (3 / 8 : ℝ) * completedSourceObserverJetSignedHistoryAction M| ≤ B * (M : ℝ) := by
  let q := completedPrimePolarGammaHarmonicCharge
  let S : ℝ := ∑' k : ℕ, |q k|
  have habs : Summable (fun k => |q k|) := summable_completedPrimePolarGammaHarmonicCharge.abs
  have hS : 0 ≤ S := tsum_nonneg fun _ => abs_nonneg _
  have hfinite (N : ℕ) : (∑ k ∈ Finset.range (N + 1), |q k|) ≤ S :=
    habs.sum_le_tsum _ fun _ _ => abs_nonneg _
  have hdrift (M : ℕ) : |completedSourceObserverJetDrift M| ≤ (M : ℝ) * S := by
    change |∑ k ∈ Finset.range (M - 2 + 1), (k : ℝ) * q k| ≤ (M : ℝ) * S
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc
      (∑ k ∈ Finset.range (M - 2 + 1), |(k : ℝ) * q k|) =
          ∑ k ∈ Finset.range (M - 2 + 1), (k : ℝ) * |q k| := by
        apply Finset.sum_congr rfl
        intro k _
        rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg k)]
      _ ≤ ∑ k ∈ Finset.range (M - 2 + 1), (M : ℝ) * |q k| := by
        apply Finset.sum_le_sum
        intro k hk
        apply mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
        exact_mod_cast (show k ≤ M by have := Finset.mem_range.mp hk; omega)
      _ = (M : ℝ) * ∑ k ∈ Finset.range (M - 2 + 1), |q k| := by rw [Finset.mul_sum]
      _ ≤ (M : ℝ) * S := mul_le_mul_of_nonneg_left (hfinite (M - 2)) (Nat.cast_nonneg M)
  refine ⟨S * (|completedRieszHarmonicClockRatio 0| +
    |completedRieszHarmonicClockRatio 1 - completedRieszHarmonicClockRatio 0| + 10),
    by positivity, fun M hM => ?_⟩
  have hMone : (1 : ℝ) ≤ M := by exact_mod_cast (show 1 ≤ M by omega)
  have hsqrtM : Real.sqrt (M : ℝ) ≤ (M : ℝ) := by
    nlinarith [Real.sq_sqrt (Nat.cast_nonneg M : (0 : ℝ) ≤ M), Real.sqrt_nonneg (M : ℝ)]
  have hmassM : |completedSourceObserverJetMass M| ≤ S := abs_completedSourceObserverJetMass_le M
  have hcurv :
      |(∑ j ∈ Finset.range (M - 3),
          completedSourceObserverJetHistory M j *
            observerJetCurvature completedRieszHarmonicClockRatio j) -
        (3 / 8 : ℝ) * completedSourceObserverJetSignedHistoryAction M| ≤
      6 * |completedSourceObserverJetDrift M| + 4 * S * Real.sqrt (M : ℝ) :=
    abs_curvatureHistory_sub_three_eighths_signedHistory_le hM
  have heq : mobiusDivisorSquareRootAbelMoment M -
      (3 / 8 : ℝ) * completedSourceObserverJetSignedHistoryAction M =
      completedSourceObserverJetMass M * completedRieszHarmonicClockRatio 0 +
        completedSourceObserverJetDrift M *
          (completedRieszHarmonicClockRatio 1 - completedRieszHarmonicClockRatio 0) +
        ((∑ j ∈ Finset.range (M - 3),
            completedSourceObserverJetHistory M j *
              observerJetCurvature completedRieszHarmonicClockRatio j) -
          (3 / 8 : ℝ) * completedSourceObserverJetSignedHistoryAction M) := by
    rw [mobiusDivisorSquareRootAbelMoment_eq_completedSourceObserverJet hM]
    ring
  rw [heq]
  have hSM : S ≤ S * (M : ℝ) := by
    simpa using mul_le_mul_of_nonneg_left hMone hS
  have h1 : |completedSourceObserverJetMass M * completedRieszHarmonicClockRatio 0| ≤
      S * |completedRieszHarmonicClockRatio 0| * (M : ℝ) := by
    rw [abs_mul]
    have hstep1 := mul_le_mul_of_nonneg_right hmassM (abs_nonneg (completedRieszHarmonicClockRatio 0))
    have hstep2 := mul_le_mul_of_nonneg_right hSM (abs_nonneg (completedRieszHarmonicClockRatio 0))
    linarith
  have h2 : |completedSourceObserverJetDrift M *
      (completedRieszHarmonicClockRatio 1 - completedRieszHarmonicClockRatio 0)| ≤
      S * |completedRieszHarmonicClockRatio 1 - completedRieszHarmonicClockRatio 0| * (M : ℝ) := by
    rw [abs_mul]
    have := mul_le_mul_of_nonneg_right (hdrift M)
      (abs_nonneg (completedRieszHarmonicClockRatio 1 - completedRieszHarmonicClockRatio 0))
    linarith
  have h3 : 6 * |completedSourceObserverJetDrift M| + 4 * S * Real.sqrt (M : ℝ) ≤
      10 * S * (M : ℝ) := by
    nlinarith [hdrift M]
  have htri :
      |completedSourceObserverJetMass M * completedRieszHarmonicClockRatio 0 +
          completedSourceObserverJetDrift M *
            (completedRieszHarmonicClockRatio 1 - completedRieszHarmonicClockRatio 0) +
          ((∑ j ∈ Finset.range (M - 3),
              completedSourceObserverJetHistory M j *
                observerJetCurvature completedRieszHarmonicClockRatio j) -
            (3 / 8 : ℝ) * completedSourceObserverJetSignedHistoryAction M)| ≤
      |completedSourceObserverJetMass M * completedRieszHarmonicClockRatio 0| +
        |completedSourceObserverJetDrift M *
          (completedRieszHarmonicClockRatio 1 - completedRieszHarmonicClockRatio 0)| +
        |(∑ j ∈ Finset.range (M - 3),
            completedSourceObserverJetHistory M j *
              observerJetCurvature completedRieszHarmonicClockRatio j) -
          (3 / 8 : ℝ) * completedSourceObserverJetSignedHistoryAction M| :=
    (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
  linarith

/-- **One-sided upper RH equivalence for the signed history action (no `max` inside the sum).** -/
theorem riemannHypothesis_iff_completedSourceObserverJetSignedHistory_boundedAbove :
    RiemannHypothesis ↔
      ∃ C : ℝ, ∀ M : ℕ, 3 ≤ M →
        completedSourceObserverJetSignedHistoryAction M ≤ C * (M : ℝ) := by
  obtain ⟨B, _hB0, hB⟩ := exists_abs_mobiusDivisorSquareRootAbel_sub_signedHistory_linear
  rw [riemannHypothesis_iff_mobiusDivisorSquareRootAbel_boundedAbove]
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨(8 / 3 : ℝ) * (C + B), fun M hM3 => ?_⟩
    have hMpos : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
    have h1 := (div_le_iff₀ hMpos).mp (hC M (by omega))
    have h2 := (abs_sub_le_iff.mp (hB M hM3)).2
    linarith
  · rintro ⟨C, hC⟩
    obtain ⟨M₀, hM2, hM3⟩ :
        ∃ M₀ : ℝ, mobiusDivisorSquareRootAbelMoment 2 / (2 : ℕ) ≤ M₀ ∧
          (3 / 8 : ℝ) * C + B ≤ M₀ :=
      ⟨max (mobiusDivisorSquareRootAbelMoment 2 / (2 : ℕ)) ((3 / 8 : ℝ) * C + B),
        le_max_left _ _, le_max_right _ _⟩
    refine ⟨M₀, fun M hM => ?_⟩
    by_cases hM_eq_2 : M = 2
    · subst M
      exact hM2
    · clear hM2
      have hM_ge_3 : 3 ≤ M := by omega
      have hMpos : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
      have h1 := hC M hM_ge_3
      have h2 := (abs_sub_le_iff.mp (hB M hM_ge_3)).1
      have hdiv : mobiusDivisorSquareRootAbelMoment M / (M : ℝ) ≤ (3 / 8 : ℝ) * C + B :=
        (div_le_iff₀ hMpos).mpr (by linarith)
      exact hdiv.trans hM3

/-- **One-sided lower RH equivalence for the signed history action (no `max` inside the sum).** -/
theorem riemannHypothesis_iff_completedSourceObserverJetSignedHistory_boundedBelow :
    RiemannHypothesis ↔
      ∃ C : ℝ, ∀ M : ℕ, 3 ≤ M →
        -C * (M : ℝ) ≤ completedSourceObserverJetSignedHistoryAction M := by
  obtain ⟨B, _hB0, hB⟩ := exists_abs_mobiusDivisorSquareRootAbel_sub_signedHistory_linear
  rw [riemannHypothesis_iff_mobiusDivisorSquareRootAbel_boundedBelow]
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨(8 / 3 : ℝ) * (-C + B), fun M hM3 => ?_⟩
    have hMpos : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
    have h1 := (le_div_iff₀ hMpos).mp (hC M (by omega))
    have h2 := (abs_sub_le_iff.mp (hB M hM3)).1
    linarith
  · rintro ⟨C, hC⟩
    obtain ⟨M₀, hM2, hM3⟩ :
        ∃ M₀ : ℝ, -M₀ ≤ mobiusDivisorSquareRootAbelMoment 2 / (2 : ℕ) ∧
          (3 / 8 : ℝ) * C + B ≤ M₀ :=
      ⟨max (-mobiusDivisorSquareRootAbelMoment 2 / (2 : ℕ)) ((3 / 8 : ℝ) * C + B),
        by
          have h := neg_le_neg (le_max_left (-mobiusDivisorSquareRootAbelMoment 2 / (2 : ℕ))
            ((3 / 8 : ℝ) * C + B))
          simpa [neg_div] using h,
        le_max_right _ _⟩
    refine ⟨-M₀, fun M hM => ?_⟩
    by_cases hM_eq_2 : M = 2
    · subst M
      exact hM2
    · clear hM2
      have hM_ge_3 : 3 ≤ M := by omega
      have hMpos : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
      have h1 := hC M hM_ge_3
      have h2 := (abs_sub_le_iff.mp (hB M hM_ge_3)).2
      have hdiv : -((3 / 8 : ℝ) * C + B) ≤ mobiusDivisorSquareRootAbelMoment M / (M : ℝ) :=
        (le_div_iff₀ hMpos).mpr (by linarith)
      exact (neg_le_neg hM3).trans hdiv

/-- **Polynomial-schedule (`M = N^m`) upper RH equivalence for the signed history action.** -/
theorem riemannHypothesis_iff_completedSourceObserverJetSignedHistory_pow_bddAbove
    {m : ℕ} (hm : 1 ≤ m) :
    RiemannHypothesis ↔
      ∃ C : ℝ, ∀ N : ℕ, 3 ≤ N →
        completedSourceObserverJetSignedHistoryAction (N ^ m) ≤ C * (N ^ m : ℕ) := by
  obtain ⟨B, _hB0, hB⟩ := exists_abs_mobiusDivisorSquareRootAbel_sub_signedHistory_linear
  rw [riemannHypothesis_iff_mobiusDivisorSquareRootAbel_pow_bddAbove hm]
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨(8 / 3 : ℝ) * (C + B), fun N hN3 => ?_⟩
    have hNm3 : 3 ≤ N ^ m := by
      calc 3 = 3 ^ 1 := (Nat.pow_one 3).symm
        _ ≤ 3 ^ m := Nat.pow_le_pow_right (by omega) hm
        _ ≤ N ^ m := Nat.pow_le_pow_left hN3 m
    have hpos : (0 : ℝ) < (N ^ m : ℕ) := by exact_mod_cast (show 0 < N ^ m by omega)
    have h1 := (div_le_iff₀ hpos).mp (hC N (by omega))
    have h2 := (abs_sub_le_iff.mp (hB (N ^ m) hNm3)).2
    linarith
  · rintro ⟨C, hC⟩
    obtain ⟨M₀, hM2, hM3⟩ :
        ∃ M₀ : ℝ, mobiusDivisorSquareRootAbelMoment (2 ^ m) / (2 ^ m : ℕ) ≤ M₀ ∧
          (3 / 8 : ℝ) * C + B ≤ M₀ :=
      ⟨max (mobiusDivisorSquareRootAbelMoment (2 ^ m) / (2 ^ m : ℕ)) ((3 / 8 : ℝ) * C + B),
        le_max_left _ _, le_max_right _ _⟩
    refine ⟨M₀, fun N hN2 => ?_⟩
    have hN_ge_2 : 2 ≤ N := by
      by_contra hlt
      have hle1 : N ≤ 1 := by omega
      have hpow : N ^ m ≤ 1 ^ m := Nat.pow_le_pow_left hle1 m
      rw [Nat.one_pow] at hpow
      omega
    by_cases hN_eq_2 : N = 2
    · subst N
      exact hM2
    · clear hM2
      have hN3 : 3 ≤ N := by omega
      have hNm3 : 3 ≤ N ^ m := by
        calc 3 = 3 ^ 1 := (Nat.pow_one 3).symm
          _ ≤ 3 ^ m := Nat.pow_le_pow_right (by omega) hm
          _ ≤ N ^ m := Nat.pow_le_pow_left hN3 m
      have hpos : (0 : ℝ) < (N ^ m : ℕ) := by exact_mod_cast (show 0 < N ^ m by omega)
      have h1 := hC N hN3
      have h2 := (abs_sub_le_iff.mp (hB (N ^ m) hNm3)).1
      have hdiv : mobiusDivisorSquareRootAbelMoment (N ^ m) / (N ^ m : ℕ) ≤
          (3 / 8 : ℝ) * C + B :=
        (div_le_iff₀ hpos).mpr (by linarith)
      exact hdiv.trans hM3

/-- **Polynomial-schedule (`M = N^m`) lower RH equivalence for the signed history action.** -/
theorem riemannHypothesis_iff_completedSourceObserverJetSignedHistory_pow_bddBelow
    {m : ℕ} (hm : 1 ≤ m) :
    RiemannHypothesis ↔
      ∃ C : ℝ, ∀ N : ℕ, 3 ≤ N →
        -C * (N ^ m : ℕ) ≤ completedSourceObserverJetSignedHistoryAction (N ^ m) := by
  obtain ⟨B, _hB0, hB⟩ := exists_abs_mobiusDivisorSquareRootAbel_sub_signedHistory_linear
  rw [riemannHypothesis_iff_mobiusDivisorSquareRootAbel_pow_bddBelow hm]
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨(8 / 3 : ℝ) * (-C + B), fun N hN3 => ?_⟩
    have hNm3 : 3 ≤ N ^ m := by
      calc 3 = 3 ^ 1 := (Nat.pow_one 3).symm
        _ ≤ 3 ^ m := Nat.pow_le_pow_right (by omega) hm
        _ ≤ N ^ m := Nat.pow_le_pow_left hN3 m
    have hpos : (0 : ℝ) < (N ^ m : ℕ) := by exact_mod_cast (show 0 < N ^ m by omega)
    have h1 := (le_div_iff₀ hpos).mp (hC N (by omega))
    have h2 := (abs_sub_le_iff.mp (hB (N ^ m) hNm3)).1
    linarith
  · rintro ⟨C, hC⟩
    obtain ⟨M₀, hM2, hM3⟩ :
        ∃ M₀ : ℝ, -M₀ ≤ mobiusDivisorSquareRootAbelMoment (2 ^ m) / (2 ^ m : ℕ) ∧
          (3 / 8 : ℝ) * C + B ≤ M₀ :=
      ⟨max (-mobiusDivisorSquareRootAbelMoment (2 ^ m) / (2 ^ m : ℕ)) ((3 / 8 : ℝ) * C + B),
        by
          have h := neg_le_neg (le_max_left (-mobiusDivisorSquareRootAbelMoment (2 ^ m) / (2 ^ m : ℕ))
            ((3 / 8 : ℝ) * C + B))
          simpa [neg_div] using h,
        le_max_right _ _⟩
    refine ⟨-M₀, fun N hN2 => ?_⟩
    have hN_ge_2 : 2 ≤ N := by
      by_contra hlt
      have hle1 : N ≤ 1 := by omega
      have hpow : N ^ m ≤ 1 ^ m := Nat.pow_le_pow_left hle1 m
      rw [Nat.one_pow] at hpow
      omega
    by_cases hN_eq_2 : N = 2
    · subst N
      exact hM2
    · clear hM2
      have hN3 : 3 ≤ N := by omega
      have hNm3 : 3 ≤ N ^ m := by
        calc 3 = 3 ^ 1 := (Nat.pow_one 3).symm
          _ ≤ 3 ^ m := Nat.pow_le_pow_right (by omega) hm
          _ ≤ N ^ m := Nat.pow_le_pow_left hN3 m
      have hpos : (0 : ℝ) < (N ^ m : ℕ) := by exact_mod_cast (show 0 < N ^ m by omega)
      have h1 := hC N hN3
      have h2 := (abs_sub_le_iff.mp (hB (N ^ m) hNm3)).2
      have hdiv : -((3 / 8 : ℝ) * C + B) ≤
          mobiusDivisorSquareRootAbelMoment (N ^ m) / (N ^ m : ℕ) :=
        (le_div_iff₀ hpos).mpr (by linarith)
      exact (neg_le_neg hM3).trans hdiv

/-! ## Section 2: Unconditional Initial-Prefix Control up to `J ≤ M^{2/3}` -/

/-- Elementary upper bound `∑_{j < J} √(j + 1) ≤ J * √J`. -/
theorem sum_range_sqrt_succ_le (J : ℕ) :
    (∑ j ∈ Finset.range J, Real.sqrt (j + 1 : ℕ)) ≤ (J : ℝ) * Real.sqrt (J : ℝ) := by
  calc
    (∑ j ∈ Finset.range J, Real.sqrt (j + 1 : ℕ)) ≤
        ∑ _j ∈ Finset.range J, Real.sqrt (J : ℝ) := by
      apply Finset.sum_le_sum
      intro j hj
      have hjJ : j + 1 ≤ J := Finset.mem_range.mp hj
      exact Real.sqrt_le_sqrt (by exact_mod_cast hjJ)
    _ = (J : ℝ) * Real.sqrt (J : ℝ) := by simp

/-- **Unconditional initial-prefix bound for the positive history action on `[0, J)`:**
for `3 ≤ M` and `J ≤ M - 3`, the prefix positive action is bounded by
`2 * √J * max (Drift M) 0 + 2 * S * J * √J`. -/
theorem completedSourceObserverJetPrefixPositiveAction_le
    {M J : ℕ} (hM : 3 ≤ M) (hJ : J ≤ M - 3) :
    (∑ j ∈ Finset.range J,
        max (completedSourceObserverJetHistory M j) 0 / Real.sqrt (j + 1 : ℕ)) ≤
      2 * Real.sqrt (J : ℝ) * max (completedSourceObserverJetDrift M) 0 +
        2 * (∑' k : ℕ, |completedPrimePolarGammaHarmonicCharge k|) *
          ((J : ℝ) * Real.sqrt (J : ℝ)) := by
  let S : ℝ := ∑' k : ℕ, |completedPrimePolarGammaHarmonicCharge k|
  have hS : 0 ≤ S := tsum_nonneg fun _ => abs_nonneg _
  have hterm (j : ℕ) (hj : j ∈ Finset.range J) :
      max (completedSourceObserverJetHistory M j) 0 / Real.sqrt (j + 1 : ℕ) ≤
        max (completedSourceObserverJetDrift M) 0 * (1 / Real.sqrt (j + 1 : ℕ)) +
          2 * S * Real.sqrt (j + 1 : ℕ) := by
    have hjM : j < M - 3 := lt_of_lt_of_le (Finset.mem_range.mp hj) hJ
    have hsj : 0 < Real.sqrt (j + 1 : ℕ) := Real.sqrt_pos.mpr (by positivity)
    have hsq : Real.sqrt (j + 1 : ℕ) * Real.sqrt (j + 1 : ℕ) = ((j + 1 : ℕ) : ℝ) :=
      Real.mul_self_sqrt (by positivity)
    have hsub := (abs_le.mp (abs_completedSourceObserverJetHistory_sub_drift_le hM hjM)).2
    have hmax : max (completedSourceObserverJetHistory M j) 0 ≤
        max (completedSourceObserverJetDrift M) 0 + 2 * S * ((j + 1 : ℕ) : ℝ) := by
      apply max_le
      · linarith [le_max_left (completedSourceObserverJetDrift M) 0]
      · positivity
    have hdiv := div_le_div_of_nonneg_right hmax hsj.le
    have hdiv_eq : (max (completedSourceObserverJetDrift M) 0 + 2 * S * ((j + 1 : ℕ) : ℝ)) /
        Real.sqrt (j + 1 : ℕ) =
        max (completedSourceObserverJetDrift M) 0 * (1 / Real.sqrt (j + 1 : ℕ)) +
          2 * S * Real.sqrt (j + 1 : ℕ) := by
      apply (div_eq_iff hsj.ne').mpr
      calc
        max (completedSourceObserverJetDrift M) 0 + 2 * S * ((j + 1 : ℕ) : ℝ) =
          max (completedSourceObserverJetDrift M) 0 *
              ((1 / Real.sqrt (j + 1 : ℕ)) * Real.sqrt (j + 1 : ℕ)) +
            2 * S * (Real.sqrt (j + 1 : ℕ) * Real.sqrt (j + 1 : ℕ)) := by
          rw [one_div_mul_cancel hsj.ne', hsq]
          ring
        _ = (max (completedSourceObserverJetDrift M) 0 * (1 / Real.sqrt (j + 1 : ℕ)) +
              2 * S * Real.sqrt (j + 1 : ℕ)) * Real.sqrt (j + 1 : ℕ) := by ring
    exact hdiv.trans_eq hdiv_eq
  have hsum1 : (∑ j ∈ Finset.range J, 1 / Real.sqrt (j + 1 : ℕ)) ≤ 2 * Real.sqrt (J : ℝ) := by
    have h := sum_one_div_sqrt_le J
    rw [sum_Icc_eq_sum_range_shift] at h
    exact h
  have hsum2 := sum_range_sqrt_succ_le J
  calc
    (∑ j ∈ Finset.range J,
        max (completedSourceObserverJetHistory M j) 0 / Real.sqrt (j + 1 : ℕ)) ≤
      ∑ j ∈ Finset.range J,
        (max (completedSourceObserverJetDrift M) 0 * (1 / Real.sqrt (j + 1 : ℕ)) +
          2 * S * Real.sqrt (j + 1 : ℕ)) := Finset.sum_le_sum hterm
    _ = max (completedSourceObserverJetDrift M) 0 *
          (∑ j ∈ Finset.range J, 1 / Real.sqrt (j + 1 : ℕ)) +
        2 * S * (∑ j ∈ Finset.range J, Real.sqrt (j + 1 : ℕ)) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    _ ≤ max (completedSourceObserverJetDrift M) 0 * (2 * Real.sqrt (J : ℝ)) +
        2 * S * ((J : ℝ) * Real.sqrt (J : ℝ)) :=
      add_le_add
        (mul_le_mul_of_nonneg_left hsum1 (le_max_right _ _))
        (mul_le_mul_of_nonneg_left hsum2 (by positivity))
    _ = 2 * Real.sqrt (J : ℝ) * max (completedSourceObserverJetDrift M) 0 +
        2 * S * ((J : ℝ) * Real.sqrt (J : ℝ)) := by ring

/-- **Unconditional initial-prefix bound for the negative history action on `[0, J)`:**
for `3 ≤ M` and `J ≤ M - 3`, the prefix negative action is bounded by
`2 * √J * max (-Drift M) 0 + 2 * S * J * √J`. -/
theorem completedSourceObserverJetPrefixNegativeAction_le
    {M J : ℕ} (hM : 3 ≤ M) (hJ : J ≤ M - 3) :
    (∑ j ∈ Finset.range J,
        max (-completedSourceObserverJetHistory M j) 0 / Real.sqrt (j + 1 : ℕ)) ≤
      2 * Real.sqrt (J : ℝ) * max (-completedSourceObserverJetDrift M) 0 +
        2 * (∑' k : ℕ, |completedPrimePolarGammaHarmonicCharge k|) *
          ((J : ℝ) * Real.sqrt (J : ℝ)) := by
  let S : ℝ := ∑' k : ℕ, |completedPrimePolarGammaHarmonicCharge k|
  have hS : 0 ≤ S := tsum_nonneg fun _ => abs_nonneg _
  have hterm (j : ℕ) (hj : j ∈ Finset.range J) :
      max (-completedSourceObserverJetHistory M j) 0 / Real.sqrt (j + 1 : ℕ) ≤
        max (-completedSourceObserverJetDrift M) 0 * (1 / Real.sqrt (j + 1 : ℕ)) +
          2 * S * Real.sqrt (j + 1 : ℕ) := by
    have hjM : j < M - 3 := lt_of_lt_of_le (Finset.mem_range.mp hj) hJ
    have hsj : 0 < Real.sqrt (j + 1 : ℕ) := Real.sqrt_pos.mpr (by positivity)
    have hsq : Real.sqrt (j + 1 : ℕ) * Real.sqrt (j + 1 : ℕ) = ((j + 1 : ℕ) : ℝ) :=
      Real.mul_self_sqrt (by positivity)
    have hsub := (abs_le.mp (abs_completedSourceObserverJetHistory_sub_drift_le hM hjM)).1
    have hmax : max (-completedSourceObserverJetHistory M j) 0 ≤
        max (-completedSourceObserverJetDrift M) 0 + 2 * S * ((j + 1 : ℕ) : ℝ) := by
      apply max_le
      · linarith [le_max_left (-completedSourceObserverJetDrift M) 0]
      · positivity
    have hdiv := div_le_div_of_nonneg_right hmax hsj.le
    have hdiv_eq : (max (-completedSourceObserverJetDrift M) 0 + 2 * S * ((j + 1 : ℕ) : ℝ)) /
        Real.sqrt (j + 1 : ℕ) =
        max (-completedSourceObserverJetDrift M) 0 * (1 / Real.sqrt (j + 1 : ℕ)) +
          2 * S * Real.sqrt (j + 1 : ℕ) := by
      apply (div_eq_iff hsj.ne').mpr
      calc
        max (-completedSourceObserverJetDrift M) 0 + 2 * S * ((j + 1 : ℕ) : ℝ) =
          max (-completedSourceObserverJetDrift M) 0 *
              ((1 / Real.sqrt (j + 1 : ℕ)) * Real.sqrt (j + 1 : ℕ)) +
            2 * S * (Real.sqrt (j + 1 : ℕ) * Real.sqrt (j + 1 : ℕ)) := by
          rw [one_div_mul_cancel hsj.ne', hsq]
          ring
        _ = (max (-completedSourceObserverJetDrift M) 0 * (1 / Real.sqrt (j + 1 : ℕ)) +
              2 * S * Real.sqrt (j + 1 : ℕ)) * Real.sqrt (j + 1 : ℕ) := by ring
    exact hdiv.trans_eq hdiv_eq
  have hsum1 : (∑ j ∈ Finset.range J, 1 / Real.sqrt (j + 1 : ℕ)) ≤ 2 * Real.sqrt (J : ℝ) := by
    have h := sum_one_div_sqrt_le J
    rw [sum_Icc_eq_sum_range_shift] at h
    exact h
  have hsum2 := sum_range_sqrt_succ_le J
  calc
    (∑ j ∈ Finset.range J,
        max (-completedSourceObserverJetHistory M j) 0 / Real.sqrt (j + 1 : ℕ)) ≤
      ∑ j ∈ Finset.range J,
        (max (-completedSourceObserverJetDrift M) 0 * (1 / Real.sqrt (j + 1 : ℕ)) +
          2 * S * Real.sqrt (j + 1 : ℕ)) := Finset.sum_le_sum hterm
    _ = max (-completedSourceObserverJetDrift M) 0 *
          (∑ j ∈ Finset.range J, 1 / Real.sqrt (j + 1 : ℕ)) +
        2 * S * (∑ j ∈ Finset.range J, Real.sqrt (j + 1 : ℕ)) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    _ ≤ max (-completedSourceObserverJetDrift M) 0 * (2 * Real.sqrt (J : ℝ)) +
        2 * S * ((J : ℝ) * Real.sqrt (J : ℝ)) :=
      add_le_add
        (mul_le_mul_of_nonneg_left hsum1 (le_max_right _ _))
        (mul_le_mul_of_nonneg_left hsum2 (by positivity))
    _ = 2 * Real.sqrt (J : ℝ) * max (-completedSourceObserverJetDrift M) 0 +
        2 * S * ((J : ℝ) * Real.sqrt (J : ℝ)) := by ring

/-! ## Section 3: Unit-Step Telescoping Monotonicity of `lagBracketSlope` and 2-Zone Closure -/

/-- Unit-step upper bound on `lagBracketSlope (m + 1) - lagBracketSlope m`:
for `1 ≤ m`,
`lagBracketSlope (m + 1) - lagBracketSlope m ≤ (psiRemainder (m + 1) + 1) * (1 / m - 1 / (m + 1))`. -/
theorem lagBracketSlope_succ_sub_le_psiRemainder_add_one
    {m : ℕ} (hm : 1 ≤ m) :
    lagBracketSlope (m + 1) - lagBracketSlope m ≤
      (psiRemainder (m + 1) + 1) * (1 / (m : ℝ) - 1 / ((m + 1 : ℕ) : ℝ)) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hm1 : (0 : ℝ) < (m + 1 : ℕ) := by positivity
  have hstep := lagBracketSlope_sub_le_psiRemainder_add_sub hm (Nat.le_succ m)
  have hsub : ((m + 1 : ℕ) : ℝ) - (m : ℝ) = 1 := by push_cast; ring
  have hrec : 1 / ((m : ℝ) * ((m + 1 : ℕ) : ℝ)) = 1 / (m : ℝ) - 1 / ((m + 1 : ℕ) : ℝ) := by
    field_simp [hm0.ne', hm1.ne']
    push_cast
    ring
  rw [hsub, hrec] at hstep
  exact hstep

/-- Unit-step lower-side bound on `-(lagBracketSlope (m + 1) - lagBracketSlope m)`:
for `1 ≤ m`,
`-(lagBracketSlope (m + 1) - lagBracketSlope m) ≤ (1 - psiRemainder m) * (1 / m - 1 / (m + 1))`. -/
theorem neg_lagBracketSlope_succ_sub_le_one_sub_psiRemainder
    {m : ℕ} (hm : 1 ≤ m) :
    -(lagBracketSlope (m + 1) - lagBracketSlope m) ≤
      (1 - psiRemainder m) * (1 / (m : ℝ) - 1 / ((m + 1 : ℕ) : ℝ)) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hm1 : (0 : ℝ) < (m + 1 : ℕ) := by positivity
  have hstep := neg_lagBracketSlope_sub_le_of_le hm (le_refl m) (Nat.le_succ m)
  have hsub : ((m + 1 : ℕ) : ℝ) - (m : ℝ) = 1 := by push_cast; ring
  have hrec : 1 / ((m : ℝ) * ((m + 1 : ℕ) : ℝ)) = 1 / (m : ℝ) - 1 / ((m + 1 : ℕ) : ℝ) := by
    field_simp [hm0.ne', hm1.ne']
    push_cast
    ring
  rw [hsub, hrec] at hstep
  exact hstep

/-- **Unit-step telescoped upper bound on `lagBracketSlope M - lagBracketSlope d`:**
eliminates the `O(M - d)` linear drift term of single-step monotonicity, replacing it by `1`! -/
theorem lagBracketSlope_sub_le_of_psiRemainder_le_on_Ico
    {d M : ℕ} {R : ℝ} (hd : 1 ≤ d) (hdM : d ≤ M)
    (hpsi : ∀ m ∈ Finset.Ico d M, psiRemainder (m + 1) ≤ R) :
    lagBracketSlope M - lagBracketSlope d ≤
      (R + 1) * (1 / (d : ℝ) - 1 / (M : ℝ)) := by
  rw [← Finset.sum_Ico_sub lagBracketSlope hdM]
  calc
    (∑ m ∈ Finset.Ico d M, (lagBracketSlope (m + 1) - lagBracketSlope m)) ≤
        ∑ m ∈ Finset.Ico d M,
          ((R + 1) * (1 / (m : ℝ) - 1 / ((m + 1 : ℕ) : ℝ))) := by
      apply Finset.sum_le_sum
      intro m hm
      have hdm : d ≤ m := (Finset.mem_Ico.mp hm).1
      have hm1 : 1 ≤ m := hd.trans hdm
      have hgap0 : 0 ≤ 1 / (m : ℝ) - 1 / ((m + 1 : ℕ) : ℝ) := by
        apply sub_nonneg.mpr
        exact one_div_le_one_div_of_le (by exact_mod_cast hm1)
          (by exact_mod_cast Nat.le_succ m)
      refine (lagBracketSlope_succ_sub_le_psiRemainder_add_one hm1).trans ?_
      exact mul_le_mul_of_nonneg_right (by linarith [hpsi m hm]) hgap0
    _ = (R + 1) * (∑ m ∈ Finset.Ico d M, (1 / (m : ℝ) - 1 / ((m + 1 : ℕ) : ℝ))) := by
      rw [← Finset.mul_sum]
    _ = (R + 1) * (1 / (d : ℝ) - 1 / (M : ℝ)) := by
      rw [sum_Ico_sub_succ (f := fun m : ℕ => 1 / (m : ℝ)) hdM]

/-- **Unit-step telescoped lower-side bound on `-(lagBracketSlope M - lagBracketSlope d)`.** -/
theorem neg_lagBracketSlope_sub_le_of_neg_psiRemainder_le_on_Ico
    {d M : ℕ} {R : ℝ} (hd : 1 ≤ d) (hdM : d ≤ M)
    (hpsi : ∀ m ∈ Finset.Ico d M, -psiRemainder m ≤ R) :
    -(lagBracketSlope M - lagBracketSlope d) ≤
      (R + 1) * (1 / (d : ℝ) - 1 / (M : ℝ)) := by
  rw [← Finset.sum_Ico_sub lagBracketSlope hdM, ← Finset.sum_neg_distrib]
  calc
    (∑ m ∈ Finset.Ico d M, -(lagBracketSlope (m + 1) - lagBracketSlope m)) ≤
        ∑ m ∈ Finset.Ico d M,
          ((R + 1) * (1 / (m : ℝ) - 1 / ((m + 1 : ℕ) : ℝ))) := by
      apply Finset.sum_le_sum
      intro m hm
      have hdm : d ≤ m := (Finset.mem_Ico.mp hm).1
      have hm1 : 1 ≤ m := hd.trans hdm
      have hgap0 : 0 ≤ 1 / (m : ℝ) - 1 / ((m + 1 : ℕ) : ℝ) := by
        apply sub_nonneg.mpr
        exact one_div_le_one_div_of_le (by exact_mod_cast hm1)
          (by exact_mod_cast Nat.le_succ m)
      refine (neg_lagBracketSlope_succ_sub_le_one_sub_psiRemainder hm1).trans ?_
      exact mul_le_mul_of_nonneg_right (by linarith [hpsi m hm]) hgap0
    _ = (R + 1) * (∑ m ∈ Finset.Ico d M, (1 / (m : ℝ) - 1 / ((m + 1 : ℕ) : ℝ))) := by
      rw [← Finset.mul_sum]
    _ = (R + 1) * (1 / (d : ℝ) - 1 / (M : ℝ)) := by
      rw [sum_Ico_sub_succ (f := fun m : ℕ => 1 / (m : ℝ)) hdM]

/-- Unit-step telescoped upper bound on the mass difference
`completedSourceObserverJetMass M - completedSourceObserverJetMass (k + 2)`. -/
theorem completedSourceObserverJetMass_sub_le_of_psiRemainder_le_on_Ico
    {k M : ℕ} {R : ℝ} (hkM : k + 2 ≤ M)
    (hpsi : ∀ m ∈ Finset.Ico (k + 2) M, psiRemainder (m + 1) ≤ R) :
    completedSourceObserverJetMass M - completedSourceObserverJetMass (k + 2) ≤
      (R + 2 + |2 * Real.eulerMascheroniConstant|) *
        (1 / ((k + 2 : ℕ) : ℝ) - 1 / (M : ℝ)) := by
  have hlag := lagBracketSlope_sub_le_of_psiRemainder_le_on_Ico
    (by omega : 1 ≤ k + 2) hkM hpsi
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
  have hkcast : ((k : ℝ) + 2) = ((k + 2 : ℕ) : ℝ) := by push_cast; ring
  rw [hMcast, hkcast] at harch
  linarith

/-- Unit-step telescoped lower-side bound on the negated mass difference
`-(completedSourceObserverJetMass M - completedSourceObserverJetMass (k + 2))`. -/
theorem neg_completedSourceObserverJetMass_sub_le_of_neg_psiRemainder_le_on_Ico
    {k M : ℕ} {R : ℝ} (hkM : k + 2 ≤ M)
    (hpsi : ∀ m ∈ Finset.Ico (k + 2) M, -psiRemainder m ≤ R) :
    -(completedSourceObserverJetMass M - completedSourceObserverJetMass (k + 2)) ≤
      (R + 2 + |2 * Real.eulerMascheroniConstant|) *
        (1 / ((k + 2 : ℕ) : ℝ) - 1 / (M : ℝ)) := by
  have hlag := neg_lagBracketSlope_sub_le_of_neg_psiRemainder_le_on_Ico
    (by omega : 1 ≤ k + 2) hkM hpsi
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
  have hkcast : ((k : ℝ) + 2) = ((k + 2 : ℕ) : ℝ) := by push_cast; ring
  rw [hMcast, hkcast] at harch
  linarith

/-- **Drift-free cubic terminal positive-action bound:**
whenever `psiRemainder (m + 1) ≤ R` on `[M - 2 - L, M)`, the `O(L^4)` quartic drift term of
`ObserverJetEndpointMonotoneTerminalLayer` vanishes completely, leaving
`4 * (R + 2 + |2γ|) * L^3 / (M^2 √M) ≤ 4 * (R + 2 + |2γ|) * √M` for ALL `2 * (L + 2) ≤ M`! -/
theorem completedSourceObserverJetTerminalPositiveAction_le_cubic_of_psiRemainder_le
    {M L : ℕ} {R : ℝ} (hR0 : 0 ≤ R) (hwindow : 2 * (L + 2) ≤ M)
    (hpsi : ∀ m ∈ Finset.Ico (M - 2 - L) M, psiRemainder (m + 1) ≤ R) :
    completedSourceObserverJetTerminalPositiveAction M L ≤
      4 * (R + 2 + |2 * Real.eulerMascheroniConstant|) *
        (L : ℝ) ^ 3 / ((M : ℝ) ^ 2 * Real.sqrt (M : ℝ)) := by
  have hM : 0 < (M : ℝ) := by exact_mod_cast (show 0 < M by omega)
  have hsM : 0 < Real.sqrt (M : ℝ) := Real.sqrt_pos.mpr hM
  have hLle : L ≤ M - 3 := by omega
  have hterm (j : ℕ) (hj : j ∈ Finset.Ico (M - 3 - L) (M - 3)) :
      max (completedSourceObserverJetHistory M j) 0 / Real.sqrt (j + 1 : ℕ) ≤
        4 * (R + 2 + |2 * Real.eulerMascheroniConstant|) *
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
    have hhist_le : completedSourceObserverJetHistory M j ≤
        2 * (R + 2 + |2 * Real.eulerMascheroniConstant|) * (L : ℝ) ^ 2 / (M : ℝ) ^ 2 := by
      rw [completedSourceObserverJetHistory_eq_sum_mass_sub (by omega : 3 ≤ M)
        (Finset.mem_range.mpr hj'.2)]
      have hinner (k : ℕ) (hk : k ∈ Finset.Ico (j + 1) (M - 2)) :
          completedSourceObserverJetMass M - completedSourceObserverJetMass (k + 2) ≤
            2 * (R + 2 + |2 * Real.eulerMascheroniConstant|) * (L : ℝ) / (M : ℝ) ^ 2 := by
        have hk' := Finset.mem_Ico.mp hk
        have hkM : k + 2 ≤ M := by omega
        have hpsi_k : ∀ m ∈ Finset.Ico (k + 2) M, psiRemainder (m + 1) ≤ R := by
          intro m hm
          apply hpsi m
          rw [Finset.mem_Ico] at hm ⊢
          exact ⟨by omega, hm.2⟩
        have hstep := completedSourceObserverJetMass_sub_le_of_psiRemainder_le_on_Ico hkM hpsi_k
        have hd0 : (0 : ℝ) < (k + 2 : ℕ) := by positivity
        have hgap_le : 1 / ((k + 2 : ℕ) : ℝ) - 1 / (M : ℝ) ≤ 2 * (L : ℝ) / (M : ℝ) ^ 2 := by
          have hgap_eq : 1 / ((k + 2 : ℕ) : ℝ) - 1 / (M : ℝ) =
              ((M : ℝ) - ((k + 2 : ℕ) : ℝ)) / (((k + 2 : ℕ) : ℝ) * (M : ℝ)) := by
            field_simp [hd0.ne', hM.ne']
          rw [hgap_eq, div_le_div_iff₀ (mul_pos hd0 hM) (sq_pos_of_pos hM)]
          have hsub_le : (M : ℝ) - ((k + 2 : ℕ) : ℝ) ≤ L := by
            have : M - (k + 2) ≤ L := by omega
            have hcast : ((M - (k + 2) : ℕ) : ℝ) = (M : ℝ) - ((k + 2 : ℕ) : ℝ) :=
              Nat.cast_sub hkM
            linarith [show ((M - (k + 2) : ℕ) : ℝ) ≤ L by exact_mod_cast this]
          have hhalf_k : (M : ℝ) ≤ 2 * ((k + 2 : ℕ) : ℝ) := by
            exact_mod_cast (show M ≤ 2 * (k + 2) by omega)
          nlinarith [mul_le_mul_of_nonneg_right hsub_le (sq_nonneg (M : ℝ)),
            mul_le_mul_of_nonneg_left hhalf_k (mul_nonneg (Nat.cast_nonneg L) hM.le)]
        calc
          completedSourceObserverJetMass M - completedSourceObserverJetMass (k + 2) ≤
            (R + 2 + |2 * Real.eulerMascheroniConstant|) *
              (1 / ((k + 2 : ℕ) : ℝ) - 1 / (M : ℝ)) := hstep
          _ ≤ (R + 2 + |2 * Real.eulerMascheroniConstant|) *
              (2 * (L : ℝ) / (M : ℝ) ^ 2) :=
            mul_le_mul_of_nonneg_left hgap_le (by positivity)
          _ = 2 * (R + 2 + |2 * Real.eulerMascheroniConstant|) * (L : ℝ) / (M : ℝ) ^ 2 := by ring
      have hcard : ((M - 2 - (j + 1) : ℕ) : ℝ) ≤ L := by
        exact_mod_cast (show M - 2 - (j + 1) ≤ L by omega)
      calc
        (∑ k ∈ Finset.Ico (j + 1) (M - 2),
            (completedSourceObserverJetMass M - completedSourceObserverJetMass (k + 2))) ≤
          ∑ _k ∈ Finset.Ico (j + 1) (M - 2),
            (2 * (R + 2 + |2 * Real.eulerMascheroniConstant|) * (L : ℝ) / (M : ℝ) ^ 2) :=
          Finset.sum_le_sum hinner
        _ = ((M - 2 - (j + 1) : ℕ) : ℝ) *
            (2 * (R + 2 + |2 * Real.eulerMascheroniConstant|) * (L : ℝ) / (M : ℝ) ^ 2) := by simp
        _ ≤ (L : ℝ) *
            (2 * (R + 2 + |2 * Real.eulerMascheroniConstant|) * (L : ℝ) / (M : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_right hcard (by positivity)
        _ = 2 * (R + 2 + |2 * Real.eulerMascheroniConstant|) * (L : ℝ) ^ 2 / (M : ℝ) ^ 2 := by
          ring
    have hhist : max (completedSourceObserverJetHistory M j) 0 ≤
        2 * (R + 2 + |2 * Real.eulerMascheroniConstant|) * (L : ℝ) ^ 2 / (M : ℝ) ^ 2 :=
      max_le hhist_le (by positivity)
    calc
      max (completedSourceObserverJetHistory M j) 0 / Real.sqrt (j + 1 : ℕ) =
        max (completedSourceObserverJetHistory M j) 0 * (1 / Real.sqrt (j + 1 : ℕ)) := by ring
      _ ≤ (2 * (R + 2 + |2 * Real.eulerMascheroniConstant|) * (L : ℝ) ^ 2 / (M : ℝ) ^ 2) *
          (2 / Real.sqrt (M : ℝ)) :=
        mul_le_mul hhist hinv (by positivity) (by positivity)
      _ = 4 * (R + 2 + |2 * Real.eulerMascheroniConstant|) *
          (L : ℝ) ^ 2 / ((M : ℝ) ^ 2 * Real.sqrt (M : ℝ)) := by ring
  unfold completedSourceObserverJetTerminalPositiveAction
  calc
    _ ≤ ∑ _j ∈ Finset.Ico (M - 3 - L) (M - 3),
        4 * (R + 2 + |2 * Real.eulerMascheroniConstant|) *
          (L : ℝ) ^ 2 / ((M : ℝ) ^ 2 * Real.sqrt (M : ℝ)) := Finset.sum_le_sum hterm
    _ = (L : ℝ) *
        (4 * (R + 2 + |2 * Real.eulerMascheroniConstant|) *
          (L : ℝ) ^ 2 / ((M : ℝ) ^ 2 * Real.sqrt (M : ℝ))) := by simp [Nat.sub_sub_self hLle]
    _ = _ := by ring

/-- **Drift-free cubic terminal negative-action bound:**
whenever `-psiRemainder m ≤ R` on `[M - 2 - L, M)`,
`completedSourceObserverJetTerminalNegativeAction M L ≤ 4 * (R + 2 + |2γ|) * L^3 / (M^2 √M)`. -/
theorem completedSourceObserverJetTerminalNegativeAction_le_cubic_of_neg_psiRemainder_le
    {M L : ℕ} {R : ℝ} (hR0 : 0 ≤ R) (hwindow : 2 * (L + 2) ≤ M)
    (hpsi : ∀ m ∈ Finset.Ico (M - 2 - L) M, -psiRemainder m ≤ R) :
    completedSourceObserverJetTerminalNegativeAction M L ≤
      4 * (R + 2 + |2 * Real.eulerMascheroniConstant|) *
        (L : ℝ) ^ 3 / ((M : ℝ) ^ 2 * Real.sqrt (M : ℝ)) := by
  have hM : 0 < (M : ℝ) := by exact_mod_cast (show 0 < M by omega)
  have hsM : 0 < Real.sqrt (M : ℝ) := Real.sqrt_pos.mpr hM
  have hLle : L ≤ M - 3 := by omega
  have hterm (j : ℕ) (hj : j ∈ Finset.Ico (M - 3 - L) (M - 3)) :
      max (-completedSourceObserverJetHistory M j) 0 / Real.sqrt (j + 1 : ℕ) ≤
        4 * (R + 2 + |2 * Real.eulerMascheroniConstant|) *
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
    have hhist_le : -completedSourceObserverJetHistory M j ≤
        2 * (R + 2 + |2 * Real.eulerMascheroniConstant|) * (L : ℝ) ^ 2 / (M : ℝ) ^ 2 := by
      rw [completedSourceObserverJetHistory_eq_sum_mass_sub (by omega : 3 ≤ M)
        (Finset.mem_range.mpr hj'.2), ← Finset.sum_neg_distrib]
      have hinner (k : ℕ) (hk : k ∈ Finset.Ico (j + 1) (M - 2)) :
          -(completedSourceObserverJetMass M - completedSourceObserverJetMass (k + 2)) ≤
            2 * (R + 2 + |2 * Real.eulerMascheroniConstant|) * (L : ℝ) / (M : ℝ) ^ 2 := by
        have hk' := Finset.mem_Ico.mp hk
        have hkM : k + 2 ≤ M := by omega
        have hpsi_k : ∀ m ∈ Finset.Ico (k + 2) M, -psiRemainder m ≤ R := by
          intro m hm
          apply hpsi m
          rw [Finset.mem_Ico] at hm ⊢
          exact ⟨by omega, hm.2⟩
        have hstep := neg_completedSourceObserverJetMass_sub_le_of_neg_psiRemainder_le_on_Ico
          hkM hpsi_k
        have hd0 : (0 : ℝ) < (k + 2 : ℕ) := by positivity
        have hgap_le : 1 / ((k + 2 : ℕ) : ℝ) - 1 / (M : ℝ) ≤ 2 * (L : ℝ) / (M : ℝ) ^ 2 := by
          have hgap_eq : 1 / ((k + 2 : ℕ) : ℝ) - 1 / (M : ℝ) =
              ((M : ℝ) - ((k + 2 : ℕ) : ℝ)) / (((k + 2 : ℕ) : ℝ) * (M : ℝ)) := by
            field_simp [hd0.ne', hM.ne']
          rw [hgap_eq, div_le_div_iff₀ (mul_pos hd0 hM) (sq_pos_of_pos hM)]
          have hsub_le : (M : ℝ) - ((k + 2 : ℕ) : ℝ) ≤ L := by
            have : M - (k + 2) ≤ L := by omega
            have hcast : ((M - (k + 2) : ℕ) : ℝ) = (M : ℝ) - ((k + 2 : ℕ) : ℝ) :=
              Nat.cast_sub hkM
            linarith [show ((M - (k + 2) : ℕ) : ℝ) ≤ L by exact_mod_cast this]
          have hhalf_k : (M : ℝ) ≤ 2 * ((k + 2 : ℕ) : ℝ) := by
            exact_mod_cast (show M ≤ 2 * (k + 2) by omega)
          nlinarith [mul_le_mul_of_nonneg_right hsub_le (sq_nonneg (M : ℝ)),
            mul_le_mul_of_nonneg_left hhalf_k (mul_nonneg (Nat.cast_nonneg L) hM.le)]
        calc
          -(completedSourceObserverJetMass M - completedSourceObserverJetMass (k + 2)) ≤
            (R + 2 + |2 * Real.eulerMascheroniConstant|) *
              (1 / ((k + 2 : ℕ) : ℝ) - 1 / (M : ℝ)) := hstep
          _ ≤ (R + 2 + |2 * Real.eulerMascheroniConstant|) *
              (2 * (L : ℝ) / (M : ℝ) ^ 2) :=
            mul_le_mul_of_nonneg_left hgap_le (by positivity)
          _ = 2 * (R + 2 + |2 * Real.eulerMascheroniConstant|) * (L : ℝ) / (M : ℝ) ^ 2 := by ring
      have hcard : ((M - 2 - (j + 1) : ℕ) : ℝ) ≤ L := by
        exact_mod_cast (show M - 2 - (j + 1) ≤ L by omega)
      calc
        (∑ k ∈ Finset.Ico (j + 1) (M - 2),
            -(completedSourceObserverJetMass M - completedSourceObserverJetMass (k + 2))) ≤
          ∑ _k ∈ Finset.Ico (j + 1) (M - 2),
            (2 * (R + 2 + |2 * Real.eulerMascheroniConstant|) * (L : ℝ) / (M : ℝ) ^ 2) :=
          Finset.sum_le_sum hinner
        _ = ((M - 2 - (j + 1) : ℕ) : ℝ) *
            (2 * (R + 2 + |2 * Real.eulerMascheroniConstant|) * (L : ℝ) / (M : ℝ) ^ 2) := by simp
        _ ≤ (L : ℝ) *
            (2 * (R + 2 + |2 * Real.eulerMascheroniConstant|) * (L : ℝ) / (M : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_right hcard (by positivity)
        _ = 2 * (R + 2 + |2 * Real.eulerMascheroniConstant|) * (L : ℝ) ^ 2 / (M : ℝ) ^ 2 := by
          ring
    have hhist : max (-completedSourceObserverJetHistory M j) 0 ≤
        2 * (R + 2 + |2 * Real.eulerMascheroniConstant|) * (L : ℝ) ^ 2 / (M : ℝ) ^ 2 :=
      max_le hhist_le (by positivity)
    calc
      max (-completedSourceObserverJetHistory M j) 0 / Real.sqrt (j + 1 : ℕ) =
        max (-completedSourceObserverJetHistory M j) 0 * (1 / Real.sqrt (j + 1 : ℕ)) := by ring
      _ ≤ (2 * (R + 2 + |2 * Real.eulerMascheroniConstant|) * (L : ℝ) ^ 2 / (M : ℝ) ^ 2) *
          (2 / Real.sqrt (M : ℝ)) :=
        mul_le_mul hhist hinv (by positivity) (by positivity)
      _ = 4 * (R + 2 + |2 * Real.eulerMascheroniConstant|) *
          (L : ℝ) ^ 2 / ((M : ℝ) ^ 2 * Real.sqrt (M : ℝ)) := by ring
  unfold completedSourceObserverJetTerminalNegativeAction
  calc
    _ ≤ ∑ _j ∈ Finset.Ico (M - 3 - L) (M - 3),
        4 * (R + 2 + |2 * Real.eulerMascheroniConstant|) *
          (L : ℝ) ^ 2 / ((M : ℝ) ^ 2 * Real.sqrt (M : ℝ)) := Finset.sum_le_sum hterm
    _ = (L : ℝ) *
        (4 * (R + 2 + |2 * Real.eulerMascheroniConstant|) *
          (L : ℝ) ^ 2 / ((M : ℝ) ^ 2 * Real.sqrt (M : ℝ))) := by simp [Nat.sub_sub_self hLle]
    _ = _ := by ring

/-- **Arbitrary-Cutoff Tail Positive-Action Bound on `[J, M - 3)` (no `2 * (L + 2) ≤ M` restriction):**
for any `3 ≤ M`, `J ≤ M - 3`, and `R ≥ 0` with `psiRemainder (m + 1) ≤ R` on `[J + 2, M)`,
`∑_{j ∈ Ico J (M - 3)} max (History M j) 0 / √(j + 1) ≤ 6 * (R + 2 + |2γ|) * M / √(J + 1)`. -/
theorem completedSourceObserverJetTailPositiveAction_le_of_psiRemainder_le
    {M J : ℕ} {R : ℝ} (hR0 : 0 ≤ R) (hM : 3 ≤ M)
    (hpsi : ∀ m ∈ Finset.Ico (J + 2) M, psiRemainder (m + 1) ≤ R) :
    (∑ j ∈ Finset.Ico J (M - 3),
        max (completedSourceObserverJetHistory M j) 0 / Real.sqrt (j + 1 : ℕ)) ≤
      6 * (R + 2 + |2 * Real.eulerMascheroniConstant|) * (M : ℝ) / Real.sqrt (J + 1 : ℕ) := by
  have hterm (j : ℕ) (hj : j ∈ Finset.Ico J (M - 3)) :
      max (completedSourceObserverJetHistory M j) 0 / Real.sqrt (j + 1 : ℕ) ≤
        ((R + 2 + |2 * Real.eulerMascheroniConstant|) * (M : ℝ)) *
          (1 / (((j + 1 : ℕ) : ℝ) * Real.sqrt (j + 1 : ℕ))) := by
    have hj' := Finset.mem_Ico.mp hj
    have hsj : 0 < Real.sqrt (j + 1 : ℕ) := Real.sqrt_pos.mpr (by positivity)
    have hj1 : (0 : ℝ) < (j + 1 : ℕ) := by positivity
    have hhist_le : completedSourceObserverJetHistory M j ≤
        (R + 2 + |2 * Real.eulerMascheroniConstant|) * (M : ℝ) / ((j + 1 : ℕ) : ℝ) := by
      rw [completedSourceObserverJetHistory_eq_sum_mass_sub hM (Finset.mem_range.mpr hj'.2)]
      have hinner (k : ℕ) (hk : k ∈ Finset.Ico (j + 1) (M - 2)) :
          completedSourceObserverJetMass M - completedSourceObserverJetMass (k + 2) ≤
            (R + 2 + |2 * Real.eulerMascheroniConstant|) / ((j + 1 : ℕ) : ℝ) := by
        have hk' := Finset.mem_Ico.mp hk
        have hkM : k + 2 ≤ M := by omega
        have hpsi_k : ∀ m ∈ Finset.Ico (k + 2) M, psiRemainder (m + 1) ≤ R := by
          intro m hm
          apply hpsi m
          rw [Finset.mem_Ico] at hm ⊢
          exact ⟨by omega, hm.2⟩
        have hstep := completedSourceObserverJetMass_sub_le_of_psiRemainder_le_on_Ico hkM hpsi_k
        have hgap_le : 1 / ((k + 2 : ℕ) : ℝ) - 1 / (M : ℝ) ≤ 1 / ((j + 1 : ℕ) : ℝ) := by
          have h1 : 1 / ((k + 2 : ℕ) : ℝ) ≤ 1 / ((j + 1 : ℕ) : ℝ) :=
            one_div_le_one_div_of_le hj1 (by exact_mod_cast (show j + 1 ≤ k + 2 by omega))
          have h2 : (0 : ℝ) ≤ 1 / (M : ℝ) := by positivity
          linarith
        calc
          completedSourceObserverJetMass M - completedSourceObserverJetMass (k + 2) ≤
            (R + 2 + |2 * Real.eulerMascheroniConstant|) *
              (1 / ((k + 2 : ℕ) : ℝ) - 1 / (M : ℝ)) := hstep
          _ ≤ (R + 2 + |2 * Real.eulerMascheroniConstant|) * (1 / ((j + 1 : ℕ) : ℝ)) :=
            mul_le_mul_of_nonneg_left hgap_le (by positivity)
          _ = (R + 2 + |2 * Real.eulerMascheroniConstant|) / ((j + 1 : ℕ) : ℝ) := by ring
      have hcard : ((M - 2 - (j + 1) : ℕ) : ℝ) ≤ (M : ℝ) := by
        exact_mod_cast (show M - 2 - (j + 1) ≤ M by omega)
      calc
        (∑ k ∈ Finset.Ico (j + 1) (M - 2),
            (completedSourceObserverJetMass M - completedSourceObserverJetMass (k + 2))) ≤
          ∑ _k ∈ Finset.Ico (j + 1) (M - 2),
            ((R + 2 + |2 * Real.eulerMascheroniConstant|) / ((j + 1 : ℕ) : ℝ)) :=
          Finset.sum_le_sum hinner
        _ = ((M - 2 - (j + 1) : ℕ) : ℝ) *
            ((R + 2 + |2 * Real.eulerMascheroniConstant|) / ((j + 1 : ℕ) : ℝ)) := by simp
        _ ≤ (M : ℝ) * ((R + 2 + |2 * Real.eulerMascheroniConstant|) / ((j + 1 : ℕ) : ℝ)) :=
          mul_le_mul_of_nonneg_right hcard (by positivity)
        _ = (R + 2 + |2 * Real.eulerMascheroniConstant|) * (M : ℝ) / ((j + 1 : ℕ) : ℝ) := by ring
    have hmax : max (completedSourceObserverJetHistory M j) 0 ≤
        (R + 2 + |2 * Real.eulerMascheroniConstant|) * (M : ℝ) / ((j + 1 : ℕ) : ℝ) :=
      max_le hhist_le (by positivity)
    have hdiv := div_le_div_of_nonneg_right hmax hsj.le
    calc
      max (completedSourceObserverJetHistory M j) 0 / Real.sqrt (j + 1 : ℕ) ≤
        ((R + 2 + |2 * Real.eulerMascheroniConstant|) * (M : ℝ) / ((j + 1 : ℕ) : ℝ)) /
          Real.sqrt (j + 1 : ℕ) := hdiv
      _ = ((R + 2 + |2 * Real.eulerMascheroniConstant|) * (M : ℝ)) *
          (1 / (((j + 1 : ℕ) : ℝ) * Real.sqrt (j + 1 : ℕ))) := by ring
  calc
    (∑ j ∈ Finset.Ico J (M - 3),
        max (completedSourceObserverJetHistory M j) 0 / Real.sqrt (j + 1 : ℕ)) ≤
      ∑ j ∈ Finset.Ico J (M - 3),
        (((R + 2 + |2 * Real.eulerMascheroniConstant|) * (M : ℝ)) *
          (1 / (((j + 1 : ℕ) : ℝ) * Real.sqrt (j + 1 : ℕ)))) := Finset.sum_le_sum hterm
    _ = ((R + 2 + |2 * Real.eulerMascheroniConstant|) * (M : ℝ)) *
        (∑ j ∈ Finset.Ico J (M - 3),
          1 / (((j + 1 : ℕ) : ℝ) * Real.sqrt (j + 1 : ℕ))) := by rw [← Finset.mul_sum]
    _ ≤ ((R + 2 + |2 * Real.eulerMascheroniConstant|) * (M : ℝ)) *
        (6 / Real.sqrt (J + 1 : ℕ)) :=
      mul_le_mul_of_nonneg_left (sum_Ico_inv_mul_sqrt_le J (M - 3)) (by positivity)
    _ = 6 * (R + 2 + |2 * Real.eulerMascheroniConstant|) * (M : ℝ) / Real.sqrt (J + 1 : ℕ) := by
      ring

/-- **Arbitrary-Cutoff Tail Negative-Action Bound on `[J, M - 3)`:**
for any `3 ≤ M`, `J ≤ M - 3`, and `R ≥ 0` with `-psiRemainder m ≤ R` on `[J + 2, M)`,
`∑_{j ∈ Ico J (M - 3)} max (-History M j) 0 / √(j + 1) ≤ 6 * (R + 2 + |2γ|) * M / √(J + 1)`. -/
theorem completedSourceObserverJetTailNegativeAction_le_of_neg_psiRemainder_le
    {M J : ℕ} {R : ℝ} (hR0 : 0 ≤ R) (hM : 3 ≤ M)
    (hpsi : ∀ m ∈ Finset.Ico (J + 2) M, -psiRemainder m ≤ R) :
    (∑ j ∈ Finset.Ico J (M - 3),
        max (-completedSourceObserverJetHistory M j) 0 / Real.sqrt (j + 1 : ℕ)) ≤
      6 * (R + 2 + |2 * Real.eulerMascheroniConstant|) * (M : ℝ) / Real.sqrt (J + 1 : ℕ) := by
  have hterm (j : ℕ) (hj : j ∈ Finset.Ico J (M - 3)) :
      max (-completedSourceObserverJetHistory M j) 0 / Real.sqrt (j + 1 : ℕ) ≤
        ((R + 2 + |2 * Real.eulerMascheroniConstant|) * (M : ℝ)) *
          (1 / (((j + 1 : ℕ) : ℝ) * Real.sqrt (j + 1 : ℕ))) := by
    have hj' := Finset.mem_Ico.mp hj
    have hsj : 0 < Real.sqrt (j + 1 : ℕ) := Real.sqrt_pos.mpr (by positivity)
    have hj1 : (0 : ℝ) < (j + 1 : ℕ) := by positivity
    have hhist_le : -completedSourceObserverJetHistory M j ≤
        (R + 2 + |2 * Real.eulerMascheroniConstant|) * (M : ℝ) / ((j + 1 : ℕ) : ℝ) := by
      rw [completedSourceObserverJetHistory_eq_sum_mass_sub hM (Finset.mem_range.mpr hj'.2),
        ← Finset.sum_neg_distrib]
      have hinner (k : ℕ) (hk : k ∈ Finset.Ico (j + 1) (M - 2)) :
          -(completedSourceObserverJetMass M - completedSourceObserverJetMass (k + 2)) ≤
            (R + 2 + |2 * Real.eulerMascheroniConstant|) / ((j + 1 : ℕ) : ℝ) := by
        have hk' := Finset.mem_Ico.mp hk
        have hkM : k + 2 ≤ M := by omega
        have hpsi_k : ∀ m ∈ Finset.Ico (k + 2) M, -psiRemainder m ≤ R := by
          intro m hm
          apply hpsi m
          rw [Finset.mem_Ico] at hm ⊢
          exact ⟨by omega, hm.2⟩
        have hstep := neg_completedSourceObserverJetMass_sub_le_of_neg_psiRemainder_le_on_Ico
          hkM hpsi_k
        have hgap_le : 1 / ((k + 2 : ℕ) : ℝ) - 1 / (M : ℝ) ≤ 1 / ((j + 1 : ℕ) : ℝ) := by
          have h1 : 1 / ((k + 2 : ℕ) : ℝ) ≤ 1 / ((j + 1 : ℕ) : ℝ) :=
            one_div_le_one_div_of_le hj1 (by exact_mod_cast (show j + 1 ≤ k + 2 by omega))
          have h2 : (0 : ℝ) ≤ 1 / (M : ℝ) := by positivity
          linarith
        calc
          -(completedSourceObserverJetMass M - completedSourceObserverJetMass (k + 2)) ≤
            (R + 2 + |2 * Real.eulerMascheroniConstant|) *
              (1 / ((k + 2 : ℕ) : ℝ) - 1 / (M : ℝ)) := hstep
          _ ≤ (R + 2 + |2 * Real.eulerMascheroniConstant|) * (1 / ((j + 1 : ℕ) : ℝ)) :=
            mul_le_mul_of_nonneg_left hgap_le (by positivity)
          _ = (R + 2 + |2 * Real.eulerMascheroniConstant|) / ((j + 1 : ℕ) : ℝ) := by ring
      have hcard : ((M - 2 - (j + 1) : ℕ) : ℝ) ≤ (M : ℝ) := by
        exact_mod_cast (show M - 2 - (j + 1) ≤ M by omega)
      calc
        (∑ k ∈ Finset.Ico (j + 1) (M - 2),
            -(completedSourceObserverJetMass M - completedSourceObserverJetMass (k + 2))) ≤
          ∑ _k ∈ Finset.Ico (j + 1) (M - 2),
            ((R + 2 + |2 * Real.eulerMascheroniConstant|) / ((j + 1 : ℕ) : ℝ)) :=
          Finset.sum_le_sum hinner
        _ = ((M - 2 - (j + 1) : ℕ) : ℝ) *
            ((R + 2 + |2 * Real.eulerMascheroniConstant|) / ((j + 1 : ℕ) : ℝ)) := by simp
        _ ≤ (M : ℝ) * ((R + 2 + |2 * Real.eulerMascheroniConstant|) / ((j + 1 : ℕ) : ℝ)) :=
          mul_le_mul_of_nonneg_right hcard (by positivity)
        _ = (R + 2 + |2 * Real.eulerMascheroniConstant|) * (M : ℝ) / ((j + 1 : ℕ) : ℝ) := by ring
    have hmax : max (-completedSourceObserverJetHistory M j) 0 ≤
        (R + 2 + |2 * Real.eulerMascheroniConstant|) * (M : ℝ) / ((j + 1 : ℕ) : ℝ) :=
      max_le hhist_le (by positivity)
    have hdiv := div_le_div_of_nonneg_right hmax hsj.le
    calc
      max (-completedSourceObserverJetHistory M j) 0 / Real.sqrt (j + 1 : ℕ) ≤
        ((R + 2 + |2 * Real.eulerMascheroniConstant|) * (M : ℝ) / ((j + 1 : ℕ) : ℝ)) /
          Real.sqrt (j + 1 : ℕ) := hdiv
      _ = ((R + 2 + |2 * Real.eulerMascheroniConstant|) * (M : ℝ)) *
          (1 / (((j + 1 : ℕ) : ℝ) * Real.sqrt (j + 1 : ℕ))) := by ring
  calc
    (∑ j ∈ Finset.Ico J (M - 3),
        max (-completedSourceObserverJetHistory M j) 0 / Real.sqrt (j + 1 : ℕ)) ≤
      ∑ j ∈ Finset.Ico J (M - 3),
        (((R + 2 + |2 * Real.eulerMascheroniConstant|) * (M : ℝ)) *
          (1 / (((j + 1 : ℕ) : ℝ) * Real.sqrt (j + 1 : ℕ)))) := Finset.sum_le_sum hterm
    _ = ((R + 2 + |2 * Real.eulerMascheroniConstant|) * (M : ℝ)) *
        (∑ j ∈ Finset.Ico J (M - 3),
          1 / (((j + 1 : ℕ) : ℝ) * Real.sqrt (j + 1 : ℕ))) := by rw [← Finset.mul_sum]
    _ ≤ ((R + 2 + |2 * Real.eulerMascheroniConstant|) * (M : ℝ)) *
        (6 / Real.sqrt (J + 1 : ℕ)) :=
      mul_le_mul_of_nonneg_left (sum_Ico_inv_mul_sqrt_le J (M - 3)) (by positivity)
    _ = 6 * (R + 2 + |2 * Real.eulerMascheroniConstant|) * (M : ℝ) / Real.sqrt (J + 1 : ℕ) := by
      ring

/-- **Full-Range 2-Zone Positive History Action Bound:**
Combining the unconditional prefix bound on `[0, J)` and the unit-step telescoped tail bound on
`[J, M - 3)` bounds the entire `completedSourceObserverJetPositiveHistoryAction M` with no
unanalyzed interior region. -/
theorem completedSourceObserverJetPositiveHistoryAction_le_of_twoZone
    {M J : ℕ} {R : ℝ} (hR0 : 0 ≤ R) (hM : 3 ≤ M) (hJ : J ≤ M - 3)
    (hpsi : ∀ m ∈ Finset.Ico (J + 2) M, psiRemainder (m + 1) ≤ R) :
    completedSourceObserverJetPositiveHistoryAction M ≤
      2 * Real.sqrt (J : ℝ) * max (completedSourceObserverJetDrift M) 0 +
        2 * (∑' k : ℕ, |completedPrimePolarGammaHarmonicCharge k|) *
          ((J : ℝ) * Real.sqrt (J : ℝ)) +
        6 * (R + 2 + |2 * Real.eulerMascheroniConstant|) * (M : ℝ) / Real.sqrt (J + 1 : ℕ) := by
  unfold completedSourceObserverJetPositiveHistoryAction
  rw [← Finset.sum_range_add_sum_Ico _ hJ]
  exact add_le_add
    (completedSourceObserverJetPrefixPositiveAction_le hM hJ)
    (completedSourceObserverJetTailPositiveAction_le_of_psiRemainder_le hR0 hM hpsi)

/-- **Full-Range 2-Zone Negative History Action Bound:**
Combining the unconditional prefix bound on `[0, J)` and the unit-step telescoped tail bound on
`[J, M - 3)` bounds the entire `completedSourceObserverJetNegativeHistoryAction M` with no
unanalyzed interior region. -/
theorem completedSourceObserverJetNegativeHistoryAction_le_of_twoZone
    {M J : ℕ} {R : ℝ} (hR0 : 0 ≤ R) (hM : 3 ≤ M) (hJ : J ≤ M - 3)
    (hpsi : ∀ m ∈ Finset.Ico (J + 2) M, -psiRemainder m ≤ R) :
    completedSourceObserverJetNegativeHistoryAction M ≤
      2 * Real.sqrt (J : ℝ) * max (-completedSourceObserverJetDrift M) 0 +
        2 * (∑' k : ℕ, |completedPrimePolarGammaHarmonicCharge k|) *
          ((J : ℝ) * Real.sqrt (J : ℝ)) +
        6 * (R + 2 + |2 * Real.eulerMascheroniConstant|) * (M : ℝ) / Real.sqrt (J + 1 : ℕ) := by
  unfold completedSourceObserverJetNegativeHistoryAction
  rw [← Finset.sum_range_add_sum_Ico _ hJ]
  exact add_le_add
    (completedSourceObserverJetPrefixNegativeAction_le hM hJ)
    (completedSourceObserverJetTailNegativeAction_le_of_neg_psiRemainder_le hR0 hM hpsi)

/-- **Full-Range 2-Zone Positive RH Criterion (`M = N^3, J = N^2`) with NO interior hypothesis:**
because `J * √J = N^3 = M`, the initial prefix `[0, N^2)` is `O(N^3)` unconditionally on the
potential/mass terms, leaving only `Drift (N^3)` and `psiRemainder` on `[N^2 + 3, N^3]`. -/
theorem riemannHypothesis_of_twoZone_cubic_positive
    {K D : ℝ} (hK0 : 0 ≤ K) (hD0 : 0 ≤ D)
    (hdrift : ∀ N : ℕ, 3 ≤ N → completedSourceObserverJetDrift (N ^ 3) ≤ D * (N ^ 2 : ℕ))
    (hpsi : ∀ N : ℕ, 3 ≤ N → ∀ m ∈ Finset.Ico (N ^ 2 + 2) (N ^ 3),
      psiRemainder (m + 1) ≤ K * (N : ℝ)) :
    RiemannHypothesis := by
  have hS : 0 ≤ ∑' k : ℕ, |completedPrimePolarGammaHarmonicCharge k| :=
    tsum_nonneg fun _ => abs_nonneg _
  obtain ⟨B, _hB0, hB⟩ := exists_mobiusDivisorSquareRootAbel_upper_positiveHistory
  rw [riemannHypothesis_iff_mobiusDivisorSquareRootAbel_pow_bddAbove (m := 3) (by omega)]
  refine ⟨max (mobiusDivisorSquareRootAbelMoment (2 ^ 3) / (2 ^ 3 : ℕ))
    (B + (3 / 8 : ℝ) * (2 * D + 2 * (∑' k : ℕ, |completedPrimePolarGammaHarmonicCharge k|) +
      6 * (K + 2 + |2 * Real.eulerMascheroniConstant|))), fun N hN2 => ?_⟩
  have hN_ge_2 : 2 ≤ N := by
    by_contra hlt
    have hle1 : N ≤ 1 := by omega
    have hpow : N ^ 3 ≤ 1 ^ 3 := Nat.pow_le_pow_left hle1 3
    omega
  by_cases hN_eq_2 : N = 2
  · subst N
    exact le_max_left _ _
  · have hN : 3 ≤ N := by omega
    have hN3 : 3 ≤ N ^ 3 := by
      calc 3 ≤ 3 ^ 3 := by norm_num
        _ ≤ N ^ 3 := Nat.pow_le_pow_left hN 3
    have hJ : N ^ 2 ≤ N ^ 3 - 3 := by
      have : 3 * N ^ 2 ≤ N ^ 3 := by
        rw [show N ^ 3 = N * N ^ 2 by ring]
        exact Nat.mul_le_mul_right (N ^ 2) hN
      have : 9 ≤ N ^ 2 := by
        calc 9 = 3 ^ 2 := by norm_num
          _ ≤ N ^ 2 := Nat.pow_le_pow_left hN 2
      omega
    have hsqrtJ : Real.sqrt ((N ^ 2 : ℕ) : ℝ) = (N : ℝ) := by
      rw [Nat.cast_pow, Real.sqrt_sq (by positivity)]
    have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    have hN3pos : (0 : ℝ) < (N ^ 3 : ℕ) := by exact_mod_cast (show 0 < N ^ 3 by omega)
    have hzone := completedSourceObserverJetPositiveHistoryAction_le_of_twoZone
      (M := N ^ 3) (J := N ^ 2) (R := K * (N : ℝ))
      (by positivity) hN3 hJ (hpsi N hN)
    have h1 : 2 * Real.sqrt ((N ^ 2 : ℕ) : ℝ) * max (completedSourceObserverJetDrift (N ^ 3)) 0 ≤
        2 * D * (N ^ 3 : ℕ) := by
      rw [hsqrtJ]
      have hd : max (completedSourceObserverJetDrift (N ^ 3)) 0 ≤ D * (N ^ 2 : ℕ) :=
        max_le (hdrift N hN) (by positivity)
      have hmul := mul_le_mul_of_nonneg_left hd (show (0 : ℝ) ≤ 2 * (N : ℝ) by positivity)
      push_cast at hmul ⊢
      linarith
    have h2 : 2 * (∑' k : ℕ, |completedPrimePolarGammaHarmonicCharge k|) *
        (((N ^ 2 : ℕ) : ℝ) * Real.sqrt ((N ^ 2 : ℕ) : ℝ)) =
        2 * (∑' k : ℕ, |completedPrimePolarGammaHarmonicCharge k|) * (N ^ 3 : ℕ) := by
      rw [hsqrtJ]
      push_cast
      ring
    have h3 : 6 * (K * (N : ℝ) + 2 + |2 * Real.eulerMascheroniConstant|) * (N ^ 3 : ℕ) /
        Real.sqrt (N ^ 2 + 1 : ℕ) ≤
        6 * (K + 2 + |2 * Real.eulerMascheroniConstant|) * (N ^ 3 : ℕ) := by
      have hsJ1 : (N : ℝ) ≤ Real.sqrt (N ^ 2 + 1 : ℕ) := by
        rw [← hsqrtJ]
        exact Real.sqrt_le_sqrt (by exact_mod_cast Nat.le_succ (N ^ 2))
      have hspos : 0 < Real.sqrt (N ^ 2 + 1 : ℕ) := Real.sqrt_pos.mpr (by positivity)
      apply (div_le_iff₀ hspos).mpr
      have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
      have hcoeff : K * (N : ℝ) + 2 + |2 * Real.eulerMascheroniConstant| ≤
          (K + 2 + |2 * Real.eulerMascheroniConstant|) * (N : ℝ) := by
        nlinarith [abs_nonneg (2 * Real.eulerMascheroniConstant)]
      have hcoeff_mul : 6 * (K * (N : ℝ) + 2 + |2 * Real.eulerMascheroniConstant|) * (N ^ 3 : ℕ) ≤
          6 * (K + 2 + |2 * Real.eulerMascheroniConstant|) * (N ^ 3 : ℕ) * (N : ℝ) := by
        nlinarith [mul_le_mul_of_nonneg_right hcoeff hN3pos.le]
      have hsqrt_mul : 6 * (K + 2 + |2 * Real.eulerMascheroniConstant|) * (N ^ 3 : ℕ) * (N : ℝ) ≤
          6 * (K + 2 + |2 * Real.eulerMascheroniConstant|) * (N ^ 3 : ℕ) *
            Real.sqrt (N ^ 2 + 1 : ℕ) :=
        mul_le_mul_of_nonneg_left hsJ1 (by positivity)
      linarith
    have hact : completedSourceObserverJetPositiveHistoryAction (N ^ 3) ≤
        (2 * D + 2 * (∑' k : ℕ, |completedPrimePolarGammaHarmonicCharge k|) +
          6 * (K + 2 + |2 * Real.eulerMascheroniConstant|)) * (N ^ 3 : ℕ) := by
      linarith
    have hupper := hB (N ^ 3) hN3
    have hdiv : mobiusDivisorSquareRootAbelMoment (N ^ 3) / (N ^ 3 : ℕ) ≤
        B + (3 / 8 : ℝ) * (2 * D + 2 * (∑' k : ℕ, |completedPrimePolarGammaHarmonicCharge k|) +
          6 * (K + 2 + |2 * Real.eulerMascheroniConstant|)) := by
      apply (div_le_iff₀ hN3pos).mpr
      have hact_mul := mul_le_mul_of_nonneg_left hact (show (0 : ℝ) ≤ 3 / 8 by norm_num)
      linarith
    exact hdiv.trans (le_max_right _ _)

/-- **Full-Range 2-Zone Negative RH Criterion (`M = N^3, J = N^2`) with NO interior hypothesis:**
symmetric lower-bound counterpart to `riemannHypothesis_of_twoZone_cubic_positive`. -/
theorem riemannHypothesis_of_twoZone_cubic_negative
    {K D : ℝ} (hK0 : 0 ≤ K) (hD0 : 0 ≤ D)
    (hdrift : ∀ N : ℕ, 3 ≤ N → -completedSourceObserverJetDrift (N ^ 3) ≤ D * (N ^ 2 : ℕ))
    (hpsi : ∀ N : ℕ, 3 ≤ N → ∀ m ∈ Finset.Ico (N ^ 2 + 2) (N ^ 3),
      -psiRemainder m ≤ K * (N : ℝ)) :
    RiemannHypothesis := by
  have hS : 0 ≤ ∑' k : ℕ, |completedPrimePolarGammaHarmonicCharge k| :=
    tsum_nonneg fun _ => abs_nonneg _
  obtain ⟨B, _hB0, hB⟩ := exists_mobiusDivisorSquareRootAbel_lower_negativeHistory
  rw [riemannHypothesis_iff_mobiusDivisorSquareRootAbel_pow_bddBelow (m := 3) (by omega)]
  refine ⟨min (mobiusDivisorSquareRootAbelMoment (2 ^ 3) / (2 ^ 3 : ℕ))
    (-(B + (3 / 8 : ℝ) * (2 * D + 2 * (∑' k : ℕ, |completedPrimePolarGammaHarmonicCharge k|) +
      6 * (K + 2 + |2 * Real.eulerMascheroniConstant|)))), fun N hN2 => ?_⟩
  have hN_ge_2 : 2 ≤ N := by
    by_contra hlt
    have hle1 : N ≤ 1 := by omega
    have hpow : N ^ 3 ≤ 1 ^ 3 := Nat.pow_le_pow_left hle1 3
    omega
  by_cases hN_eq_2 : N = 2
  · subst N
    exact min_le_left _ _
  · have hN : 3 ≤ N := by omega
    have hN3 : 3 ≤ N ^ 3 := by
      calc 3 ≤ 3 ^ 3 := by norm_num
        _ ≤ N ^ 3 := Nat.pow_le_pow_left hN 3
    have hJ : N ^ 2 ≤ N ^ 3 - 3 := by
      have : 3 * N ^ 2 ≤ N ^ 3 := by
        rw [show N ^ 3 = N * N ^ 2 by ring]
        exact Nat.mul_le_mul_right (N ^ 2) hN
      have : 9 ≤ N ^ 2 := by
        calc 9 = 3 ^ 2 := by norm_num
          _ ≤ N ^ 2 := Nat.pow_le_pow_left hN 2
      omega
    have hsqrtJ : Real.sqrt ((N ^ 2 : ℕ) : ℝ) = (N : ℝ) := by
      rw [Nat.cast_pow, Real.sqrt_sq (by positivity)]
    have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    have hN3pos : (0 : ℝ) < (N ^ 3 : ℕ) := by exact_mod_cast (show 0 < N ^ 3 by omega)
    have hzone := completedSourceObserverJetNegativeHistoryAction_le_of_twoZone
      (M := N ^ 3) (J := N ^ 2) (R := K * (N : ℝ))
      (by positivity) hN3 hJ (hpsi N hN)
    have h1 : 2 * Real.sqrt ((N ^ 2 : ℕ) : ℝ) * max (-completedSourceObserverJetDrift (N ^ 3)) 0 ≤
        2 * D * (N ^ 3 : ℕ) := by
      rw [hsqrtJ]
      have hd : max (-completedSourceObserverJetDrift (N ^ 3)) 0 ≤ D * (N ^ 2 : ℕ) :=
        max_le (hdrift N hN) (by positivity)
      have hmul := mul_le_mul_of_nonneg_left hd (show (0 : ℝ) ≤ 2 * (N : ℝ) by positivity)
      push_cast at hmul ⊢
      linarith
    have h2 : 2 * (∑' k : ℕ, |completedPrimePolarGammaHarmonicCharge k|) *
        (((N ^ 2 : ℕ) : ℝ) * Real.sqrt ((N ^ 2 : ℕ) : ℝ)) =
        2 * (∑' k : ℕ, |completedPrimePolarGammaHarmonicCharge k|) * (N ^ 3 : ℕ) := by
      rw [hsqrtJ]
      push_cast
      ring
    have h3 : 6 * (K * (N : ℝ) + 2 + |2 * Real.eulerMascheroniConstant|) * (N ^ 3 : ℕ) /
        Real.sqrt (N ^ 2 + 1 : ℕ) ≤
        6 * (K + 2 + |2 * Real.eulerMascheroniConstant|) * (N ^ 3 : ℕ) := by
      have hsJ1 : (N : ℝ) ≤ Real.sqrt (N ^ 2 + 1 : ℕ) := by
        rw [← hsqrtJ]
        exact Real.sqrt_le_sqrt (by exact_mod_cast Nat.le_succ (N ^ 2))
      have hspos : 0 < Real.sqrt (N ^ 2 + 1 : ℕ) := Real.sqrt_pos.mpr (by positivity)
      apply (div_le_iff₀ hspos).mpr
      have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
      have hcoeff : K * (N : ℝ) + 2 + |2 * Real.eulerMascheroniConstant| ≤
          (K + 2 + |2 * Real.eulerMascheroniConstant|) * (N : ℝ) := by
        nlinarith [abs_nonneg (2 * Real.eulerMascheroniConstant)]
      have hcoeff_mul : 6 * (K * (N : ℝ) + 2 + |2 * Real.eulerMascheroniConstant|) * (N ^ 3 : ℕ) ≤
          6 * (K + 2 + |2 * Real.eulerMascheroniConstant|) * (N ^ 3 : ℕ) * (N : ℝ) := by
        nlinarith [mul_le_mul_of_nonneg_right hcoeff hN3pos.le]
      have hsqrt_mul : 6 * (K + 2 + |2 * Real.eulerMascheroniConstant|) * (N ^ 3 : ℕ) * (N : ℝ) ≤
          6 * (K + 2 + |2 * Real.eulerMascheroniConstant|) * (N ^ 3 : ℕ) *
            Real.sqrt (N ^ 2 + 1 : ℕ) :=
        mul_le_mul_of_nonneg_left hsJ1 (by positivity)
      linarith
    have hact : completedSourceObserverJetNegativeHistoryAction (N ^ 3) ≤
        (2 * D + 2 * (∑' k : ℕ, |completedPrimePolarGammaHarmonicCharge k|) +
          6 * (K + 2 + |2 * Real.eulerMascheroniConstant|)) * (N ^ 3 : ℕ) := by
      linarith
    have hlower := hB (N ^ 3) hN3
    have hdiv : -(B + (3 / 8 : ℝ) * (2 * D + 2 * (∑' k : ℕ, |completedPrimePolarGammaHarmonicCharge k|) +
          6 * (K + 2 + |2 * Real.eulerMascheroniConstant|))) ≤
        mobiusDivisorSquareRootAbelMoment (N ^ 3) / (N ^ 3 : ℕ) := by
      apply (le_div_iff₀ hN3pos).mpr
      have hact_mul := mul_le_mul_of_nonneg_left hact (show (0 : ℝ) ≤ 3 / 8 by norm_num)
      linarith
    exact (min_le_right _ _).trans hdiv

end GaloisForLFunctions.RHTower
