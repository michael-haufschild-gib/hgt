import GaloisForLFunctions.RHTower.FiniteAndersonLocalizedSurvivalRecurrenceLaw

/-!
# Resolution-scale Anderson-localized survival recurrence

Set phase resolution `Q = 2^N - 1` at spatial scale `N`.  If the
localization ball contains at most `V (N+1)^ν` modes, the finite localized
survival law gives the explicit deadline

`2 ^ (N * (V * (N + 1) ^ ν - 1))`

and survival-deviation budget

`4 * geometricTail(N) + 4π / 2^N`.

The theorem is deterministic and finite-dimensional.  Its localization and
shell hypotheses remain explicit; no random Anderson ensemble statement is
inferred.
-/

open scoped BigOperators

noncomputable section

namespace RHTower

private theorem two_pow_sub_one_add_one (N : ℕ) :
    (2 ^ N - 1) + 1 = 2 ^ N :=
  Nat.sub_add_cancel (Nat.one_le_pow N 2 (by norm_num))

/--
**Finite Anderson-localized resolution-scale recurrence law.**

At spatial scale `N`, phase resolution `Q = 2^N - 1`, localization-ball
growth `|B_N| ≤ V(N+1)^ν`, exponential spectral localization, and geometric
shell growth imply one positive recurrence time satisfying

`n ≤ 2^(N(V(N+1)^ν-1))`

with survival deviation at most

`4 geometricTail(C,μ,A,B,N) + 4π/2^N`.
-/
theorem exists_finiteAndersonLocalizedSurvival_resolutionScale_recurrence
    {d : ℕ} (p : Fin d → ℝ)
    (hp : ∀ i, 0 ≤ p i)
    (hpSum : ∑ i, p i = 1)
    (radius : Fin d → ℕ) (N ν V : ℕ)
    (hBall : (finiteLocalizationBall radius N).Nonempty)
    (hvolume :
      (finiteLocalizationBall radius N).card ≤
        V * (N + 1) ^ ν)
    (C μ A B : ℝ)
    (hC : 0 ≤ C) (hμ : 0 < μ)
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hcontract : B * Real.exp (-2 * μ) < 1)
    (hdecay :
      ∀ i,
        p i ≤ C * Real.exp (-2 * μ * (radius i : ℝ)))
    (hshell :
      ∀ m,
        ((finiteLocalizationShell radius m).card : ℝ) ≤
          A * B ^ m)
    (energy : Fin d → ℝ) :
    ∃ n : ℕ, 0 < n ∧
      n ≤ 2 ^ (N * (V * (N + 1) ^ ν - 1)) ∧
      finiteSpectralSurvivalDeviation p
          (finiteObserverHamiltonianVertexPhase
            (n : ℝ) energy) ≤
        4 * finiteLocalizationGeometricTailBound C μ A B N +
          4 * Real.pi / (2 ^ N : ℝ) := by
  obtain ⟨n, hn0, hnQ, hdev⟩ :=
    exists_finiteAndersonLocalizedSurvival_volume_recurrence
      p hp hpSum radius N (V * (N + 1) ^ ν)
      hBall hvolume C μ A B hC hμ hA hB
      hcontract hdecay hshell energy (2 ^ N - 1)
  rw [two_pow_sub_one_add_one N] at hnQ
  have hnDeadline :
      n ≤ 2 ^ (N * (V * (N + 1) ^ ν - 1)) := by
    simpa only [pow_mul] using hnQ
  refine ⟨n, hn0, hnDeadline, ?_⟩
  have hbaseReal :
      (((2 ^ N - 1 : ℕ) : ℝ) + 1) =
        ((2 ^ N : ℕ) : ℝ) := by
    exact_mod_cast two_pow_sub_one_add_one N
  rw [hbaseReal] at hdev
  have hcastPow :
      ((2 ^ N : ℕ) : ℝ) = (2 : ℝ) ^ N := by
    norm_num
  rw [hcastPow] at hdev
  calc
    finiteSpectralSurvivalDeviation p
        (finiteObserverHamiltonianVertexPhase
          (n : ℝ) energy) ≤
      4 * finiteLocalizationGeometricTailBound C μ A B N +
        2 * (2 * Real.pi / (2 : ℝ) ^ N) :=
      hdev
    _ = 4 * finiteLocalizationGeometricTailBound C μ A B N +
        4 * Real.pi / (2 ^ N : ℝ) := by ring

/--
**Non-vacuous resolution-scale survival alternative.**

At the same explicit resolution-scale budget, either survival deviation
never leaves the budget at any nonnegative time, or it leaves and later
returns.  The return is strictly post-exit and obeys the same spatial
resolution deadline after conversion to physical time.
-/
theorem
    finiteAndersonLocalizedSurvival_resolutionScale_neverExits_or_postExit_return
    {d : ℕ} (p : Fin d → ℝ)
    (hp : ∀ i, 0 ≤ p i)
    (hpSum : ∑ i, p i = 1)
    (radius : Fin d → ℕ) (N ν V : ℕ)
    (hBall : (finiteLocalizationBall radius N).Nonempty)
    (hvolume :
      (finiteLocalizationBall radius N).card ≤
        V * (N + 1) ^ ν)
    (C μ A B : ℝ)
    (hC : 0 ≤ C) (hμ : 0 < μ)
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hcontract : B * Real.exp (-2 * μ) < 1)
    (hdecay :
      ∀ i,
        p i ≤ C * Real.exp (-2 * μ * (radius i : ℝ)))
    (hshell :
      ∀ m,
        ((finiteLocalizationShell radius m).card : ℝ) ≤
          A * B ^ m)
    (energy : Fin d → ℝ)
    (guardTime : ℝ) (hguard : 0 < guardTime) :
    (∀ t : ℝ, 0 ≤ t →
      finiteSpectralSurvivalDeviation p
          (finiteObserverHamiltonianVertexPhase t energy) ≤
        4 * finiteLocalizationGeometricTailBound C μ A B N +
          4 * Real.pi / (2 ^ N : ℝ)) ∨
    ∃ exitTime : ℝ, ∃ n : ℕ,
      0 ≤ exitTime ∧
      0 < n ∧
      n ≤ 2 ^ (N * (V * (N + 1) ^ ν - 1)) ∧
      4 * finiteLocalizationGeometricTailBound C μ A B N +
          4 * Real.pi / (2 ^ N : ℝ) <
        finiteSpectralSurvivalDeviation p
          (finiteObserverHamiltonianVertexPhase
            exitTime energy) ∧
      exitTime < (n : ℝ) * (exitTime + guardTime) ∧
      (n : ℝ) * (exitTime + guardTime) ≤
        ((2 ^ (N * (V * (N + 1) ^ ν - 1)) : ℕ) : ℝ) *
          (exitTime + guardTime) ∧
      finiteSpectralSurvivalDeviation p
          (finiteObserverHamiltonianVertexPhase
            ((n : ℝ) * (exitTime + guardTime)) energy) ≤
        4 * finiteLocalizationGeometricTailBound C μ A B N +
          4 * Real.pi / (2 ^ N : ℝ) := by
  classical
  by_cases hnever :
      ∀ t : ℝ, 0 ≤ t →
        finiteSpectralSurvivalDeviation p
            (finiteObserverHamiltonianVertexPhase t energy) ≤
          4 * finiteLocalizationGeometricTailBound C μ A B N +
            4 * Real.pi / (2 ^ N : ℝ)
  · exact Or.inl hnever
  · right
    push Not at hnever
    obtain ⟨exitTime, hexitTime, hexit⟩ := hnever
    let tick : ℝ := exitTime + guardTime
    have htick0 : 0 < tick := by
      dsimp only [tick]
      linarith
    obtain ⟨n, hn0, hnDeadline, hreturn⟩ :=
      exists_finiteAndersonLocalizedSurvival_resolutionScale_recurrence
        p hp hpSum radius N ν V hBall hvolume
        C μ A B hC hμ hA hB hcontract hdecay hshell
        (fun i => tick * energy i)
    have hnOne : 1 ≤ n :=
      Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hn0)
    have hpost : exitTime < (n : ℝ) * tick := by
      calc
        exitTime < tick := by
          dsimp only [tick]
          linarith
        _ = (1 : ℝ) * tick := by ring
        _ ≤ (n : ℝ) * tick := by
          exact mul_le_mul_of_nonneg_right
            (by exact_mod_cast hnOne) htick0.le
    have hdeadlinePhysical :
        (n : ℝ) * tick ≤
          ((2 ^ (N * (V * (N + 1) ^ ν - 1)) : ℕ) : ℝ) *
            tick :=
      mul_le_mul_of_nonneg_right
        (by exact_mod_cast hnDeadline) htick0.le
    have hreturnPhysical :
        finiteSpectralSurvivalDeviation p
            (finiteObserverHamiltonianVertexPhase
              ((n : ℝ) * tick) energy) ≤
          4 * finiteLocalizationGeometricTailBound C μ A B N +
            4 * Real.pi / (2 ^ N : ℝ) := by
      rw [← finiteObserverHamiltonianVertexPhase_scaledEnergy]
      exact hreturn
    exact
      ⟨exitTime, n, hexitTime, hn0, hnDeadline, hexit,
        by simpa only [tick] using hpost,
        by simpa only [tick] using hdeadlinePhysical,
        by simpa only [tick] using hreturnPhysical⟩

end RHTower
