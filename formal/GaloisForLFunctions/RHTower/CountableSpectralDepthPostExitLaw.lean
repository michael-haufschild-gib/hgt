import GaloisForLFunctions.RHTower.CountableSpectralHamiltonianRealization
import GaloisForLFunctions.RHTower.CountableSpectralDepthFirstReturnLaw

/-!
# Post-exit countable spectral-depth recurrence

The spectral-depth deadline is not merely a positive-time hit.  For every
finite checkpoint, rescaling the phase packet by the next integer tick
forces a strictly later return with the same full-packet defect and the same
spectral-depth entropy.  Through the exact diagonal Hamiltonian realization,
this is a genuine survival-amplitude return after any witnessed exit.
-/

noncomputable section

namespace RHTower

/--
Every finite checkpoint is followed by a countable pure-point survival
return.  The one-block spectral-depth deadline `T` is unchanged; only the
physical deadline is dilated by the first integer tick after the checkpoint.
-/
theorem exists_countableSpectralDepth_postCheckpointReturn
    (p : ℕ → ℝ) (hp : ∀ k, 0 ≤ p k)
    (hsum : Summable p) (htotal : ∑' k, p k = 1)
    (M : ℕ) (hM : 2 ≤ M)
    (hmass : 0 < summableWeightedHeadMass p M)
    (pivot : Fin M)
    {eta lam : ℝ} (heta0 : 0 < eta) (heta1 : eta ≤ 1)
    (hlam : 0 < lam)
    (hwater :
      projectiveWaterMass
          (normalizedWeightedHeadWeight p M) pivot
          (summableWeightedHeadMass p M * lam) ≤ eta)
    (x : ℕ → UnitAddCircle) (checkpoint : ℕ) :
    ∃ T N : ℕ,
      checkpoint < N ∧
      N ≤ (checkpoint + 1) * T ∧
      CountableSpectralHamiltonianCoherenceAt p hp hsum x
        (countableSpectralDepthDefect p M eta) N ∧
      Real.log (T : ℝ) ≤
        countableSpectralDepthEntropy p M lam +
          countableSpectralDepthResolutionCost M := by
  obtain ⟨T, hreturn, hlog⟩ :=
    exists_countableWeightedCoherenceDeadline_headFixedWaterCeiling
      p hp hsum htotal M hM hmass pivot
      heta0 heta1 hlam hwater
  obtain ⟨m, hm0, hmT, hmreturn⟩ :=
    hreturn (fun k =>
      (checkpoint + 1 : ℝ) * torusRealFrequency (x k))
  let N : ℕ := m * (checkpoint + 1)
  have hm1 : 1 ≤ m :=
    Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hm0)
  have hcheckpoint : checkpoint < N := by
    calc
      checkpoint < 1 * (checkpoint + 1) := by omega
      _ ≤ m * (checkpoint + 1) :=
        Nat.mul_le_mul_right (checkpoint + 1) hm1
  have hdeadline : N ≤ (checkpoint + 1) * T := by
    have hmul :=
      Nat.mul_le_mul_right (checkpoint + 1) hmT
    simpa only [N, Nat.mul_comm] using hmul
  have hphase :
      (fun k =>
        Complex.exp
          (Complex.I *
            ((((m : ℝ) *
              ((checkpoint + 1 : ℝ) *
                torusRealFrequency (x k)) : ℝ) : ℂ)))) =
        (fun k =>
          fourier 1 ((((N : ℕ) : ℤ) • x k))) := by
    funext k
    rw [← exp_torusRealFrequency_eq_fourier_zsmul (x k) N]
    congr 2
    push_cast
    dsimp only [N]
    norm_num [Nat.cast_add, Nat.cast_mul]
    ring
  have hcoherence :
      CountableTorusWeightedCoherenceAt p x
        (countableSpectralDepthDefect p M eta) N := by
    refine ⟨by
      dsimp only [N]
      positivity, ?_⟩
    rw [← hphase]
    simpa only [countableSpectralDepthDefect] using hmreturn
  have hphysical :
      CountableSpectralHamiltonianCoherenceAt p hp hsum x
        (countableSpectralDepthDefect p M eta) N :=
    (countableTorusWeightedCoherenceAt_iff_hamiltonian
      p hp hsum x (countableSpectralDepthDefect p M eta) N).mp
        hcoherence
  refine ⟨T, N, hcheckpoint, hdeadline, hphysical, ?_⟩
  simpa only [countableSpectralDepthEntropy,
    countableSpectralDepthResolutionCost] using hlog

/--
If the survival orbit has exited the spectral-depth neighborhood at a
finite checkpoint, the return supplied above is strictly post-exit.
-/
theorem exists_countableSpectralDepth_postExitReturn
    (p : ℕ → ℝ) (hp : ∀ k, 0 ≤ p k)
    (hsum : Summable p) (htotal : ∑' k, p k = 1)
    (M : ℕ) (hM : 2 ≤ M)
    (hmass : 0 < summableWeightedHeadMass p M)
    (pivot : Fin M)
    {eta lam : ℝ} (heta0 : 0 < eta) (heta1 : eta ≤ 1)
    (hlam : 0 < lam)
    (hwater :
      projectiveWaterMass
          (normalizedWeightedHeadWeight p M) pivot
          (summableWeightedHeadMass p M * lam) ≤ eta)
    (x : ℕ → UnitAddCircle) (exitIndex : ℕ)
    (hexit :
      ¬CountableSpectralHamiltonianCoherenceAt p hp hsum x
        (countableSpectralDepthDefect p M eta) exitIndex) :
    ∃ T N : ℕ,
      exitIndex < N ∧
      N ≤ (exitIndex + 1) * T ∧
      ¬CountableSpectralHamiltonianCoherenceAt p hp hsum x
        (countableSpectralDepthDefect p M eta) exitIndex ∧
      CountableSpectralHamiltonianCoherenceAt p hp hsum x
        (countableSpectralDepthDefect p M eta) N ∧
      Real.log (T : ℝ) ≤
        countableSpectralDepthEntropy p M lam +
          countableSpectralDepthResolutionCost M := by
  obtain ⟨T, N, hpost, hdeadline, hreturn, hlog⟩ :=
    exists_countableSpectralDepth_postCheckpointReturn
      p hp hsum htotal M hM hmass pivot
      heta0 heta1 hlam hwater x exitIndex
  exact ⟨T, N, hpost, hdeadline, hexit, hreturn, hlog⟩

end RHTower
