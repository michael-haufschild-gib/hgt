import GaloisForLFunctions.RHTower.CCM.CCMActualHeadWallGramLightConeCircleCompletion

/-!
# Affine center jet of the completed actual wall Gram

The literal reflected wall chord has zero center value.  Its canonical complex completion does
not: the chord-complement coordinate restores exactly one critical Mellin atom, while the Suzuki
light coordinate supplies a strictly positive oriented first jet.  This isolates the only local
affine datum available to a source-faithful two-channel completion.  It does not assert a global
prime--polar--Gamma cancellation or a reverse-prime bound.
-/

open Complex

noncomputable section
namespace RHTower

/-- The completed wall phase restores the literal critical Mellin atom at spectral center. -/
theorem ccmActualHeadWallLightCompletedPhase_zero
    (p : Nat.Primes) (e : ℕ) :
    ccmActualHeadWallLightCompletedPhase 0 p e =
      (criticalMellinAtomWeight (xiGammaEulerValuationNat (p, e)) : ℂ) := by
  unfold ccmActualHeadWallLightCompletedPhase
  dsimp only
  rw [normSq_ccmActualHeadMellinWallChord,
    ccmActualHeadMatchedWallLightImbalance_eq]
  simp

/-- The oriented coordinate has the literal positive-clock critical Mellin first jet. -/
theorem deriv_ccmActualHeadWallLightCompletedPhase_im_zero
    (p : Nat.Primes) (e : ℕ) :
    deriv (fun xi : ℝ => (ccmActualHeadWallLightCompletedPhase xi p e).im) 0 =
      criticalMellinAtomWeight (xiGammaEulerValuationNat (p, e)) *
        (2 * Real.pi * Real.log (xiGammaEulerValuationNat (p, e))) := by
  let n := xiGammaEulerValuationNat (p, e)
  let w := criticalMellinAtomWeight n
  have him : HasDerivAt (ccmActualHeadMatchedWallLightImbalance p e)
      (w * (2 * Real.pi * Real.log n)) 0 := by
    have h := hasDerivAt_ccmActualHeadMatchedWallLightImbalance p e 0
    rw [ccmActualHeadMatchedWallLightImbalanceFirstJet_zero] at h
    simpa only [n, w] using h
  have hphase : (fun xi : ℝ =>
      (ccmActualHeadWallLightCompletedPhase xi p e).im) =
      ccmActualHeadMatchedWallLightImbalance p e := by
    funext xi
    simp [ccmActualHeadWallLightCompletedPhase]
  rw [hphase]
  simpa only [n, w] using him.deriv

/-- The restored oriented jet is strictly positive at every literal prime-power wall. -/
theorem deriv_ccmActualHeadWallLightCompletedPhase_im_zero_pos
    (p : Nat.Primes) (e : ℕ) :
    0 < deriv (fun xi : ℝ => (ccmActualHeadWallLightCompletedPhase xi p e).im) 0 := by
  rw [deriv_ccmActualHeadWallLightCompletedPhase_im_zero]
  have hw : 0 < criticalMellinAtomWeight (xiGammaEulerValuationNat (p, e)) := by
    rw [criticalMellinAtomWeight_primePower_eq_sq_suzukiCriticalEntryWallBareAmplitude]
    exact sq_pos_of_pos (suzukiCriticalEntryWallBareAmplitude_pos p e)
  have hlog : 0 < Real.log (xiGammaEulerValuationNat (p, e) : ℝ) :=
    Real.log_pos (by exact_mod_cast (one_lt_xiGammaEulerValuationNat p e))
  positivity

end RHTower
