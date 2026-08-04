import GaloisForLFunctions.HTGeometry.WaveDecayingReflection
import GaloisForLFunctions.HTGeometry.WaveOperatorBridge
import GaloisForLFunctions.HTGeometry.WaveCauchyUniqueness

/-!
# Uniqueness for the corpus's clock equation, without compact support

The decaying estimate stated in the corpus's own language: a smooth field on events whose pullback
to time-space coordinates satisfies the decay conditions, and whose value and time derivative vanish
on the initial slice, vanishes at every event. This is the form a Fourier-built probe can meet — it
decays rather than vanishing outside a compact set.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped ContDiff

section EventDecaying

variable {d : ℕ} {u V : (Fin (d + 1) → ℝ) → ℝ}

/-- **Vanishing Cauchy data forces a decaying solution of the corpus's clock equation to vanish.** -/
theorem eq_zero_of_solvesPotentialWave_of_decaying (hu : ContDiff ℝ ∞ u)
    (hdec : DecayingSolution (fun q => u (eventCLM d q)) (fun q => V (eventCLM d q)))
    {M : ℝ} (hM : ∀ y, |V y| ≤ M)
    (hval : ∀ x : Fin d → ℝ, u (Fin.cons 0 x) = 0)
    (hder : ∀ x : Fin d → ℝ, coordPartial 0 u (Fin.cons 0 x) = 0)
    (y : Fin (d + 1) → ℝ) : u y = 0 := by
  have hev : ∀ x : Fin d → ℝ, eventCLM d ((0 : ℝ), x) = Fin.cons 0 x := by
    intro x
    rw [eventCLM_apply]
  have hvalc : ∀ x : Fin d → ℝ,
      (fun q : ℝ × (Fin d → ℝ) => u (eventCLM d q)) ((0 : ℝ), x) = 0 := by
    intro x
    show u (eventCLM d ((0 : ℝ), x)) = 0
    rw [hev x]
    exact hval x
  have hderc : ∀ x : Fin d → ℝ,
      waveDirDeriv (timeDir d) (fun q : ℝ × (Fin d → ℝ) => u (eventCLM d q)) ((0 : ℝ), x)
        = 0 := by
    intro x
    rw [waveDirDeriv_timeDir_comp_eventCLM hu, hev x]
    exact hder x
  have h0 : waveEnergy (fun q : ℝ × (Fin d → ℝ) => u (eventCLM d q)) 0 = 0 :=
    waveEnergy_eq_zero_of_slice_zero (contDiff_comp_eventCLM hu) hvalc hderc
  have hvan := eq_zero_of_waveEnergy_zero_of_decaying_all hdec
    (fun p => hM (eventCLM d p)) h0 (y 0) (Fin.tail y)
  have hres : u (eventCLM d ((y 0, Fin.tail y) : ℝ × (Fin d → ℝ))) = 0 := hvan
  rwa [eventCLM_surjective y] at hres

end EventDecaying

end GaloisForLFunctions.HTGeometry
