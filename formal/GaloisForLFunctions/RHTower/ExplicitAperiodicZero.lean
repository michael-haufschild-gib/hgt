import GaloisForLFunctions.RHTower.ClockEscape

/-!
# Explicit aperiodic zero and one-clock escape

The linear carrier `z ↦ z - ρ` supplies the previously providerless `AperiodicZeroAt` interface:
its zero at `ρ` cannot repeat along any positive vertical period.  Instantiating the finite-clock
escape theorem with the constant family and the singleton period inventory `{1}` removes every
remaining abstract input and gives a concrete unconditional clock-escape statement.
-/

open Complex Filter Topology Set

namespace RHTower

noncomputable section

/-- The linear carrier with its unique zero at `ρ`. -/
def simpleZeroAt (ρ z : ℂ) : ℂ := z - ρ

/-- A simple zero is aperiodic: a nonzero vertical translation cannot return to its unique zero. -/
theorem simpleZeroAt_aperiodicZeroAt (ρ : ℂ) :
    AperiodicZeroAt (simpleZeroAt ρ) ρ := by
  refine ⟨by simp [simpleZeroAt], ?_⟩
  rintro ⟨T, hT, hprog⟩
  have h := hprog 1
  simp [simpleZeroAt] at h
  exact (ne_of_gt hT) h

private theorem simpleZeroAt_const_locallyUniform (ρ : ℂ) :
    TendstoLocallyUniformlyOn (fun _ : ℕ => simpleZeroAt ρ) (simpleZeroAt ρ)
      atTop Set.univ := by
  intro u hu x hx
  refine ⟨Set.univ, univ_mem, Eventually.of_forall fun n y hy => ?_⟩
  exact refl_mem_uniformity hu

/-- Unconditional one-clock escape: no sequence of progression-riding zeros of the constant
linear family can converge to its aperiodic zero when the only allowed period is one. -/
theorem simpleZeroAt_singleClock_escape (ρ : ℂ) :
    ¬ ∃ (zn : ℕ → ℂ) (Tn : ℕ → ℝ),
      Tendsto zn atTop (nhds ρ) ∧ (∀ n, zn n ∈ (Set.univ : Set ℂ)) ∧
        (∀ n, Tn n ∈ ({1} : Finset ℝ)) ∧
          ∀ n, ∀ k : ℤ,
            simpleZeroAt ρ (zn n + (k * Tn n) * Complex.I) = 0 := by
  exact aperiodic_zero_clock_escape
    (fun w hw t => Set.mem_univ _) (simpleZeroAt_const_locallyUniform ρ)
    (continuous_id.sub continuous_const).continuousOn (Set.mem_univ ρ)
    (simpleZeroAt_aperiodicZeroAt ρ) (by simp)

end

end RHTower
