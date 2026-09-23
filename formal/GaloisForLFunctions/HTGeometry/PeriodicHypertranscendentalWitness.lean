import GaloisForLFunctions.HTGeometry.CompExpDescent
import GaloisForLFunctions.HTGeometry.InfiniteGeometricLayerTowerWitness
import GaloisForLFunctions.HTGeometry.PeriodAutonomyDichotomy

/-!
# A periodic hypertranscendental function

Composing the explicit hypertranscendental entire function of `InfiniteGeometricLayerTowerWitness`
with `z ↦ exp (2πi z)` produces an entire function of period one which still satisfies no algebraic
differential equation: the descent through the exponential carries hypertranscendence across.

This inhabits the second case of `autonomous_or_cyclic_hypertranscendental`, so the dichotomy is not
vacuous on either side, and it answers the question the period-subgroup classification left open —
**a hypertranscendental meromorphic function can have a nonzero period**, and then its period group
is infinite cyclic.

* **`hypertranscendental_periodicWitness`**, `periodic_periodicWitness`;
* **`exists_periodic_hypertranscendental`** — the second case of the dichotomy is inhabited.
-/

namespace GaloisForLFunctions.HTGeometry

/-- The explicit hypertranscendental entire function read around the unit circle. -/
noncomputable def periodicWitness : ℂ → ℂ :=
  fun z => dyadicLayerEntireFunction (Complex.exp (2 * Real.pi * Complex.I * z))

theorem twoPiI_ne_zero_periodicHypertranscendentalWitness : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
  simp [Real.pi_ne_zero, Complex.I_ne_zero]

theorem contDiff_periodicWitness : ContDiff ℂ (⊤ : ℕ∞) periodicWitness := by
  refine contDiff_dyadicLayerEntireFunction.comp ?_
  exact Complex.contDiff_exp.comp (contDiff_const.mul contDiff_id)

/-- The witness has period one. -/
theorem periodic_periodicWitness : Function.Periodic periodicWitness 1 := by
  intro z
  show dyadicLayerEntireFunction (Complex.exp (2 * Real.pi * Complex.I * (z + 1)))
      = dyadicLayerEntireFunction (Complex.exp (2 * Real.pi * Complex.I * z))
  have h : (2 * Real.pi * Complex.I : ℂ) * (z + 1)
      = 2 * Real.pi * Complex.I * z + 2 * Real.pi * Complex.I := by ring
  rw [h, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]

/-- **The witness is hypertranscendental.**  Differential algebraicity would descend through the
exponential to the entire layer-tower function, which has none. -/
theorem hypertranscendental_periodicWitness : Hypertranscendental periodicWitness :=
  hypertranscendental_comp_exp contDiff_dyadicLayerEntireFunction twoPiI_ne_zero_periodicHypertranscendentalWitness
    hypertranscendental_dyadicLayerEntireFunction

theorem meromorphicNFOn_periodicWitness : MeromorphicNFOn periodicWitness Set.univ := fun z _ =>
  ((contDiff_periodicWitness.differentiable (by simp)).analyticAt z).meromorphicNFAt

theorem periodSubgroup_periodicWitness_ne_bot : periodSubgroup periodicWitness ≠ ⊥ := by
  intro h
  have hmem : (1 : ℂ) ∈ periodSubgroup periodicWitness := periodic_periodicWitness
  rw [h, AddSubgroup.mem_bot] at hmem
  exact one_ne_zero hmem

/-- **The second case of the period dichotomy is inhabited.**  There is a meromorphic normal-form
function on `ℂ` with a nonzero period that satisfies no algebraic differential equation — hence none
autonomous either, and its period group is infinite cyclic. -/
theorem exists_periodic_hypertranscendental :
    ∃ f : ℂ → ℂ, MeromorphicNFOn f Set.univ ∧ periodSubgroup f ≠ ⊥ ∧ Hypertranscendental f ∧
      ¬ HasAutonomousJetRelation f ∧
      ∃ ω : ℂ, ω ≠ 0 ∧ periodSubgroup f = AddSubgroup.zmultiples ω := by
  refine ⟨periodicWitness, meromorphicNFOn_periodicWitness, periodSubgroup_periodicWitness_ne_bot,
    hypertranscendental_periodicWitness, ?_, ?_⟩
  · rcases autonomous_or_cyclic_hypertranscendental meromorphicNFOn_periodicWitness
      periodSubgroup_periodicWitness_ne_bot with hA | ⟨_, hno, _⟩
    · exact absurd ⟨hA, hypertranscendental_periodicWitness⟩ not_and_autonomous_hypertranscendental
    · exact hno
  · rcases autonomous_or_cyclic_hypertranscendental meromorphicNFOn_periodicWitness
      periodSubgroup_periodicWitness_ne_bot with hA | ⟨_, _, hcyc⟩
    · exact absurd ⟨hA, hypertranscendental_periodicWitness⟩ not_and_autonomous_hypertranscendental
    · exact hcyc

end GaloisForLFunctions.HTGeometry
