import GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy.CriticalEnergyFamilies
import GaloisForLFunctions.RHTower.AdmissionBelowHalfDampingAboveTheZeroWidth

/-!
# The damped Möbius critical energy

The arithmetic instance of record.  With

`A_ε(n) = Σ_{d ≤ n} μ(d) d^{-ε} ⌊n/d⌋ − n·Re(1/ζ(1+ε))`,
`E_T(ε) = Σ_{n ≤ T} A_ε(n)² / (n(n+1))`,

the source is fixed before any closure: every coefficient, the exact pole subtraction and the
observation weight are named, and nothing is selected from the zeros.

Two dictionary entries fix what continuation has to deliver:

* admission at a positive damping is membership in `receiverDampings`;
* cofinal admission is the Riemann hypothesis.

Half damping is the unconditional endpoint of the family, and under RH every positive damping is
admitted.  So the continuation statements this programme seeks are exactly as strong as RH — not
stronger, and not a disguised extra hypothesis.
-/

open Set Filter Finset RHTower

namespace GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy

noncomputable section
set_option autoImplicit false

/-- The critical energy of the programme: the pronic energy, to horizon `T`, of the centred prefix
of the power-damped Möbius row at damping `ε`. -/
abbrev dampedMobiusEnergy : ℝ → ℕ → ℝ := pmPowerDampedDivisorDiscreteEnergy

theorem dampedMobiusEnergy_nonneg (ε : ℝ) (T : ℕ) : 0 ≤ dampedMobiusEnergy ε T :=
  Finset.sum_nonneg fun n _ => by positivity

/-- The energy is nondecreasing in the observation horizon: each horizon adds one pronic cell. -/
theorem dampedMobiusEnergy_mono (ε : ℝ) : Monotone (dampedMobiusEnergy ε) := by
  refine monotone_nat_of_le_succ fun T => ?_
  simp only [dampedMobiusEnergy, pmPowerDampedDivisorDiscreteEnergy_eq_range,
    Finset.sum_range_succ]
  have : (0 : ℝ) ≤ pmPowerDampedCenteredDivisorPrefix ε (T + 1) ^ 2 /
      (((T : ℝ) + 1) * ((T : ℝ) + 2)) := by positivity
  linarith

/-- **Dictionary.**  Admission at a positive damping is membership in `receiverDampings`. -/
theorem mem_receiverDampings_iff_admits {ε : ℝ} (hε : 0 < ε) :
    ε ∈ receiverDampings ↔ Admits dampedMobiusEnergy ε :=
  ⟨fun h => h.2, fun h => ⟨hε, h⟩⟩

/-- Half damping is the unconditional endpoint: every damping `ε ≥ ½` is admitted. -/
theorem admits_dampedMobiusEnergy_of_half_le {ε : ℝ} (hε : (1 / 2 : ℝ) ≤ ε) :
    Admits dampedMobiusEnergy ε :=
  exists_pmPowerDampedDivisorDiscreteEnergy_budget_of_half_le hε

/-- **Dictionary.**  Cofinal admission of the damped Möbius energy is the Riemann hypothesis. -/
theorem riemannHypothesis_iff_cofinallyAdmits :
    RiemannHypothesis ↔ CofinallyAdmits dampedMobiusEnergy :=
  riemannHypothesis_iff_cofinal_budget

/-- Under the Riemann hypothesis every positive damping is admitted. -/
theorem admits_dampedMobiusEnergy_of_riemannHypothesis (h : RiemannHypothesis) {ε : ℝ}
    (hε : 0 < ε) : Admits dampedMobiusEnergy ε :=
  (mem_receiverDampings_iff_admits hε).mp
    (Ioi_zero_subset_receiverDampings_of_riemannHypothesis h hε)

end

end GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy
