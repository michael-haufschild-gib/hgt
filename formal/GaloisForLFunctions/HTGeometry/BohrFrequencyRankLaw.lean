import GaloisForLFunctions.HTGeometry.PhaseFunctionBohrCoefficient
import GaloisForLFunctions.HTGeometry.PhaseRankFromAutonomousEquation

/-!
# The frequency rank of a differentially algebraic quasiperiodic function

The Bohr spectrum of a quasiperiodic function with holomorphic phase observable
is the set of detunings of its active characters, and rational independence
makes the detuning injective, so the rational rank of its Bohr frequency module
is the integer rank of its active lattice.

Combined with the bound on the rank of the active lattice, this is the
frequency-rank law: the rational frequency rank of a quasiperiodic function
with holomorphic phase observable is at most the order of any nonzero
autonomous algebraic differential equation it satisfies whose top derivative is
genuinely present.
-/

open Complex Set Filter Topology

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

variable {d : Type} [Fintype d] [DecidableEq d]

/-- **The rational frequency rank is the integer rank of the active
lattice.** -/
theorem rank_bohrFrequencyModule_eq_rank_activeLattice {ρ omega : d → ℝ}
    (hρ : ∀ j, 0 < ρ j) (hindep : RationallyIndependentFrequency omega)
    {F : (d → ℂ) → ℂ} (hF : AnalyticOnNhd ℂ F (polyannulus ρ)) :
    Module.rank ℚ (bohrFrequencyModule (realPhaseFunction omega F))
      = Module.rank ℤ (activeLattice F) := by
  rw [bohrFrequencyModule, bohrSpectrum_realPhaseFunction hρ hindep hF]
  exact rank_span_characterFrequencySet hindep (activeSupport F)

/-- **The frequency-rank law.**  A quasiperiodic function whose phase
observable is holomorphic on a polyannulus, with rationally independent
frequencies, and which satisfies a nonzero autonomous algebraic differential
equation of order `n` along the real time axis with the top derivative
genuinely present, has rational frequency rank at most `n`. -/
theorem rank_bohrFrequencyModule_le_of_realAutonomousAnnihilator {ρ omega : d → ℝ}
    (hρ : ∀ j, 0 < ρ j) (hindep : RationallyIndependentFrequency omega)
    {F : (d → ℂ) → ℂ} (hF : AnalyticOnNhd ℂ F (polyannulus ρ)) {n : ℕ}
    (hex : ∃ P : Polynomial (MvPolynomial (Fin n) ℂ), P ≠ 0 ∧
      RealAutonomousAnnihilator (phaseFunction omega F) n P)
    (hpos : ∀ Q : Polynomial (MvPolynomial (Fin n) ℂ), Q ≠ 0 →
      RealAutonomousAnnihilator (phaseFunction omega F) n Q → Q.natDegree ≠ 0) :
    Module.rank ℚ (bohrFrequencyModule (realPhaseFunction omega F)) ≤ (n : Cardinal) := by
  rw [rank_bohrFrequencyModule_eq_rank_activeLattice hρ hindep hF]
  exact rank_activeLattice_le_of_realAutonomousAnnihilator hρ hindep hF hex hpos

/-- **The frequency-rank law, with no minimality hypothesis.**  The rational
frequency rank is at most the order of *any* nonzero autonomous algebraic
differential equation the quasiperiodic function satisfies. -/
theorem rank_bohrFrequencyModule_le_of_exists_realAutonomousAnnihilator
    {ρ omega : d → ℝ} (hρ : ∀ j, 0 < ρ j)
    (hindep : RationallyIndependentFrequency omega)
    {F : (d → ℂ) → ℂ} (hF : AnalyticOnNhd ℂ F (polyannulus ρ)) {n : ℕ}
    (hex : ∃ P : Polynomial (MvPolynomial (Fin n) ℂ), P ≠ 0 ∧
      RealAutonomousAnnihilator (phaseFunction omega F) n P) :
    Module.rank ℚ (bohrFrequencyModule (realPhaseFunction omega F))
      ≤ (n : Cardinal) := by
  rw [rank_bohrFrequencyModule_eq_rank_activeLattice hρ hindep hF]
  exact rank_activeLattice_le_of_exists_realAutonomousAnnihilator hρ hindep hF hex

/-- **The hypertranscendence consequence.**  If the rational frequency rank
exceeds `n`, no nonzero autonomous algebraic differential equation of order `n`
annihilates the quasiperiodic function. -/
theorem not_realAutonomousAnnihilator_of_lt_rank {ρ omega : d → ℝ}
    (hρ : ∀ j, 0 < ρ j) (hindep : RationallyIndependentFrequency omega)
    {F : (d → ℂ) → ℂ} (hF : AnalyticOnNhd ℂ F (polyannulus ρ)) {n : ℕ}
    (hrank : (n : Cardinal) <
      Module.rank ℚ (bohrFrequencyModule (realPhaseFunction omega F))) :
    ¬ ∃ P : Polynomial (MvPolynomial (Fin n) ℂ), P ≠ 0 ∧
      RealAutonomousAnnihilator (phaseFunction omega F) n P := fun hex =>
  absurd (rank_bohrFrequencyModule_le_of_exists_realAutonomousAnnihilator
    hρ hindep hF hex) (not_le.2 hrank)

end

end GaloisForLFunctions.HTGeometry
