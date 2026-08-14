import GaloisForLFunctions.HTGeometry.PrimePhaseBudgetRank
import GaloisForLFunctions.HTGeometry.BohrSpectrumProduct

/-!
# The frequency budget at the minimal autonomous order

The frequency-rank law bounds the rational Bohr-frequency rank of a quasiperiodic function by the
order of *any* nonzero autonomous algebraic differential equation it satisfies.  Applying it at the
least such order gives the sharp form of the budget: the rank is at most the **minimal autonomous
order** of the function, which is exactly its Kolchin jet capacity
(`kolchinJetCapacity_eq_differentialOrder`).

Consequently a carrier that retains `π′(N)` prime-logarithm frequencies must have Kolchin jet
capacity at least `π′(N)` — the capacity floor, with the constant `1` rather than `1/2`.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

open scoped BoundedContinuousFunction

noncomputable section

/-- The orders carrying a nonzero autonomous algebraic differential relation. -/
def autonomousOrderSet (f : ℂ → ℂ) : Set ℕ :=
  {n : ℕ | ∃ P : Polynomial (MvPolynomial (Fin n) ℂ), P ≠ 0 ∧ RealAutonomousAnnihilator f n P}

/-- **The minimal autonomous order** of a function: the least order of a nonzero autonomous
algebraic differential relation it satisfies. -/
def autonomousMinimalOrder (f : ℂ → ℂ) : ℕ := sInf (autonomousOrderSet f)

theorem autonomousOrderSet_nonempty {f : ℂ → ℂ} {n : ℕ}
    (hex : ∃ P : Polynomial (MvPolynomial (Fin n) ℂ), P ≠ 0 ∧ RealAutonomousAnnihilator f n P) :
    (autonomousOrderSet f).Nonempty := ⟨n, hex⟩

/-- A nonzero autonomous relation of the minimal order exists. -/
theorem exists_realAutonomousAnnihilator_autonomousMinimalOrder {f : ℂ → ℂ} {n : ℕ}
    (hex : ∃ P : Polynomial (MvPolynomial (Fin n) ℂ), P ≠ 0 ∧ RealAutonomousAnnihilator f n P) :
    ∃ P : Polynomial (MvPolynomial (Fin (autonomousMinimalOrder f)) ℂ), P ≠ 0 ∧
      RealAutonomousAnnihilator f (autonomousMinimalOrder f) P :=
  Nat.sInf_mem (autonomousOrderSet_nonempty hex)

theorem autonomousMinimalOrder_le {f : ℂ → ℂ} {n : ℕ}
    (hex : ∃ P : Polynomial (MvPolynomial (Fin n) ℂ), P ≠ 0 ∧ RealAutonomousAnnihilator f n P) :
    autonomousMinimalOrder f ≤ n := Nat.sInf_le hex

variable {d : Type} [Fintype d] [DecidableEq d]

/-- **The frequency budget at the minimal order.**  The rational Bohr-frequency rank of a
quasiperiodic function with holomorphic phase observable is at most its minimal autonomous order,
i.e. at most its Kolchin jet capacity. -/
theorem rank_bohrFrequencyModule_le_autonomousMinimalOrder {ρ omega : d → ℝ}
    (hρ : ∀ j, 0 < ρ j) (hindep : RationallyIndependentFrequency omega)
    {F : (d → ℂ) → ℂ} (hF : AnalyticOnNhd ℂ F (polyannulus ρ)) {n : ℕ}
    (hex : ∃ P : Polynomial (MvPolynomial (Fin n) ℂ), P ≠ 0 ∧
      RealAutonomousAnnihilator (phaseFunction omega F) n P) :
    Module.rank ℚ (bohrFrequencyModule (realPhaseFunction omega F))
      ≤ (autonomousMinimalOrder (phaseFunction omega F) : Cardinal) :=
  rank_bohrFrequencyModule_le_of_exists_realAutonomousAnnihilator hρ hindep hF
    (exists_realAutonomousAnnihilator_autonomousMinimalOrder hex)

/-- **The capacity floor.**  A carrier retaining every prime logarithm below `N` in its Bohr
frequency module has minimal autonomous order — hence Kolchin jet capacity — at least `π′(N)`. -/
theorem primeCounting_le_autonomousMinimalOrder {ρ omega : d → ℝ}
    (hρ : ∀ j, 0 < ρ j) (hindep : RationallyIndependentFrequency omega)
    {F : (d → ℂ) → ℂ} (hF : AnalyticOnNhd ℂ F (polyannulus ρ)) {n N : ℕ}
    (hex : ∃ P : Polynomial (MvPolynomial (Fin n) ℂ), P ≠ 0 ∧
      RealAutonomousAnnihilator (phaseFunction omega F) n P)
    (hΓ : ∀ p ∈ N.primesBelow,
      (Real.log (p : ℕ) : ℝ) ∈ bohrFrequencyModule (realPhaseFunction omega F)) :
    Nat.primeCounting' N ≤ autonomousMinimalOrder (phaseFunction omega F) :=
  primeCounting_le_of_realAutonomousAnnihilator_of_primeLog_mem hρ hindep hF
    (exists_realAutonomousAnnihilator_autonomousMinimalOrder hex) hΓ

/-- **The cofinal capacity law.**  No single autonomous order carries every prime cutoff: if the
carriers at cutoff `N` all satisfy a relation of one fixed order `n`, the retained prime count is
bounded by `n`, so beyond `n` primes the capacity must grow. -/
theorem not_realAutonomousAnnihilator_of_lt_primeCounting {ρ omega : d → ℝ}
    (hρ : ∀ j, 0 < ρ j) (hindep : RationallyIndependentFrequency omega)
    {F : (d → ℂ) → ℂ} (hF : AnalyticOnNhd ℂ F (polyannulus ρ)) {n N : ℕ}
    (hΓ : ∀ p ∈ N.primesBelow,
      (Real.log (p : ℕ) : ℝ) ∈ bohrFrequencyModule (realPhaseFunction omega F))
    (hlt : n < Nat.primeCounting' N) :
    ¬ ∃ P : Polynomial (MvPolynomial (Fin n) ℂ), P ≠ 0 ∧
      RealAutonomousAnnihilator (phaseFunction omega F) n P :=
  not_realAutonomousAnnihilator_of_primeLog_mem hρ hindep hF hΓ hlt

/-- **Observable form of the budget.**  An observable whose Bohr spectrum lies inside the frequency
module of the carrier has frequency rank at most that of the carrier. -/
theorem rank_bohrFrequencyModule_le_of_bohrSpectrum_subset {g f : ℝ → ℂ}
    (hsub : bohrSpectrum g ⊆ (bohrFrequencyModule f : Set ℝ)) :
    Module.rank ℚ (bohrFrequencyModule g) ≤ Module.rank ℚ (bohrFrequencyModule f) :=
  Submodule.rank_mono (Submodule.span_le.mpr hsub)

/-- The frequency budget passes to the square of a carrier: squaring cannot create new rational
frequency directions. -/
theorem rank_bohrFrequencyModule_mul_self_le {f : ℝ →ᵇ ℂ}
    (hf : UniformContinuous fun x => f x) (htb : HasTotallyBoundedOrbit fun x => f x) :
    Module.rank ℚ (bohrFrequencyModule (fun t => f t * f t))
      ≤ Module.rank ℚ (bohrFrequencyModule (fun x => f x)) := by
  refine rank_bohrFrequencyModule_le_of_bohrSpectrum_subset ?_
  intro lam hlam
  have hmem := bohrSpectrum_mul_subset_closure hf htb hf htb hlam
  rw [Set.union_self] at hmem
  have hle : AddSubgroup.closure (bohrSpectrum fun x => f x)
      ≤ (bohrFrequencyModule (fun x => f x)).toAddSubgroup := by
    refine AddSubgroup.closure_le _ |>.mpr ?_
    exact subset_bohrFrequencyModule _
  exact hle hmem

end

end GaloisForLFunctions.HTGeometry
