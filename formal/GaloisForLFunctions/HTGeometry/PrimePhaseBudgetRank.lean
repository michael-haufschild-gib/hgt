import GaloisForLFunctions.RHTower.PrimeLogPhaseBudget
import GaloisForLFunctions.HTGeometry.BohrFrequencyRankLaw
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

/-!
# The prime phase-budget inequality

A rational subspace of the reals containing every prime logarithm below `N` has dimension at least
the prime-counting value: unique factorization makes the prime logarithms `ℤ`-independent, hence
`ℚ`-independent, and independence transfers to any subspace containing them.  Consequently any
numerical bound on the dimension of a recurrent Bohr-frequency group bounds the number of prime
directions the group can carry.
-/

namespace GaloisForLFunctions.HTGeometry

open Module

noncomputable section

/-- The logarithms of the primes below `N` are `ℚ`-linearly independent. -/
theorem primeLog_primesBelow_linearIndependent_rat (N : ℕ) :
    LinearIndependent ℚ (fun p : (N.primesBelow : Finset ℕ) => Real.log (p : ℕ)) :=
  (LinearIndependent.iff_fractionRing ℤ ℚ).mp
    (GaloisForLFunctions.primeLog_primesBelow_linearIndependent N)

/-- **Prime phase budget.**  A rational subspace of `ℝ` containing every prime logarithm below `N`
has dimension at least `π'(N)`. -/
theorem primeCounting_le_finrank_of_primeLog_mem {N : ℕ} (Γ : Submodule ℚ ℝ)
    [FiniteDimensional ℚ Γ]
    (hΓ : ∀ p ∈ N.primesBelow, (Real.log (p : ℕ) : ℝ) ∈ Γ) :
    Nat.primeCounting' N ≤ finrank ℚ Γ := by
  classical
  have hindep : LinearIndependent ℚ
      (fun p : (N.primesBelow : Finset ℕ) => (⟨Real.log (p : ℕ), hΓ (p : ℕ) p.2⟩ : Γ)) := by
    refine LinearIndependent.of_comp Γ.subtype ?_
    have hcomp : (Γ.subtype ∘ fun p : (N.primesBelow : Finset ℕ) =>
        (⟨Real.log (p : ℕ), hΓ (p : ℕ) p.2⟩ : Γ)) =
        fun p : (N.primesBelow : Finset ℕ) => Real.log (p : ℕ) := by
      funext p
      rfl
    rw [hcomp]
    exact primeLog_primesBelow_linearIndependent_rat N
  have hcard := hindep.fintype_card_le_finrank
  have hfin : Fintype.card (N.primesBelow : Finset ℕ) = Nat.primeCounting' N := by
    rw [Fintype.card_coe]
    exact Nat.primesBelow_card_eq_primeCounting' N
  rw [hfin] at hcard
  exact hcard

/-- **The phase-budget inequality `(37)`.**  If the recurrent frequency group contains every prime
logarithm below `N` and its rational dimension is bounded by `B`, then `π'(N) ≤ B`. -/
theorem primeCounting_le_of_primeLog_mem_of_finrank_le {N B : ℕ} (Γ : Submodule ℚ ℝ)
    [FiniteDimensional ℚ Γ]
    (hΓ : ∀ p ∈ N.primesBelow, (Real.log (p : ℕ) : ℝ) ∈ Γ)
    (hB : finrank ℚ Γ ≤ B) : Nat.primeCounting' N ≤ B :=
  le_trans (primeCounting_le_finrank_of_primeLog_mem Γ hΓ) hB

/-- **The complexity form `(38)`.**  With `B = δ + 2·m·(n+1)` the same inequality reads as the
lower bound `m(n+1) ≥ (π'(N) − δ)/2` on the atlas-and-order budget. -/
theorem two_mul_atlasOrder_ge_of_primeLog_mem {N δ m n : ℕ} (Γ : Submodule ℚ ℝ)
    [FiniteDimensional ℚ Γ]
    (hΓ : ∀ p ∈ N.primesBelow, (Real.log (p : ℕ) : ℝ) ∈ Γ)
    (hB : finrank ℚ Γ ≤ δ + 2 * (m * (n + 1))) :
    Nat.primeCounting' N ≤ δ + 2 * (m * (n + 1)) :=
  primeCounting_le_of_primeLog_mem_of_finrank_le Γ hΓ hB

/-- The cardinal form of the prime phase budget. -/
theorem primeCounting_le_rank_of_primeLog_mem {N : ℕ} (Γ : Submodule ℚ ℝ)
    (hΓ : ∀ p ∈ N.primesBelow, (Real.log (p : ℕ) : ℝ) ∈ Γ) :
    (Nat.primeCounting' N : Cardinal) ≤ Module.rank ℚ Γ := by
  classical
  have hindep : LinearIndependent ℚ
      (fun p : (N.primesBelow : Finset ℕ) => (⟨Real.log (p : ℕ), hΓ (p : ℕ) p.2⟩ : Γ)) := by
    refine LinearIndependent.of_comp Γ.subtype ?_
    have hcomp : (Γ.subtype ∘ fun p : (N.primesBelow : Finset ℕ) =>
        (⟨Real.log (p : ℕ), hΓ (p : ℕ) p.2⟩ : Γ)) =
        fun p : (N.primesBelow : Finset ℕ) => Real.log (p : ℕ) := by
      funext p
      rfl
    rw [hcomp]
    exact primeLog_primesBelow_linearIndependent_rat N
  have hcard := hindep.cardinal_le_rank
  have hmk : (Cardinal.mk ((N.primesBelow : Finset ℕ) : Type))
      = (Nat.primeCounting' N : Cardinal) := by
    rw [Cardinal.mk_fintype, Fintype.card_coe, Nat.primesBelow_card_eq_primeCounting']
  rwa [hmk] at hcard

/-- **The unconditional phase-budget law.**  A quasiperiodic function with holomorphic phase
observable that satisfies a nonzero autonomous algebraic differential equation of order `n` cannot
carry more prime-logarithm directions in its Bohr frequency module than that order: if every prime
logarithm below `N` is a Bohr frequency, then `π′(N) ≤ n`. -/
theorem primeCounting_le_of_realAutonomousAnnihilator_of_primeLog_mem
    {d : Type} [Fintype d] [DecidableEq d] {ρ omega : d → ℝ}
    (hρ : ∀ j, 0 < ρ j) (hindep : RationallyIndependentFrequency omega)
    {F : (d → ℂ) → ℂ} (hF : AnalyticOnNhd ℂ F (polyannulus ρ)) {n N : ℕ}
    (hex : ∃ P : Polynomial (MvPolynomial (Fin n) ℂ), P ≠ 0 ∧
      RealAutonomousAnnihilator (phaseFunction omega F) n P)
    (hΓ : ∀ p ∈ N.primesBelow,
      (Real.log (p : ℕ) : ℝ) ∈ bohrFrequencyModule (realPhaseFunction omega F)) :
    Nat.primeCounting' N ≤ n := by
  have h1 := primeCounting_le_rank_of_primeLog_mem
    (bohrFrequencyModule (realPhaseFunction omega F)) hΓ
  have h2 := rank_bohrFrequencyModule_le_of_exists_realAutonomousAnnihilator hρ hindep hF hex
  have hchain : (Nat.primeCounting' N : Cardinal) ≤ (n : Cardinal) := le_trans h1 h2
  exact_mod_cast hchain

/-- **Hypertranscendence from prime-log frequency saturation.**  If more than `n` prime logarithms
below `N` are Bohr frequencies, no nonzero autonomous algebraic differential equation of order `n`
annihilates the phase function. -/
theorem not_realAutonomousAnnihilator_of_primeLog_mem
    {d : Type} [Fintype d] [DecidableEq d] {ρ omega : d → ℝ}
    (hρ : ∀ j, 0 < ρ j) (hindep : RationallyIndependentFrequency omega)
    {F : (d → ℂ) → ℂ} (hF : AnalyticOnNhd ℂ F (polyannulus ρ)) {n N : ℕ}
    (hΓ : ∀ p ∈ N.primesBelow,
      (Real.log (p : ℕ) : ℝ) ∈ bohrFrequencyModule (realPhaseFunction omega F))
    (hlt : n < Nat.primeCounting' N) :
    ¬ ∃ P : Polynomial (MvPolynomial (Fin n) ℂ), P ≠ 0 ∧
      RealAutonomousAnnihilator (phaseFunction omega F) n P := by
  intro hex
  exact absurd (primeCounting_le_of_realAutonomousAnnihilator_of_primeLog_mem
    hρ hindep hF hex hΓ) (not_le.2 hlt)

end

end GaloisForLFunctions.HTGeometry
