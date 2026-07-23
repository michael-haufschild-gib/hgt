import GaloisForLFunctions.RHTower.GammaCellNonrealMobility
import GaloisForLFunctions.RHTower.PeriodicityDichotomy

/-!
# Gamma-cell periodic nonreal mobility universality law

Real-zero-free nonreal strip mobility and the periodicity dichotomy are compatible in only one
way: the mobile off-line zero cannot enter the dichotomy's critical-line branch, so it must expand
to a full two-sided vertical progression.  The result is first proved for any carrier class and
then specialized to the gamma-completed cell.
-/

open Complex

namespace RHTower

noncomputable section

/-- A class has periodic real-zero-free nonreal strip mobility when one member has no real
open-strip zero but carries a nonreal off-line zero whose full vertical arithmetic progression
also consists of zeros. -/
def RealZeroFreeNonrealPeriodicStripMobility (C : (ℂ → ℂ) → Prop) : Prop :=
  ∃ f : ℂ → ℂ, ∃ ρ : ℂ, ∃ T : ℝ, C f ∧
    (∀ σ : ℝ, 0 < σ → σ < 1 → f (σ : ℂ) ≠ 0) ∧
    0 < ρ.re ∧ ρ.re < 1 ∧ ρ.im ≠ 0 ∧ ρ.re ≠ 1 / 2 ∧
    0 < T ∧ ∀ k : ℤ, f (ρ + (k * T) * Complex.I) = 0

/-- **Abstract periodic-mobility law.**  If every member of a mobile carrier class satisfies the
periodicity dichotomy, real-zero-free nonreal mobility necessarily upgrades to a full off-line
vertical zero progression. -/
theorem realZeroFreeNonrealStripMobility_promotes_to_periodic
    (C : (ℂ → ℂ) → Prop)
    (hmobility : RealZeroFreeNonrealStripMobility C)
    (hdichotomy : ∀ f : ℂ → ℂ, C f → PeriodicityDichotomy f) :
    RealZeroFreeNonrealPeriodicStripMobility C := by
  rcases hmobility with
    ⟨f, ρ, hf, hrealFree, hρ0, hρ1, hρnonreal, hzero, hρoffLine⟩
  rcases hdichotomy f hf ρ hρ0 hρ1 hzero with hline | ⟨T, hT, hperiodic⟩
  · exact (hρoffLine hline).elim
  · exact ⟨f, ρ, T, hf, hrealFree, hρ0, hρ1, hρnonreal,
      hρoffLine, hT, hperiodic⟩

/-- **Gamma-cell periodic nonreal mobility universality law.**  A cell-wide periodicity dichotomy
does not collapse gamma-cell mobility onto the critical line.  It forces existence of an all-prime
cell member that is zero-free on the real strip and carries a full nonreal off-line vertical
progression of zeros. -/
theorem gammaFECell_periodic_nonreal_mobility_of_dichotomy
    (hdichotomy : ∀ f : ℂ → ℂ, GammaFECell f → PeriodicityDichotomy f) :
    RealZeroFreeNonrealPeriodicStripMobility GammaFECell := by
  exact realZeroFreeNonrealStripMobility_promotes_to_periodic
    GammaFECell gammaFECell_real_zero_free_nonreal_strip_mobility hdichotomy

end

end RHTower
