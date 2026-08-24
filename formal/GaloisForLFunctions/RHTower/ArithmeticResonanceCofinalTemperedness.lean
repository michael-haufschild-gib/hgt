import GaloisForLFunctions.RHTower.CompleteResolutionReflectedShellSecondCartierDescent
import GaloisForLFunctions.RHTower.PurityCurvatureExponentialTransgression
import GaloisForLFunctions.RHTower.RiemannComplexModularCharacterLaw

/-!
# Arithmetic resonance cofinal temperedness

The completed Euler--Gamma source supplies genuine consecutive forward and reflected shell
transfers before any divisor is selected.  For a nonzero polarized coefficient, one uniform
cofinal positive-energy budget for those finite transfers exists exactly when the scale character
is tempered.  This file identifies that condition, for an arbitrary point in the critical strip,
with both vanishing weight-one Hodge curvature and unitarity of the centered modular character.

Thus these are not three prospective selection mechanisms.  They are three languages for one
condition.  Any source theorem proposed to produce the budget is falsified at every point with
nonzero Hodge curvature.
-/

open Complex Filter Topology

namespace RHTower

noncomputable section

/-- Weight-one Hodge curvature vanishes exactly on the critical line, without a divisor or
zero hypothesis. -/
theorem weightOnePurityCurvature_eq_zero_iff_re_eq_half
    (s : ℂ) :
    weightOnePurityCurvature s = 0 ↔ s.re = 1 / 2 := by
  constructor
  · intro h
    have hre := congrArg Complex.re h
    simp [weightOnePurityCurvature] at hre
    linarith
  · intro h
    apply Complex.ext
    · simp [weightOnePurityCurvature]
      linarith
    · simp [weightOnePurityCurvature]

/-- **Pre-divisor cofinal temperedness.** Uniform positive energy along genuine consecutive
completed shell runs is equivalent to zero real scale weight. -/
theorem completeResolutionPrimePeeledCumulativeReflectedSecondCartierCofinalBudget_iff_re_eq_half
    (p : Nat.Primes) {s c : ℂ}
    (hs0 : 0 < s.re) (hs1 : s.re < 1) (hc : c ≠ 0) :
    CompleteResolutionPrimePeeledCumulativeReflectedSecondCartierCofinalBudget p s c ↔
      s.re = 1 / 2 := by
  have hlam : ((p.1 : ℂ) ^ ((1 / 2 : ℂ) - s)) ≠ 0 := by
    simpa [bilateralHalfDensityCharacter] using
      bilateralHalfDensityCharacter_ne_zero (p := p.1) (Nat.Prime.pos p.2) s
  rw [completeResolutionPrimePeeledCumulativeReflectedSecondCartierCofinalBudget_iff
      p hs0 hs1,
    sourceHorizontalSecondCartierKreinPolarizedGhostOrbitBounded_iff
      hlam hc]
  simpa [bilateralHalfDensityCharacter] using
    norm_bilateralHalfDensityCharacter_eq_one_iff
      (p := p.1) (Nat.Prime.two_le p.2) s

/-- Genuine completed-shell cofinal order is exactly flatness of the weight-one Hodge
connection.  No Xi-zero indexing occurs. -/
theorem completeResolutionPrimePeeledCumulativeReflectedSecondCartierCofinalBudget_iff_hodgeFlat
    (p : Nat.Primes) {s c : ℂ}
    (hs0 : 0 < s.re) (hs1 : s.re < 1) (hc : c ≠ 0) :
    CompleteResolutionPrimePeeledCumulativeReflectedSecondCartierCofinalBudget p s c ↔
      weightOnePurityCurvature s = 0 := by
  rw [completeResolutionPrimePeeledCumulativeReflectedSecondCartierCofinalBudget_iff_re_eq_half
      p hs0 hs1 hc,
    weightOnePurityCurvature_eq_zero_iff_re_eq_half]

/-- Genuine completed-shell cofinal order is exactly unitarity of the centered modular
character at the retained prime clock. -/
theorem completeResolutionPrimePeeledCumulativeReflectedSecondCartierCofinalBudget_iff_modularUnitary
    (p : Nat.Primes) {s c : ℂ}
    (hs0 : 0 < s.re) (hs1 : s.re < 1) (hc : c ≠ 0) :
    CompleteResolutionPrimePeeledCumulativeReflectedSecondCartierCofinalBudget p s c ↔
      ‖centeredComplexModularCharacter s (Real.log (p.1 : ℝ) : ℂ)‖ = 1 := by
  rw [completeResolutionPrimePeeledCumulativeReflectedSecondCartierCofinalBudget_iff_re_eq_half
      p hs0 hs1 hc]
  rw [norm_centeredComplexModularCharacter_ofReal]
  constructor
  · intro h
    rw [h]
    ring_nf
    exact Real.exp_zero
  · intro h
    rw [← Real.exp_zero, Real.exp_eq_exp] at h
    have hlog : Real.log (p.1 : ℝ) ≠ 0 :=
      ne_of_gt (Real.log_pos (by exact_mod_cast Nat.Prime.one_lt p.2))
    rcases mul_eq_zero.mp h with hp | hs
    · exact absurd hp hlog
    · norm_num [Real.exp_zero] at hs
      linarith

/-- Explicit falsifier: nonflat Hodge curvature forbids any uniform cofinal positive-energy
budget for genuine completed shell evolution. -/
theorem not_completeResolutionPrimePeeledCumulativeReflectedSecondCartierCofinalBudget_of_hodgeCurvature_ne_zero
    (p : Nat.Primes) {s c : ℂ}
    (hs0 : 0 < s.re) (hs1 : s.re < 1) (hc : c ≠ 0)
    (hcurv : weightOnePurityCurvature s ≠ 0) :
    ¬ CompleteResolutionPrimePeeledCumulativeReflectedSecondCartierCofinalBudget p s c := by
  intro hbudget
  exact hcurv
    ((completeResolutionPrimePeeledCumulativeReflectedSecondCartierCofinalBudget_iff_hodgeFlat
      p hs0 hs1 hc).mp hbudget)

end

end RHTower
