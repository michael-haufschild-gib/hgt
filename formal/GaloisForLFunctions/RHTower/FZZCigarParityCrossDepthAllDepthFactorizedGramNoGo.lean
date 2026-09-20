import GaloisForLFunctions.RHTower.FZZCigarParityCrossDepthFactorizedGramNoGo

/-!
# FZZ-P all-depth real factorized cross-depth Gram no-go

The literal neutral-screening tower is not made oriented merely by replacing a finite real
factorized depth accumulation with its all-depth nested counterpart.  This file gives the exact
classification: the iterated `tsum` is a single Hermitian Gram square, hence real and
nonnegative.

This kills the FZZ-P subroute

`literal all-depth cross-depth covariance → real factorized nested depth integration → oriented
Ward term`.

For a physical application the indicated nested series must of course be the source-derived,
well-defined all-depth tower.  No Fubini interchange or assertion about a differently ordered
double series is used here.  The sharp survivor is source-derived order sensitivity,
nonfactorization, or a genuinely complex counterterm coupling.
-/

open Complex
open scoped BigOperators ComplexConjugate

namespace GaloisForLFunctions.RHTower

noncomputable section

/-- Nested all-depth real-factorized accumulation of the literal neutral radial covariance. -/
def fzzRadialCouplingAllDepthFactorizedGram
    (u : ℕ → ℝ) (w : ℕ → ℝ) (v p : ℝ) : ℂ :=
  ∑' i : ℕ, ∑' j : ℕ,
    (w i : ℂ) * (w j : ℂ) *
      fzzRadialCouplingCrossDepthCoherence (u i) (u j) v p

/-- Exact Gram-square classification of every nested all-depth real-factorized accumulation. -/
theorem fzzRadialCouplingAllDepthFactorizedGram_eq_normSq
    (u : ℕ → ℝ) (w : ℕ → ℝ) (v p : ℝ) :
    fzzRadialCouplingAllDepthFactorizedGram u w v p =
      ((Complex.normSq (∑' n : ℕ,
        (w n : ℂ) * fzzRadialCouplingCharacteristic (u n) v p) : ℝ) : ℂ) := by
  unfold fzzRadialCouplingAllDepthFactorizedGram
  rw [← Complex.mul_conj]
  change (∑' i : ℕ, ∑' j : ℕ,
      (w i : ℂ) * (w j : ℂ) *
        fzzRadialCouplingCrossDepthCoherence (u i) (u j) v p) =
    (∑' n : ℕ, (w n : ℂ) * fzzRadialCouplingCharacteristic (u n) v p) *
      star (∑' n : ℕ, (w n : ℂ) * fzzRadialCouplingCharacteristic (u n) v p)
  rw [tsum_star, ← tsum_mul_right, Complex.star_def]
  apply tsum_congr
  intro i
  rw [← tsum_mul_left]
  apply tsum_congr
  intro j
  rw [fzzRadialCouplingCrossDepthCoherence]
  rw [map_mul, Complex.conj_ofReal]
  ring

/-- No nested all-depth real-factorized depth accumulation retains imaginary orientation. -/
theorem fzzRadialCouplingAllDepthFactorizedGram_im
    (u : ℕ → ℝ) (w : ℕ → ℝ) (v p : ℝ) :
    (fzzRadialCouplingAllDepthFactorizedGram u w v p).im = 0 := by
  rw [fzzRadialCouplingAllDepthFactorizedGram_eq_normSq]
  simp

/-- The remaining all-depth value is a nonnegative Gram energy, not an oriented Ward term. -/
theorem fzzRadialCouplingAllDepthFactorizedGram_re_nonneg
    (u : ℕ → ℝ) (w : ℕ → ℝ) (v p : ℝ) :
    0 ≤ (fzzRadialCouplingAllDepthFactorizedGram u w v p).re := by
  rw [fzzRadialCouplingAllDepthFactorizedGram_eq_normSq]
  exact Complex.normSq_nonneg _

/-- **FZZ-P route-class no-go.** No nested all-depth real factorized depth measure can yield a
nonzero imaginary contribution from the literal cross-depth covariance. -/
theorem not_exists_fzzRadialCouplingAllDepthFactorizedGram_im_ne_zero :
    ¬ ∃ (u : ℕ → ℝ) (w : ℕ → ℝ) (v p : ℝ),
      (fzzRadialCouplingAllDepthFactorizedGram u w v p).im ≠ 0 := by
  rintro ⟨u, w, v, p, h⟩
  exact h (fzzRadialCouplingAllDepthFactorizedGram_im u w v p)

end

end GaloisForLFunctions.RHTower
