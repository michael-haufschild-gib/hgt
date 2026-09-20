import GaloisForLFunctions.RHTower.FZZCigarNeutralRadialCrossDepthCoherence

/-!
# FZZ-P finite real factorized cross-depth Gram no-go

The literal neutral radial covariance is genuinely complex at a selected ordered pair of coupling
depths.  That fact alone does not survive a physical depth accumulation.  This file classifies the
entire finite, real, factorized class exactly: it is a Hermitian Gram square, hence real and
nonnegative.

This kills the FZZ-P subroute

`literal cross-depth covariance → finite real factorized depth integration → oriented Ward term`.

The positive survivor is sharp: a physical integrated mixed replica--momentum Ward identity must
retain source-derived order sensitivity, nonfactorization, or a genuinely complex counterterm
coupling.  A complex pointwise covariance and an arbitrary real depth measure cannot provide the
missing orientation.
-/

open Complex
open scoped BigOperators ComplexConjugate

namespace GaloisForLFunctions.RHTower

noncomputable section

/-- Finite real-factorized accumulation of the literal neutral radial cross-depth covariance. -/
def fzzRadialCouplingFiniteFactorizedGram
    (S : Finset ℝ) (w : ℝ → ℝ) (v p : ℝ) : ℂ :=
  ∑ u₁ ∈ S, ∑ u₂ ∈ S,
    (w u₁ : ℂ) * (w u₂ : ℂ) *
      fzzRadialCouplingCrossDepthCoherence u₁ u₂ v p

/-- Exact Gram-square classification of every finite real-factorized cross-depth accumulation. -/
theorem fzzRadialCouplingFiniteFactorizedGram_eq_normSq
    (S : Finset ℝ) (w : ℝ → ℝ) (v p : ℝ) :
    fzzRadialCouplingFiniteFactorizedGram S w v p =
      ((Complex.normSq (∑ u ∈ S,
        (w u : ℂ) * fzzRadialCouplingCharacteristic u v p) : ℝ) : ℂ) := by
  unfold fzzRadialCouplingFiniteFactorizedGram
  rw [← Complex.mul_conj]
  rw [map_sum]
  simp only [map_mul, Complex.conj_ofReal]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro u₁ hu₁
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u₂ hu₂
  rw [fzzRadialCouplingCrossDepthCoherence]
  ring

/-- No finite real-factorized depth accumulation retains the required imaginary orientation. -/
theorem fzzRadialCouplingFiniteFactorizedGram_im
    (S : Finset ℝ) (w : ℝ → ℝ) (v p : ℝ) :
    (fzzRadialCouplingFiniteFactorizedGram S w v p).im = 0 := by
  rw [fzzRadialCouplingFiniteFactorizedGram_eq_normSq]
  simp

/-- The remaining real value is a nonnegative Gram energy, not an oriented Ward contribution. -/
theorem fzzRadialCouplingFiniteFactorizedGram_re_nonneg
    (S : Finset ℝ) (w : ℝ → ℝ) (v p : ℝ) :
    0 ≤ (fzzRadialCouplingFiniteFactorizedGram S w v p).re := by
  rw [fzzRadialCouplingFiniteFactorizedGram_eq_normSq]
  exact Complex.normSq_nonneg _

/-- **FZZ-P route-class no-go.** No finite real factorized depth measure can yield a nonzero
imaginary contribution from the literal cross-depth covariance. -/
theorem not_exists_fzzRadialCouplingFiniteFactorizedGram_im_ne_zero :
    ¬ ∃ (S : Finset ℝ) (w : ℝ → ℝ) (v p : ℝ),
      (fzzRadialCouplingFiniteFactorizedGram S w v p).im ≠ 0 := by
  rintro ⟨S, w, v, p, h⟩
  exact h (fzzRadialCouplingFiniteFactorizedGram_im S w v p)

end

end GaloisForLFunctions.RHTower
