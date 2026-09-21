import GaloisForLFunctions.RHTower.FZZCigarHigherScreeningGammaContinuation
import GaloisForLFunctions.RHTower.FZZCigarParityCrossDepthOrderedSourceLaw

/-!
# FZZ-P higher-screening source orientation no-go

The fully restored higher two-puncture screening source is a real, reflection
symmetric function of its two continuation parameters.  This leaf feeds that
literal source into the finite ordered cross-depth source law.  It proves that
the cleared higher-screening source has no anti-Hermitian current whatsoever:
on an exchange-stable depth domain it cannot produce FZZ-P orientation.  On
an ordered domain its entire orientation is exactly the exchange-order defect.

Proof-chain role:
`literal cleared higher screening source -> ordered source current ->
replica--momentum Ward orientation -> FZZ-P`.

Thus the subroute
`cleared higher-screening source + exchange-stable depth integration ->
oriented Ward term`
is closed negatively.  The positive survivor is precise: a physical ordered
domain, or one of the separately open phase-frame/full-Ward inputs, must supply
the current.
-/

open Complex
open scoped BigOperators ComplexConjugate

namespace GaloisForLFunctions.RHTower

noncomputable section

/-- The complete restored higher screening source, sampled at two depth
parameters and viewed as a complex source kernel. -/
def fzzScreeningHigherClearedDepthKernel
    (parameter : ℝ → ℝ) (u₁ u₂ : ℝ) : ℂ :=
  (fzzScreeningHigherClearedSource (parameter u₁) (parameter u₂) : ℂ)

/-- The literal cleared higher-screening source is Hermitian as a depth
kernel.  Its putative anti-Hermitian source current is identically zero. -/
theorem fzzScreeningHigherClearedDepthKernel_depthHermitian
    (parameter : ℝ → ℝ) (u₁ u₂ : ℝ) :
    fzzScreeningHigherClearedDepthKernel parameter u₁ u₂ =
      star (fzzScreeningHigherClearedDepthKernel parameter u₂ u₁) := by
  unfold fzzScreeningHigherClearedDepthKernel
  rw [fzzScreeningHigherClearedSource_symm]
  simp

/-- No finite exchange-stable integration of the complete restored
higher-screening source has FZZ-P orientation. -/
theorem fzzRadialCouplingFiniteOrderedHigherClearedScreening_im_eq_zero
    (T : Finset (ℝ × ℝ)) (parameter : ℝ → ℝ) (v p : ℝ)
    (hT : fzzRadialCouplingDepthExchange T = T) :
    (fzzRadialCouplingFiniteOrderedKernel T
      (fzzScreeningHigherClearedDepthKernel parameter) v p).im = 0 := by
  apply fzzRadialCouplingFiniteOrderedKernel_im_eq_zero_of_exchangeHermitian T
    (fzzScreeningHigherClearedDepthKernel parameter) v p hT
  exact fzzScreeningHigherClearedDepthKernel_depthHermitian parameter

/-- Exact survivor: for the literal cleared higher-screening source, the
ordered-domain defect is the only possible finite orientation current. -/
theorem fzzRadialCouplingFiniteOrderedHigherClearedScreening_sub_star
    (T : Finset (ℝ × ℝ)) (parameter : ℝ → ℝ) (v p : ℝ) :
    fzzRadialCouplingFiniteOrderedKernel T
        (fzzScreeningHigherClearedDepthKernel parameter) v p -
      star (fzzRadialCouplingFiniteOrderedKernel T
        (fzzScreeningHigherClearedDepthKernel parameter) v p) =
      fzzRadialCouplingDepthOrderDefect T (fun u₁ u₂ =>
        star (fzzScreeningHigherClearedDepthKernel parameter u₂ u₁) *
          fzzRadialCouplingCrossDepthCoherence u₁ u₂ v p) := by
  rw [fzzRadialCouplingFiniteOrderedKernel_sub_star]
  have hanti : (∑ uv ∈ T,
      fzzRadialCouplingDepthAntiHermitian
          (fzzScreeningHigherClearedDepthKernel parameter) uv.1 uv.2 *
        fzzRadialCouplingCrossDepthCoherence uv.1 uv.2 v p) = 0 := by
    apply Finset.sum_eq_zero
    intro uv huv
    unfold fzzRadialCouplingDepthAntiHermitian
    rw [fzzScreeningHigherClearedDepthKernel_depthHermitian]
    ring
  rw [hanti, zero_add]

/-- **Higher-screening FZZ-P route kill.**  No finite exchange-stable depth
domain can turn the complete restored cleared screening source into a nonzero
oriented replica--momentum Ward contribution. -/
theorem not_exists_fzzRadialCouplingFiniteOrderedHigherClearedScreening_im_ne_zero :
    ¬ ∃ (T : Finset (ℝ × ℝ)) (parameter : ℝ → ℝ) (v p : ℝ),
      fzzRadialCouplingDepthExchange T = T ∧
        (fzzRadialCouplingFiniteOrderedKernel T
          (fzzScreeningHigherClearedDepthKernel parameter) v p).im ≠ 0 := by
  rintro ⟨T, parameter, v, p, hT, hnonzero⟩
  exact hnonzero
    (fzzRadialCouplingFiniteOrderedHigherClearedScreening_im_eq_zero T parameter v p hT)

end

end GaloisForLFunctions.RHTower
