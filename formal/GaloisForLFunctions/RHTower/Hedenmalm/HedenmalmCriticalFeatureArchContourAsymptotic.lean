import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmCriticalFeatureLatticePoleGammaVMBudget

/-!
# Critical-feature archimedean contour reduction

The exact pole–Gamma–von-Mangoldt split has only one potentially leading source
channel on a sublinear lattice.  This module packages the pole–Gamma term minus
the source-only thin-strip contour and proves that the remaining von Mangoldt
channel is negligible after normalization by the zero count.

This is a reduction, not the missing `4 / 25` estimate: it identifies that
estimate with an archimedean contour cancellation problem up to `o(N)`.
-/

open Filter Topology

namespace RHTower

noncomputable section

/-- Pole–Gamma lattice budget after subtracting the source-only thin-strip
contour. -/
def criticalFeaturePoleGammaContourLatticeBudget
    (K : Finset ℤ) (A B delta : ℝ) : ℝ :=
  criticalFeaturePoleGammaLatticeBudget K -
    criticalFeatureThinStripLineContourLattice K A B delta

/-- Exact corrected-budget split into the von Mangoldt channel and the
archimedean contour channel. -/
theorem criticalFeatureThinStripPoleGammaVMLatticeBudget_eq_prime_add_archContour
    (K : Finset ℤ) (A B delta : ℝ) :
    criticalFeatureThinStripPoleGammaVMLatticeBudget K A B delta =
      criticalFeatureVonMangoldtLatticeBudget K +
        criticalFeaturePoleGammaContourLatticeBudget K A B delta := by
  rw [criticalFeatureThinStripPoleGammaVMLatticeBudget_eq_channels]
  unfold criticalFeaturePoleGammaContourLatticeBudget
  ring

/-- On any lattice whose cardinality is `o(N)`, normalized corrected budget and
normalized archimedean contour budget differ by a term tending to zero. -/
theorem tendsto_criticalFeatureThinStripPoleGammaVM_sub_archContour_div
    (K : ℕ → Finset ℤ) (N A B delta : ℕ → ℝ)
    (hN : ∀ᶠ n in atTop, 0 < N n)
    (hcard : Tendsto (fun n => ((K n).card : ℝ) / N n) atTop (nhds 0)) :
    Tendsto
      (fun n =>
        (criticalFeatureThinStripPoleGammaVMLatticeBudget
            (K n) (A n) (B n) (delta n) -
          criticalFeaturePoleGammaContourLatticeBudget
            (K n) (A n) (B n) (delta n)) / N n)
      atTop (nhds 0) := by
  have hprime :=
    tendsto_criticalFeatureVonMangoldtLatticeBudget_div_of_card_div
      K N hN hcard
  convert hprime using 1
  funext n
  rw [criticalFeatureThinStripPoleGammaVMLatticeBudget_eq_prime_add_archContour]
  ring

end

end RHTower
