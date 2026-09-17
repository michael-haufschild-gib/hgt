import GaloisForLFunctions.RHTower.EulerDeletionSelectedRefinementBlock

noncomputable section

open Finset

namespace RHTower.DeletionResidueMartingale

/-- The literal terminal-clock beta kernel of one successor-refinement block. -/
def canonicalRefinementBlockKernel (N l u b : ℕ) (x : ℝ) : ℝ :=
  (1 - x) * x ^ u *
    ∑ a : Fin (canonicalClockRatio N (l + 1)),
      (x ^ ((b + (clock (l + 1) / clock l) * a) * clock l) *
        pairedMoebiusSource N
          (u + (b + (clock (l + 1) / clock l) * a) * clock l)) *
        (1 - x ^ (canonicalClockRatio N (l + 1) * clock (l + 1)))⁻¹

/-- A child quotient is the integral of its one literal refinement block. -/
theorem canonicalBetaResolvent_succ_eq_refinementBlockKernel
    (l N u b : ℕ) :
    canonicalBetaResolvent N (l + 1) (u + b * clock l) =
      (∫ x in (0 : ℝ)..1, canonicalRefinementBlockKernel N l u b x) /
        cellMeasure.real (historyFibre (l + 1) (u + b * clock l)) := by
  simpa only [canonicalRefinementBlockKernel] using
    canonicalBetaResolvent_succ_eq_selected_refinement_block l N u b

/-- The unsplit signed aggregate of every successor-refinement block in one lower fibre. -/
def canonicalRefinementAggregateKernel (N l r : ℕ) (x : ℝ) : ℝ :=
  (1 - x) * x ^ r *
    ∑ a : Fin (canonicalClockRatio N (l + 1)), ∑ b : Fin (clock (l + 1) / clock l),
      (x ^ ((b + (clock (l + 1) / clock l) * a) * clock l) *
        pairedMoebiusSource N
          (r + (b + (clock (l + 1) / clock l) * a) * clock l)) *
        (1 - x ^ (canonicalClockRatio N (l + 1) * clock (l + 1)))⁻¹

/-- A parent quotient is the integral of the full unsplit signed refinement aggregate. -/
theorem canonicalBetaResolvent_lower_eq_refinementAggregateKernel
    (l N r : ℕ) (hlN : l < N) :
    canonicalBetaResolvent N l r =
      (∫ x in (0 : ℝ)..1, canonicalRefinementAggregateKernel N l r x) /
        cellMeasure.real (historyFibre l r) := by
  simpa only [canonicalRefinementAggregateKernel] using
    canonicalBetaResolvent_lower_eq_refinement_blocks l N r hlN

/-- The exact signed quantity in one successor-minus-parent resolvent coordinate:
one literal refinement block, with the child physical mass, less the complete
literal refinement aggregate, with the parent physical mass. -/
theorem canonicalBetaResolvent_succ_sub_lower_eq_refinementBlockKernel_difference
    (l N u b : ℕ) (hlN : l < N) :
    canonicalBetaResolvent N (l + 1) (u + b * clock l) -
      canonicalBetaResolvent N l u =
      (∫ x in (0 : ℝ)..1, canonicalRefinementBlockKernel N l u b x) /
          cellMeasure.real (historyFibre (l + 1) (u + b * clock l)) -
        (∫ x in (0 : ℝ)..1, canonicalRefinementAggregateKernel N l u x) /
          cellMeasure.real (historyFibre l u) := by
  rw [canonicalBetaResolvent_succ_eq_refinementBlockKernel,
    canonicalBetaResolvent_lower_eq_refinementAggregateKernel l N u hlN]

end RHTower.DeletionResidueMartingale
