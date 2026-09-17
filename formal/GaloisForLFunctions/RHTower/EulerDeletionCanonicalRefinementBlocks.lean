import GaloisForLFunctions.RHTower.EulerDeletionClockRefinement

noncomputable section

open Finset

namespace RHTower.DeletionResidueMartingale

/-- The lower clock's canonical beta resolvent, decomposed exactly into the
successive-clock residue blocks inside the common terminal clock.

This is a finite quotient--remainder reindexing of the literal paired
Möbius source.  No signs, terms, or beta fibres are discarded. -/
theorem canonicalBetaResolvent_lower_eq_refinement_blocks
    (l N r : ℕ) (hlN : l < N) :
    canonicalBetaResolvent N l r =
      (∫ x in (0 : ℝ)..1, (1 - x) * x ^ r *
        ∑ a : Fin (canonicalClockRatio N (l + 1)), ∑ b : Fin (clock (l + 1) / clock l),
          (x ^ ((b + (clock (l + 1) / clock l) * a) * clock l) *
            pairedMoebiusSource N
              (r + (b + (clock (l + 1) / clock l) * a) * clock l)) *
            (1 - x ^ (canonicalClockRatio N (l + 1) * clock (l + 1)))⁻¹) /
        cellMeasure.real (historyFibre l r) := by
  unfold canonicalBetaResolvent
  rw [canonicalClockRatio_eq_refinement_mul l N hlN]
  have hclock : (clock (l + 1) / clock l) * clock l = clock (l + 1) :=
    Nat.div_mul_cancel (clock_dvd (Nat.le_succ l))
  apply congrArg (fun y : ℝ => y / cellMeasure.real (historyFibre l r))
  apply intervalIntegral.integral_congr
  intro x hx
  change (1 - x) * x ^ r *
      ∑ s ∈ range (canonicalClockRatio N (l + 1) * (clock (l + 1) / clock l)),
        (x ^ (s * clock l) * pairedMoebiusSource N (r + s * clock l)) *
          (1 - x ^ ((canonicalClockRatio N (l + 1) *
            (clock (l + 1) / clock l)) * clock l))⁻¹ = _
  rw [Nat.mul_assoc, hclock]
  congr 1
  rw [← Fin.sum_univ_eq_sum_range]
  calc
    (∑ s : Fin (canonicalClockRatio N (l + 1) * (clock (l + 1) / clock l)),
        (x ^ (s * clock l) * pairedMoebiusSource N (r + s * clock l)) *
          (1 - x ^ (canonicalClockRatio N (l + 1) * clock (l + 1)))⁻¹) =
        ∑ qs : Fin (canonicalClockRatio N (l + 1)) × Fin (clock (l + 1) / clock l),
          (x ^ ((qs.2 + (clock (l + 1) / clock l) * qs.1) * clock l) *
            pairedMoebiusSource N
              (r + (qs.2 + (clock (l + 1) / clock l) * qs.1) * clock l)) *
            (1 - x ^ (canonicalClockRatio N (l + 1) * clock (l + 1)))⁻¹ :=
      by
        simpa using
          (sum_fin_block_decomposition (clock (l + 1) / clock l)
            (canonicalClockRatio N (l + 1))
            (fun s : ℕ =>
              (x ^ (s * clock l) * pairedMoebiusSource N (r + s * clock l)) *
                (1 - x ^ (canonicalClockRatio N (l + 1) * clock (l + 1)))⁻¹))
    _ = _ := by rw [Fintype.sum_prod_type]

end RHTower.DeletionResidueMartingale
