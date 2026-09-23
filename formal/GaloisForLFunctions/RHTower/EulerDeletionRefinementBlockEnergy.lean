import GaloisForLFunctions.RHTower.EulerDeletionRefinementBlockDifference
import GaloisForLFunctions.RHTower.EulerDeletionPrimePowerCanonicalResolventEnergy

noncomputable section

open Finset

namespace RHTower.DeletionResidueMartingale

/-- Exact refinement-block form of one upper-minus-lower canonical quotient,
at the actual upper residue represented by its lower residue and refinement
index. -/
theorem canonicalBetaResolvent_succ_sub_lower_eq_refinementBlockKernel_difference_mod_div
    (l N r : ℕ) (hlN : l < N) :
    canonicalBetaResolvent N (l + 1) r - canonicalBetaResolvent N l (r % clock l) =
      (∫ x in (0 : ℝ)..1,
        canonicalRefinementBlockKernel N l (r % clock l) (r / clock l) x) /
          cellMeasure.real (historyFibre (l + 1) ((r % clock l) + (r / clock l) * clock l)) -
        (∫ x in (0 : ℝ)..1,
          canonicalRefinementAggregateKernel N l (r % clock l) x) /
          cellMeasure.real (historyFibre l (r % clock l)) := by
  have hdecomp : r = r % clock l + (r / clock l) * clock l := by
    calc
      r = r % clock l + clock l * (r / clock l) := (Nat.mod_add_div r (clock l)).symm
      _ = _ := by rw [Nat.mul_comm]
  nth_rewrite 1 [hdecomp]
  exact canonicalBetaResolvent_succ_sub_lower_eq_refinementBlockKernel_difference l N
    (r % clock l) (r / clock l) hlN

/-- Exact EDQ energy at one surviving chronological step, written only with
the selected literal block, the complete literal aggregate, and the single
local innovation.  The signed Möbius source remains unsplit in both kernels. -/
theorem historyLayer_predictableDrift_norm_sq_eq_refinementBlockKernel_energy
    (l N : ℕ) (hlN : l < N) :
    ‖historyLayer l (predictableDrift N)‖ ^ (2 : ℕ) =
      ∑ r ∈ range (clock (l + 1)),
        cellMeasure.real (historyFibre (l + 1) r) *
          ((∫ x in (0 : ℝ)..1,
            canonicalRefinementBlockKernel N l (r % clock l) (r / clock l) x) /
              cellMeasure.real
                (historyFibre (l + 1) ((r % clock l) + (r / clock l) * clock l)) -
            (∫ x in (0 : ℝ)..1,
              canonicalRefinementAggregateKernel N l (r % clock l) x) /
                cellMeasure.real (historyFibre l (r % clock l)) -
            signedInnovation l r) ^ (2 : ℕ) := by
  rw [historyLayer_predictableDrift_norm_sq_eq_canonicalBetaResolvent_fibre_energy l N hlN]
  apply Finset.sum_congr rfl
  intro r hr
  rw [canonicalBetaResolvent_succ_sub_lower_eq_refinementBlockKernel_difference_mod_div l N r
    hlN]

/-- Full EDQ energy in its literal refinement-block form.  Only genuine
prime-power clock refinements remain; every surviving square contains its
selected signed block, the complete signed aggregate, and its one innovation. -/
theorem predictableDrift_norm_sq_eq_primePower_refinementBlockKernel_energy (N : ℕ) :
    ‖predictableDrift N‖ ^ (2 : ℕ) =
      ‖(historySpace 0).starProjection (predictableDrift N)‖ ^ (2 : ℕ) +
        ∑ l ∈ (range N).filter (fun l => IsPrimePow (l + 1)),
          ∑ r ∈ range (clock (l + 1)),
            cellMeasure.real (historyFibre (l + 1) r) *
              ((∫ x in (0 : ℝ)..1,
                canonicalRefinementBlockKernel N l (r % clock l) (r / clock l) x) /
                  cellMeasure.real
                    (historyFibre (l + 1) ((r % clock l) + (r / clock l) * clock l)) -
                (∫ x in (0 : ℝ)..1,
                  canonicalRefinementAggregateKernel N l (r % clock l) x) /
                    cellMeasure.real (historyFibre l (r % clock l)) -
                signedInnovation l r) ^ (2 : ℕ) := by
  rw [predictableDrift_norm_sq_eq_historyLayer_sum,
    predictableDrift_historyLayer_energy_eq_primePower_filter]
  congr 1
  apply Finset.sum_congr rfl
  intro l hl
  exact historyLayer_predictableDrift_norm_sq_eq_refinementBlockKernel_energy l N
    (Finset.mem_range.mp (Finset.mem_of_mem_filter l hl))

end RHTower.DeletionResidueMartingale
