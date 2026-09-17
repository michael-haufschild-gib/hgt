import GaloisForLFunctions.RHTower.EulerDeletionCanonicalRefinementBlocks

noncomputable section

open Finset

namespace RHTower.DeletionResidueMartingale

/-- A finer-clock canonical resolvent is exactly its selected literal block inside
the lower-clock refinement.  The physical fibre denominator remains the one
belonging to that finer residue. -/
theorem canonicalBetaResolvent_succ_eq_selected_refinement_block
    (l N u b : ℕ) :
    canonicalBetaResolvent N (l + 1) (u + b * clock l) =
      (∫ x in (0 : ℝ)..1, (1 - x) * x ^ u *
        ∑ a : Fin (canonicalClockRatio N (l + 1)),
          (x ^ ((b + (clock (l + 1) / clock l) * a) * clock l) *
            pairedMoebiusSource N
              (u + (b + (clock (l + 1) / clock l) * a) * clock l)) *
            (1 - x ^ (canonicalClockRatio N (l + 1) * clock (l + 1)))⁻¹) /
        cellMeasure.real (historyFibre (l + 1) (u + b * clock l)) := by
  unfold canonicalBetaResolvent
  have hclock : (clock (l + 1) / clock l) * clock l = clock (l + 1) :=
    Nat.div_mul_cancel (clock_dvd (Nat.le_succ l))
  apply congrArg (fun y : ℝ => y /
    cellMeasure.real (historyFibre (l + 1) (u + b * clock l)))
  apply intervalIntegral.integral_congr
  intro x hx
  change (1 - x) * x ^ (u + b * clock l) *
      ∑ s ∈ range (canonicalClockRatio N (l + 1)),
        (x ^ (s * clock (l + 1)) *
          pairedMoebiusSource N (u + b * clock l + s * clock (l + 1))) *
          (1 - x ^ (canonicalClockRatio N (l + 1) * clock (l + 1)))⁻¹ = _
  rw [← Fin.sum_univ_eq_sum_range]
  calc
    (1 - x) * x ^ (u + b * clock l) *
        ∑ a : Fin (canonicalClockRatio N (l + 1)),
          (x ^ (a * clock (l + 1)) *
            pairedMoebiusSource N (u + b * clock l + a * clock (l + 1))) *
            (1 - x ^ (canonicalClockRatio N (l + 1) * clock (l + 1)))⁻¹ =
        (1 - x) * x ^ u *
          ∑ a : Fin (canonicalClockRatio N (l + 1)),
            (x ^ (b * clock l) *
              (x ^ (a * clock (l + 1)) *
                pairedMoebiusSource N (u + b * clock l + a * clock (l + 1)))) *
              (1 - x ^ (canonicalClockRatio N (l + 1) * clock (l + 1)))⁻¹ := by
        rw [pow_add]
        calc
          (1 - x) * (x ^ u * x ^ (b * clock l)) *
              ∑ a : Fin (canonicalClockRatio N (l + 1)),
                (x ^ (a * clock (l + 1)) *
                  pairedMoebiusSource N (u + b * clock l + a * clock (l + 1))) *
                  (1 - x ^ (canonicalClockRatio N (l + 1) * clock (l + 1)))⁻¹ =
              ((1 - x) * x ^ u) *
                (x ^ (b * clock l) *
                  ∑ a : Fin (canonicalClockRatio N (l + 1)),
                    (x ^ (a * clock (l + 1)) *
                      pairedMoebiusSource N (u + b * clock l + a * clock (l + 1))) *
                      (1 - x ^ (canonicalClockRatio N (l + 1) * clock (l + 1)))⁻¹) := by ring
          _ = _ := by
            rw [Finset.mul_sum]
            congr 1
            apply Finset.sum_congr rfl
            intro a ha
            ring
    _ = _ := by
      congr 1
      apply Finset.sum_congr rfl
      intro a ha
      have hpow : b * clock l + a * clock (l + 1) =
          (b + (clock (l + 1) / clock l) * a) * clock l := by
        calc
          b * clock l + a * clock (l + 1) =
              b * clock l + a * ((clock (l + 1) / clock l) * clock l) := by
                rw [hclock]
          _ = _ := by ring
      have harg : u + b * clock l + a * clock (l + 1) =
          u + (b + (clock (l + 1) / clock l) * a) * clock l := by
        calc
          u + b * clock l + a * clock (l + 1) =
              u + b * clock l + a * ((clock (l + 1) / clock l) * clock l) := by
                rw [hclock]
          _ = _ := by ring
      calc
        x ^ (b * clock l) *
            (x ^ (a * clock (l + 1)) *
              pairedMoebiusSource N (u + b * clock l + a * clock (l + 1))) *
            (1 - x ^ (canonicalClockRatio N (l + 1) * clock (l + 1)))⁻¹ =
            (x ^ (b * clock l) * x ^ (a * clock (l + 1))) *
              pairedMoebiusSource N (u + b * clock l + a * clock (l + 1)) *
              (1 - x ^ (canonicalClockRatio N (l + 1) * clock (l + 1)))⁻¹ := by ring
        _ = _ := by rw [← pow_add, hpow, harg]

end RHTower.DeletionResidueMartingale
