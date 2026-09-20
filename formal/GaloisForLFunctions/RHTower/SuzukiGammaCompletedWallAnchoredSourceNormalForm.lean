import GaloisForLFunctions.RHTower.SuzukiGammaCompletedWallMixedCauchyKernel

/-!
# Single-source normal form of the literal completed Suzuki wall

The completed Ward wall is not an atomic prime wall plus an independently
estimated continuum.  Exact dilation puts both on the same anchored Cauchy
atoms.  This file records that source-faithful identity before any scalar
readout or positivity estimate.
-/

open Complex MeasureTheory Set
open scoped BigOperators Interval

namespace GaloisForLFunctions.RHTower

noncomputable section

/-- At every natural aperture and real Cauchy height, the literal completed
prime--polar--Gamma Ward wall is one signed measure on anchored wall atoms.
The finite atomic term retains every von Mangoldt coefficient; the two
continuous terms are the forced dilation transport of the actual regular
screw density. -/
theorem suzukiUnitRieszGammaCompletedWardWall_ofReal_eq_anchored_source
    (N : ℕ) (t : ℝ) :
    suzukiUnitRieszGammaCompletedWardWall (N + 2) (t : ℂ) =
      (∑ k ∈ Finset.Icc 2 (N + 2),
        (ArithmeticFunction.vonMangoldt k / Real.sqrt ((N + 2 : ℕ) : ℝ) : ℂ) *
          suzukiCauchyAnchoredWallAtom
            (Real.log ((N + 2 : ℕ) : ℝ) - Real.log k) t) -
        ((((2 : ℝ)⁻¹) •
          (∫ r in 0..(Real.log ((N + 2 : ℕ) : ℝ) -
            _root_.RHTower.unitRieszSuzukiBase) * 2,
            suzukiCauchyAnchoredWallAtom r t *
              (screwRegularKernel
                (Real.log ((N + 2 : ℕ) : ℝ) - r / 2) : ℂ))) -
          ∫ r in 0..Real.log ((N + 2 : ℕ) : ℝ) -
            _root_.RHTower.unitRieszSuzukiBase,
            suzukiCauchyAnchoredWallAtom r t *
              (screwRegularKernel
                (Real.log ((N + 2 : ℕ) : ℝ) - r) : ℂ)) := by
  have hbase : _root_.RHTower.unitRieszSuzukiBase ≤
      Real.log ((N + 2 : ℕ) : ℝ) :=
    (_root_.RHTower.unitRieszSuzukiBase_lt_log_of_two_le
      (by omega : 2 ≤ N + 2)).le
  rw [suzukiUnitRieszGammaCompletedWardWall_eq_prime_sub_regular,
    suzukiUnitRieszPrimeWardWall_ofReal_eq_sum_anchored,
    suzukiUnitRieszRegularWardWall_ofReal_eq_anchored_dilation hbase]

end

end GaloisForLFunctions.RHTower
