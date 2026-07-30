import GaloisForLFunctions.RHTower.XiThetaReaderConditioning

/-!
# From the completed logarithmic source back to shifted heat coordinates

The completed critical trace is Fourier in the logarithmic coordinate, but inverse Fourier recovers
the positive logarithmic source. Removing its critical weight and applying y = exp(u) - 1 converts
each physical square atom into an ordinary heat exponential on y > 0.

The resulting atom carries the scalar exp(-pi m squared). Multiplication by exp(pi m squared)
removes exactly this boundary shift and recovers the unshifted heat atom consumed by Laplace and
Hardy-space readers. Thus the superexponential reader cost is the exact x = 1 boundary
normalization, not evidence that a fixed-index composite reader is impossible.
-/

open Complex Real MeasureTheory Set Filter Topology HurwitzZeta
open scoped ENNReal Topology FourierTransform

noncomputable section

namespace RHTower

/-- Remove the critical logarithmic weight and shift the heat coordinate from x > 1 to y > 0. -/
def thetaLogToShiftedHeat (f : ℝ → ℝ) (y : ℝ) : ℝ :=
  (1 / 2 : ℝ) * Real.exp (-Real.log (1 + y) / 4) *
    f (Real.log (1 + y))

def thetaUnshiftedHeatAtom (m : ℕ) (y : ℝ) : ℝ :=
  Real.exp (-π * (m : ℝ) ^ 2 * y)

def thetaBoundaryShiftedHeatAtom (m : ℕ) (y : ℝ) : ℝ :=
  Real.exp (-π * (m : ℝ) ^ 2) * thetaUnshiftedHeatAtom m y

/-- Exact atom-level composite bridge from logarithmic theta coordinates to heat coordinates. -/
theorem thetaLogToShiftedHeat_squareAtom {m : ℕ} {y : ℝ} (hy : 0 ≤ y) :
    thetaLogToShiftedHeat (thetaSquareLogAtom m) y =
      thetaBoundaryShiftedHeatAtom m y := by
  have hy1 : 0 < 1 + y := by linarith
  rw [thetaLogToShiftedHeat, thetaSquareLogAtom, thetaBoundaryShiftedHeatAtom,
    thetaUnshiftedHeatAtom, Real.exp_log hy1]
  have hcancel : Real.exp (-Real.log (1 + y) / 4) *
      Real.exp (Real.log (1 + y) / 4) = 1 := by
    rw [← Real.exp_add]
    convert Real.exp_zero using 1
    ring_nf
  rw [show (1 / 2 : ℝ) *
      Real.exp (-Real.log (1 + y) / 4) *
      (2 * Real.exp (Real.log (1 + y) / 4) *
        Real.exp (-π * (m : ℝ) ^ 2 * (1 + y))) =
      Real.exp (-π * (m : ℝ) ^ 2 * (1 + y)) by
    calc
      (1 / 2 : ℝ) * Real.exp (-Real.log (1 + y) / 4) *
          (2 * Real.exp (Real.log (1 + y) / 4) *
            Real.exp (-π * (m : ℝ) ^ 2 * (1 + y))) =
          (Real.exp (-Real.log (1 + y) / 4) *
            Real.exp (Real.log (1 + y) / 4)) *
            Real.exp (-π * (m : ℝ) ^ 2 * (1 + y)) := by ring
      _ = Real.exp (-π * (m : ℝ) ^ 2 * (1 + y)) := by rw [hcancel, one_mul]]
  rw [← Real.exp_add]
  congr 1
  ring

/-- Away from the single strict-truncation endpoint, the actual positive atom has the same heat
reparametrization. -/
theorem thetaLogToShiftedHeat_positiveSquareAtom {m : ℕ} {y : ℝ} (hy : 0 < y) :
    thetaLogToShiftedHeat
        (fun u => (thetaPositiveSquareLogAtom m u).re) y =
      thetaBoundaryShiftedHeatAtom m y := by
  have hy1 : 0 < 1 + y := by linarith
  have hlog : 0 < Real.log (1 + y) := Real.log_pos (by linarith)
  rw [thetaLogToShiftedHeat, thetaPositiveSquareLogAtom, positiveLogTruncation,
    indicator_of_mem (show Real.log (1 + y) ∈ Ioi (0 : ℝ) from hlog),
    ofReal_re]
  exact thetaLogToShiftedHeat_squareAtom hy.le

/-- The exp(pi m squared) condition number is exactly the boundary-shift normalization. -/
theorem thetaBoundaryShiftedHeatAtom_deboundary {m : ℕ} (y : ℝ) :
    Real.exp (π * (m : ℝ) ^ 2) * thetaBoundaryShiftedHeatAtom m y =
      thetaUnshiftedHeatAtom m y := by
  rw [thetaBoundaryShiftedHeatAtom]
  have hcancel : Real.exp (π * (m : ℝ) ^ 2) *
      Real.exp (-π * (m : ℝ) ^ 2) = 1 := by
    rw [← Real.exp_add]
    convert Real.exp_zero using 1
    ring_nf
  rw [← mul_assoc, hcancel, one_mul]

/-- The positive logarithmic coordinate change y = exp(u) - 1. -/
def expSubOne (u : ℝ) : ℝ := Real.exp u - 1

private theorem expSubOne_deriv :
    ∀ u ∈ Ioi (0 : ℝ),
      HasDerivWithinAt expSubOne (Real.exp u) (Ioi (0 : ℝ)) u := by
  intro u hu
  exact ((Real.hasDerivAt_exp u).sub_const 1).hasDerivWithinAt

private theorem expSubOne_injOn : (Ioi (0 : ℝ)).InjOn expSubOne := by
  intro x hx y hy hxy
  apply Real.exp_injective
  dsimp [expSubOne] at hxy
  linarith

private theorem expSubOne_image : expSubOne '' Ioi (0 : ℝ) = Ioi (0 : ℝ) := by
  ext y
  constructor
  · rintro ⟨u, hu, rfl⟩
    rw [mem_Ioi]
    have := Real.exp_lt_exp.mpr hu
    simpa only [Real.exp_zero] using! sub_pos.mpr this
  · intro hy
    have hy1 : 0 < 1 + y := by linarith [show 0 < y from hy]
    refine ⟨Real.log (1 + y), ?_, ?_⟩
    · rw [mem_Ioi, Real.log_pos_iff hy1.le]
      linarith [show 0 < y from hy]
    · rw [expSubOne, Real.exp_log hy1]
      ring

/-- Exact Jacobian-weighted L2 identity for the source-to-heat reparametrization. The heat map is
one half of an isometry from the source norm weighted by exp(u/2). -/
theorem integral_sq_thetaLogToShiftedHeat (f : ℝ → ℝ) :
    (∫ y in Ioi (0 : ℝ), (thetaLogToShiftedHeat f y) ^ 2) =
      (1 / 4 : ℝ) * ∫ u in Ioi (0 : ℝ), Real.exp (u / 2) * (f u) ^ 2 := by
  have hchange := integral_image_eq_integral_abs_deriv_smul
    measurableSet_Ioi expSubOne_deriv expSubOne_injOn
    (fun y : ℝ => (thetaLogToShiftedHeat f y) ^ 2)
  rw [expSubOne_image] at hchange
  rw [hchange, ← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro u hu
  have hu0 : 0 < u := hu
  simp only [abs_of_pos (Real.exp_pos u), smul_eq_mul]
  rw [thetaLogToShiftedHeat, expSubOne]
  rw [show 1 + (Real.exp u - 1) = Real.exp u by ring, Real.log_exp]
  have hexp : Real.exp u * Real.exp (-u / 4) ^ 2 =
      Real.exp (u / 2) := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    ring
  calc
    Real.exp u * ((1 / 2 : ℝ) * Real.exp (-u / 4) * f u) ^ 2 =
        (1 / 4 : ℝ) * (Real.exp u * Real.exp (-u / 4) ^ 2) * f u ^ 2 := by ring
    _ = (1 / 4 : ℝ) * (Real.exp (u / 2) * f u ^ 2) := by rw [hexp]; ring

end RHTower
