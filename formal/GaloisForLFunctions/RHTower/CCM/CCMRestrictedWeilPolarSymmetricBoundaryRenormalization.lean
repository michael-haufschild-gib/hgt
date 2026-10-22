import GaloisForLFunctions.RHTower.CCM.CCMRestrictedWeilPolarParitySourceProfile

/-!
# Exact symmetric boundary renormalization for the constrained Weil source

The pole source has a common two-endpoint Gamma logarithm which neither
reflection parity removes.  This file subtracts that *literal* symmetric
logarithm before scalar readout.  The resulting profile is exactly the
bounded boundary asymmetry plus the unchanged prime--polar arithmetic
remainder.  It is an interface theorem, not a bound for the valuation-one
prime--polar codiagonal.
-/

open Complex MeasureTheory Set Filter
open scoped InnerProduct Topology ENNReal
noncomputable section
namespace RHTower

/-- The reflection-symmetric pair of endpoint logarithms in the Gamma boundary. -/
def ccmGammaPolarBoundarySymmetricLog (R L : ℝ) : ℝ :=
  -(1 / 2) * Real.log (1 - Real.exp (-(2 * R))) -
    (1 / 2) * Real.log (1 - Real.exp (-(2 * L)))

/-- The exact common Gamma counterterm in a physical reflection channel. -/
def ccmPolarParityBoundaryLogCounterterm (a : SuzukiPositiveAperture) (r x : ℝ) : ℂ :=
  ((Real.exp (x / 2) + r * Real.exp (-x / 2)) *
    ccmGammaPolarBoundarySymmetricLog (a.1 - x) (a.1 + x) : ℝ)

/-- The physical parity profile after subtracting its literal symmetric Gamma counterterm. -/
def ccmPolarParityBoundaryRenormalizedProfile (a : SuzukiPositiveAperture) (r x : ℝ) : ℂ :=
  ccmPolarParityBoundaryProfile a r x - ccmPolarParityBoundaryLogCounterterm a r x

/-- The logarithmic counterterm is invariant under interchange of its two endpoint lengths. -/
theorem ccmGammaPolarBoundarySymmetricLog_swap (R L : ℝ) :
    ccmGammaPolarBoundarySymmetricLog R L = ccmGammaPolarBoundarySymmetricLog L R := by
  unfold ccmGammaPolarBoundarySymmetricLog
  ring

/-- Exact source-faithful renormalization identity: all surviving terms are literal. -/
theorem ccmPolarParityBoundaryRenormalizedProfile_re (a : SuzukiPositiveAperture) (r x : ℝ)
    (hx : x ∈ Ioo (-a.1) a.1) :
    (ccmPolarParityBoundaryRenormalizedProfile a r x).re =
      (Real.exp (x / 2) + r * Real.exp (-x / 2)) *
        Real.log (1 + Real.exp (-(a.1 + x))) -
          ccmPolarParityArithmeticRemainder a r x := by
  unfold ccmPolarParityBoundaryRenormalizedProfile ccmPolarParityBoundaryLogCounterterm
  simp only [Complex.sub_re, Complex.ofReal_re]
  rw [ccmPolarParityBoundaryProfile_re_decomposition]
  rw [ccmGammaPolarBoundary_symmetric_decomposition (by linarith [hx.1])]
  unfold ccmGammaPolarBoundarySymmetricLog
  ring

/-- The renormalized physical parity readout has an explicit finite-aperture bound. -/
theorem abs_ccmPolarParityBoundaryRenormalizedProfile_re_le
    (a : SuzukiPositiveAperture) {r : ℝ} (hr : r = 1 ∨ r = -1) {x : ℝ}
    (hx : x ∈ Ioo (-a.1) a.1) :
    |(ccmPolarParityBoundaryRenormalizedProfile a r x).re| ≤
      2 * Real.exp (a.1 / 2) * Real.log 2 +
        Real.exp (a.1 / 2) *
          (2 * (Chebyshev.psi (Real.exp (2 * a.1)) + Real.exp (2 * a.1) +
            (Real.log 4 + 5)) + Real.log 2) := by
  have hR : 0 < a.1 - x := by linarith [hx.2]
  have hL : 0 < a.1 + x := by linarith [hx.1]
  have hlogpos : 0 < Real.log (1 + Real.exp (-(a.1 + x))) := by
    apply Real.log_pos
    linarith [Real.exp_pos (-(a.1 + x))]
  have hloglt : Real.log (1 + Real.exp (-(a.1 + x))) < Real.log 2 := by
    apply Real.log_lt_log (by positivity)
    have he : Real.exp (-(a.1 + x)) < 1 :=
      Real.exp_lt_one_iff.mpr (by linarith)
    linarith
  have hE : Real.exp (x / 2) ≤ Real.exp (a.1 / 2) :=
    Real.exp_le_exp.mpr (by linarith [hx.2])
  have hF : Real.exp (-x / 2) ≤ Real.exp (a.1 / 2) :=
    Real.exp_le_exp.mpr (by linarith [hx.1])
  have hrabs : |r| = 1 := by rcases hr with rfl | rfl <;> norm_num
  have hcoef : |Real.exp (x / 2) + r * Real.exp (-x / 2)| ≤
      2 * Real.exp (a.1 / 2) := by
    calc
      _ ≤ |Real.exp (x / 2)| + |r * Real.exp (-x / 2)| := abs_add_le _ _
      _ = Real.exp (x / 2) + Real.exp (-x / 2) := by
        rw [abs_of_pos (Real.exp_pos _), abs_mul, hrabs,
          abs_of_pos (Real.exp_pos _), one_mul]
      _ ≤ Real.exp (a.1 / 2) + Real.exp (a.1 / 2) := add_le_add hE hF
      _ = _ := by ring
  have hterm : |(Real.exp (x / 2) + r * Real.exp (-x / 2)) *
      Real.log (1 + Real.exp (-(a.1 + x)))| ≤
      2 * Real.exp (a.1 / 2) * Real.log 2 := by
    rw [abs_mul, abs_of_pos hlogpos]
    exact mul_le_mul hcoef hloglt.le hlogpos.le (by positivity)
  have hrem := abs_ccmPolarParityArithmeticRemainder_le a hr hx
  rw [ccmPolarParityBoundaryRenormalizedProfile_re a r x hx]
  calc
    _ ≤ |(Real.exp (x / 2) + r * Real.exp (-x / 2)) *
        Real.log (1 + Real.exp (-(a.1 + x)))| +
        |ccmPolarParityArithmeticRemainder a r x| := by
          simpa using (abs_sub_le
            (a := (Real.exp (x / 2) + r * Real.exp (-x / 2)) *
              Real.log (1 + Real.exp (-(a.1 + x))))
            (b := 0) (c := ccmPolarParityArithmeticRemainder a r x))
    _ ≤ _ := add_le_add hterm hrem

end RHTower
