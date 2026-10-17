import GaloisForLFunctions.BiScaleUncertainty.AnnularSourceRegularity
import GaloisForLFunctions.HTGeometry.CompactSupportIntegrationByParts

/-!
# Exact correlation geometry of the collar gauge derivative

The squared collar slope is the single-width correlation deficit divided by
the squared width. Compact-source integration by parts removes its mixed term
with the collar. The resulting gauge energy depends on collar width, not position.
-/

open MeasureTheory Set
open scoped CompactlySupported

namespace GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
open RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm RHTower.WeilMarkovPole
noncomputable section
set_option autoImplicit false

/-- Exact derivative energy is a finite-width source chord. -/
theorem integral_collarSourceSlope_sq (f : C_c(ℝ, ℝ)) (a b : ℝ) :
    (∫ u, collarSourceSlope f a b u ^ 2) =
      2 * (autocorr f 0 - autocorr f (Real.exp b)) / Real.exp b ^ 2 := by
  have hs := integral_shift_sub_shift_sq f.hasCompactSupport f.continuous
    (-Real.exp a) (-Real.exp a - Real.exp b)
  have ht : -Real.exp a - (-Real.exp a - Real.exp b) = Real.exp b := by ring
  rw [ht] at hs
  have he : (fun u => collarSourceSlope f a b u ^ 2) =
      fun u => (f (u + -Real.exp a) - f (u + (-Real.exp a - Real.exp b))) ^ 2 /
        Real.exp b ^ 2 := by
    funext u
    rw [collarSourceSlope, div_pow]
    simp only [sub_eq_add_neg, add_assoc]
  rw [he, integral_div, hs]

/-- Compact C¹ collar sources are orthogonal to their own derivatives. -/
theorem integral_collarSourceSlope_mul_collarSource (f : C_c(ℝ, ℝ)) (a b : ℝ) :
    (∫ u, collarSourceSlope f a b u * collarSource f a b u) = 0 := by
  have hd (u : ℝ) : HasDerivAt (fun u => collarSource f a b u * collarSource f a b u)
      (2 * (collarSourceSlope f a b u * collarSource f a b u)) u := by
    have hh := (hasDerivAt_collarSource f a b u).mul (hasDerivAt_collarSource f a b u)
    exact hh.congr_deriv (by ring)
  have hc : Continuous (fun u => 2 * (collarSourceSlope f a b u * collarSource f a b u)) :=
    continuous_const.mul ((continuous_collarSourceSlope f a b).mul (collarSource f a b).continuous)
  have hs : HasCompactSupport (fun u => collarSource f a b u * collarSource f a b u) :=
    (collarSource f a b).hasCompactSupport.mul_right
  have hz := HTGeometry.integral_deriv_eq_zero_of_hasCompactSupport hd hc hs
  rw [integral_const_mul] at hz
  linarith only [hz]

/-- The exact gauge energy is expressed only through source correlations. -/
def collarGaugeEnergy (f : C_c(ℝ, ℝ)) (a b : ℝ) : ℝ :=
  2 * (autocorr f 0 - autocorr f (Real.exp b)) / Real.exp b ^ 2 + collarEnergy f a b / 4

theorem integral_collarGaugeSource_sq (f : C_c(ℝ, ℝ)) (a b : ℝ) :
    (∫ u, collarGaugeSource f a b u ^ 2) = collarGaugeEnergy f a b := by
  have hs := integrable_sq (continuous_collarSourceSlope f a b)
    (hasCompactSupport_collarSourceSlope f a b)
  have hg := integrable_sq (g := (collarSource f a b : ℝ → ℝ))
    (collarSource f a b).continuous (collarSource f a b).hasCompactSupport
  have hc : Integrable (fun u => collarSourceSlope f a b u * collarSource f a b u) :=
    ((continuous_collarSourceSlope f a b).mul (collarSource f a b).continuous).integrable_of_hasCompactSupport
      (hasCompactSupport_collarSourceSlope f a b).mul_right
  have hsub : Integrable (fun u => collarSourceSlope f a b u ^ 2 -
      collarSourceSlope f a b u * collarSource f a b u) := hs.sub hc
  have hdiv : Integrable (fun u => collarSource f a b u ^ 2 / 4) := hg.div_const 4
  have he : (fun u => collarGaugeSource f a b u ^ 2) = fun u =>
      collarSourceSlope f a b u ^ 2 - collarSourceSlope f a b u * collarSource f a b u +
        collarSource f a b u ^ 2 / 4 := by
    funext u
    change (collarSourceSlope f a b u - collarSource f a b u / 2)^2 = _
    ring
  rw [he, integral_add hsub hdiv, integral_sub hs hc,
    integral_collarSourceSlope_mul_collarSource, sub_zero,
    integral_collarSourceSlope_sq, integral_div, integral_sq_eq_autocorr_zero]
  rfl

theorem collarGaugeEnergy_nonneg (f : C_c(ℝ, ℝ)) (a b : ℝ) :
    0 ≤ collarGaugeEnergy f a b := by
  rw [← integral_collarGaugeSource_sq]
  exact integral_nonneg fun _ => sq_nonneg _

private theorem collar_apply (f : C_c(ℝ, ℝ)) (a b u : ℝ) :
    collarSource f a b u =
      (∫ x in u - (Real.exp a + Real.exp b)..u - Real.exp a, f x) / Real.exp b := by
  have he := congrFun (collarSource_eq_annularAverage f a b) u
  change collarSource f a b u =
    (∫ x in u + -(Real.exp a + Real.exp b)..u + -(Real.exp a + Real.exp b) + Real.exp b, f x) /
      Real.exp b at he
  rw [show u + -(Real.exp a + Real.exp b) = u - (Real.exp a + Real.exp b) by ring,
    show u - (Real.exp a + Real.exp b) + Real.exp b = u - Real.exp a by ring] at he
  exact he

/-- Moving the collar position translates its source without changing shape. -/
theorem collarSource_change_position (f : C_c(ℝ, ℝ)) (a a' b u : ℝ) :
    collarSource f a b u = collarSource f a' b (u + (Real.exp a' - Real.exp a)) := by
  rw [collar_apply, collar_apply]
  congr 2 <;> ring

theorem collarEnergy_position_invariant (f : C_c(ℝ, ℝ)) (a a' b : ℝ) :
    collarEnergy f a b = collarEnergy f a' b := by
  rw [collarEnergy, collarEnergy, ← integral_sq_eq_autocorr_zero,
    ← integral_sq_eq_autocorr_zero]
  simp_rw [collarSource_change_position f a a' b]
  exact integral_add_right_eq_self (μ := volume)
    (fun u => collarSource f a' b u ^ 2) (Real.exp a' - Real.exp a)

theorem collarGaugeEnergy_position_invariant (f : C_c(ℝ, ℝ)) (a a' b : ℝ) :
    collarGaugeEnergy f a b = collarGaugeEnergy f a' b := by
  unfold collarGaugeEnergy
  rw [collarEnergy_position_invariant f a a' b]

end
end GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
