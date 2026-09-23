import GaloisForLFunctions.RHTower.OscillatoryMassRetention
import GaloisForLFunctions.RHTower.RadialPSWFSpeedMonotone

/-!
# The radial Liouville oscillation keeps half its mass, with error `O(1/c)`

Dunster's exterior radial expansion controls the solution *pointwise* by an envelope.  That is not
enough to say how much `L²` mass the main term carries, because the oscillating factor vanishes at
its zeros and no pointwise comparison survives there.

The two facts that repair this are already proved for the exterior radial speed
`S(σ,z) = √((z²−σ²)/(z²−1))`:

* `one_le_radialPSWFExteriorSpeed` — the speed never drops below `1`, so the phase `c·ξ_σ` has
  derivative at least `c`;
* `radialPSWFExteriorSpeed_deriv_nonpos` — the speed decays, so the phase derivative is monotone.

Together they are exactly the hypotheses of the nonstationary averaging estimate, and they give

`∫ w cos²(c ξ_σ) = (1/2) ∫ w + O(1/c)`

on every `[a,b] ⊂ (1,∞)`, with the error depending only on the endpoint values and the variation of
the weight — never on `∫ w`.  Since the weight of interest is itself of size `1/c`, the error is
smaller by a further factor `1/c`, and the main term keeps a definite share of the mass.
-/

open MeasureTheory Set

namespace RHTower

noncomputable section

/-- The exact derivative of the exterior radial speed, as a function. -/
def radialPSWFSpeedDeriv (sigma z : ℝ) : ℝ :=
  z * (sigma ^ (2 : ℕ) - 1) / ((z ^ (2 : ℕ) - 1) ^ (2 : ℕ) * radialPSWFExteriorSpeed sigma z)

theorem continuousOn_radialPSWFSpeedDeriv {sigma a b : ℝ} (hsigma : sigma ^ (2 : ℕ) ≤ 1) (ha : 1 < a) :
    ContinuousOn (radialPSWFSpeedDeriv sigma) (Icc a b) := by
  have hSc : ContinuousOn (radialPSWFExteriorSpeed sigma) (Icc a b) := fun x hx =>
    (continuousAt_radialPSWFExteriorSpeed sigma (ha.trans_le hx.1)).continuousWithinAt
  refine ContinuousOn.div (continuousOn_id.mul continuousOn_const)
    ((((continuousOn_id.pow 2).sub continuousOn_const).pow 2).mul hSc) ?_
  intro x hx
  have hx1 : 1 < x := ha.trans_le hx.1
  have hS : 0 < radialPSWFExteriorSpeed sigma x := radialPSWFExteriorSpeed_pos hsigma hx1
  have hd : (0 : ℝ) < x ^ (2 : ℕ) - 1 := by nlinarith
  positivity

/-- **The bandwidth-scaled radial phase averages a square to half.**  On every closed subinterval of
the exterior ray, the oscillating square differs from half the plain mass by at most the weight's
amplitude budget divided by the bandwidth `c`.  No hypothesis on the weight beyond one derivative. -/
theorem abs_integral_weight_mul_cos_sq_radialPhase_sub_half_le
    {a b c sigma : ℝ} (hab : a ≤ b) (ha : 1 < a) (hc : 0 < c)
    (hs0 : 0 ≤ sigma) (hs1 : sigma ≤ 1)
    {w w' : ℝ → ℝ}
    (hw : ∀ x ∈ Icc a b, HasDerivAt w (w' x) x) (hw'c : ContinuousOn w' (Icc a b)) :
    |(∫ t in a..b, w t * Real.cos (c * radialPSWFExteriorPhase sigma t) ^ (2 : ℕ))
        - (1 / 2) * ∫ t in a..b, w t|
      ≤ (|w b| + |w a| + ∫ t in a..b, |w' t|) / c := by
  have hsigma : sigma ^ (2 : ℕ) ≤ 1 := by nlinarith
  refine abs_integral_weight_mul_cos_sq_sub_half_le'
    (φ := fun t => c * radialPSWFExteriorPhase sigma t)
    (φ' := fun t => c * radialPSWFExteriorSpeed sigma t)
    (φ'' := fun t => c * radialPSWFSpeedDeriv sigma t)
    hab hc hw hw'c
    (fun x hx => (hasDerivAt_radialPSWFExteriorPhase sigma (ha.trans_le hx.1)).const_mul c)
    (fun x hx => (hasDerivAt_radialPSWFExteriorSpeed hsigma (ha.trans_le hx.1)).const_mul c)
    (continuousOn_const.mul (continuousOn_radialPSWFSpeedDeriv hsigma ha)) ?_ ?_
  · intro x hx
    have hneg := radialPSWFExteriorSpeed_deriv_nonpos hsigma (ha.trans_le hx.1)
    have : radialPSWFSpeedDeriv sigma x ≤ 0 := hneg
    nlinarith
  · intro x hx
    have hone := one_le_radialPSWFExteriorSpeed hs0 hs1 (ha.trans_le hx.1)
    rw [abs_of_nonneg (by nlinarith : (0:ℝ) ≤ c * radialPSWFExteriorSpeed sigma x)]
    nlinarith

/-- **Relative mass retention on the exterior radial ray.**  If the weight's amplitude budget is
small compared with `c` times its mass, the oscillating square keeps at least a quarter of it. -/
theorem quarter_integral_le_integral_weight_mul_cos_sq_radialPhase
    {a b c sigma : ℝ} (hab : a ≤ b) (ha : 1 < a) (hc : 0 < c)
    (hs0 : 0 ≤ sigma) (hs1 : sigma ≤ 1)
    {w w' : ℝ → ℝ}
    (hw : ∀ x ∈ Icc a b, HasDerivAt w (w' x) x) (hw'c : ContinuousOn w' (Icc a b))
    (hbudget : (|w b| + |w a| + ∫ t in a..b, |w' t|) / c ≤ (1 / 4) * ∫ t in a..b, w t) :
    (1 / 4) * (∫ t in a..b, w t)
      ≤ ∫ t in a..b, w t * Real.cos (c * radialPSWFExteriorPhase sigma t) ^ (2 : ℕ) := by
  have hmain := abs_integral_weight_mul_cos_sq_radialPhase_sub_half_le hab ha hc hs0 hs1 hw hw'c
  linarith [neg_le_of_abs_le hmain]

end

end RHTower
