import Mathlib.NumberTheory.Harmonic.GammaDeriv

/-!
# Critical-prime polynomial-Fock Schatten exponent

For the polynomial doubling-Fock potential of degree `m`, put `a = m / 2 - 1`.  The adapted
prime tube has Schatten density `x ^ (a - q * (a - 1)) dx`.  This leaf proves that its improper
integral converges exactly for `q > m / (m - 4)`, including the endpoint divergence.
-/

open Set MeasureTheory

namespace RHTower

noncomputable section

/-- Polynomial doubling-Fock adapted-radius exponent `rho_m(x) asymp x⁻ᵃ`. -/
def criticalPrimeFockAdaptedExponent (m : ℝ) : ℝ := m / 2 - 1

/-- Exact Schatten abscissa predicted by the superquartic critical-prime tube. -/
def criticalPrimeFockSchattenThreshold (m : ℝ) : ℝ := m / (m - 4)

/-- Power of `x` in the one-dimensional adapted-tube Schatten integral. -/
def criticalPrimeFockSchattenDensityExponent (m q : ℝ) : ℝ :=
  criticalPrimeFockAdaptedExponent m -
    q * (criticalPrimeFockAdaptedExponent m - 1)

/-- Every finite superquartic polynomial-Fock threshold is strictly above one. -/
theorem criticalPrimeFockSchattenThreshold_gt_one
    {m : ℝ} (hm : 4 < m) :
    1 < criticalPrimeFockSchattenThreshold m := by
  rw [criticalPrimeFockSchattenThreshold]
  have hd : 0 < m - 4 := sub_pos.mpr hm
  rw [lt_div_iff₀ hd]
  linarith

/-- The adapted-tube density exponent crosses the improper-integral boundary `-1` exactly at
`q = m / (m - 4)`. -/
theorem criticalPrimeFockSchattenDensityExponent_lt_neg_one_iff
    {m q : ℝ} (hm : 4 < m) :
    criticalPrimeFockSchattenDensityExponent m q < -1 ↔
      criticalPrimeFockSchattenThreshold m < q := by
  rw [criticalPrimeFockSchattenDensityExponent,
    criticalPrimeFockAdaptedExponent,
    criticalPrimeFockSchattenThreshold]
  have hd : 0 < m - 4 := sub_pos.mpr hm
  rw [div_lt_iff₀ hd]
  constructor <;> intro h <;> nlinarith

/-- Exact integrability threshold of the critical-prime adapted-tube Schatten density. -/
theorem integrableOn_criticalPrimeFockSchattenDensity_iff
    {m q : ℝ} (hm : 4 < m) :
    IntegrableOn
        (fun x : ℝ => x ^ criticalPrimeFockSchattenDensityExponent m q)
        (Ioi 1) ↔
      criticalPrimeFockSchattenThreshold m < q := by
  rw [integrableOn_Ioi_rpow_iff (by norm_num),
    criticalPrimeFockSchattenDensityExponent_lt_neg_one_iff hm]

/-- Exact confinement-degree condition for a prescribed real regularization order. -/
theorem criticalPrimeFockSchattenThreshold_lt_iff
    {m q : ℝ} (hm : 4 < m) (hq : 1 < q) :
    criticalPrimeFockSchattenThreshold m < q ↔
      4 * q / (q - 1) < m := by
  have hmden : 0 < m - 4 := sub_pos.mpr hm
  have hqden : 0 < q - 1 := sub_pos.mpr hq
  rw [criticalPrimeFockSchattenThreshold, div_lt_iff₀ hmden,
    div_lt_iff₀ hqden]
  constructor <;> intro h <;> nlinarith

/-- A second regularized determinant is admissible at the scalar Schatten threshold exactly for
polynomial confinement degree strictly above eight. -/
theorem criticalPrimeFockSchattenThreshold_lt_two_iff
    {m : ℝ} (hm : 4 < m) :
    criticalPrimeFockSchattenThreshold m < 2 ↔ 8 < m := by
  have h := criticalPrimeFockSchattenThreshold_lt_iff hm (by norm_num : (1 : ℝ) < 2)
  norm_num at h
  exact h

end

end RHTower
