import GaloisForLFunctions.RHTower.ThetaRelativeErrorMass

/-!
# The tilted prime logarithm sum

For a positive tilt `δ` the Euler-edge sum

```text
μ(δ, Y) = ∑_{2 < p ≤ Y} p^{-1-δ} log p
```

is `(1 - Y^{-δ})/δ` up to an error bounded by one absolute constant, uniformly in `δ ∈ (0,1]` and
in the aperture `Y`.  Abel summation against the Chebyshev function produces a boundary term, the
elementary power integral, and a remainder controlled by the absolute relative-error mass.
-/

open Filter Topology Set MeasureTheory intervalIntegral Asymptotics

namespace RHTower

noncomputable section

/-! ## The elementary power integral at a negative exponent -/

theorem integral_rpow_sub_one_of_ne {a : ℝ} (ha : a ≠ 0) {u v : ℝ} (hu : 2 ≤ u) (hv : 2 ≤ v) :
    (∫ t in u..v, t ^ (a - 1)) = (v ^ a - u ^ a) / a := by
  have hsum : a - 1 + 1 = a := by ring
  have hne : a - 1 ≠ -1 := by
    intro hc
    exact ha (by linarith)
  have hzero : (0 : ℝ) ∉ Set.uIcc u v := by
    intro hmem
    rcases Set.mem_uIcc.mp hmem with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> linarith
  rw [integral_rpow (Or.inr ⟨hne, hzero⟩), hsum]

/-- The Abel integral at any nonzero exponent splits into the elementary power integral and the
relative-error remainder. -/
theorem integral_derivRpow_mul_theta_eq_of_ne {a x : ℝ} (ha : a ≠ 0) (hx : 2 ≤ x) :
    (∫ t in (2 : ℝ)..x, ((a - 1) * t ^ (a - 2)) * Chebyshev.theta t)
      = (a - 1) * ((x ^ a - (2 : ℝ) ^ a) / a)
        + (a - 1) * ∫ t in (2 : ℝ)..x, thetaError t * t ^ (a - 1) := by
  have hpt : ∀ t ∈ uIcc (2 : ℝ) x, ((a - 1) * t ^ (a - 2)) * Chebyshev.theta t
      = (a - 1) * t ^ (a - 1) + (a - 1) * (thetaError t * t ^ (a - 1)) := by
    intro t ht
    rw [uIcc_of_le hx] at ht
    have ht0 : (0 : ℝ) < t := by
      have := ht.1
      linarith
    have hrp : t ^ (a - 2) * t = t ^ (a - 1) := by
      nth_rewrite 2 [← Real.rpow_one t]
      rw [← Real.rpow_add ht0, show a - 2 + 1 = a - 1 by ring]
    rw [theta_eq_mul_thetaError ht0]
    calc ((a - 1) * t ^ (a - 2)) * (t * (1 + thetaError t))
        = (a - 1) * (t ^ (a - 2) * t) * (1 + thetaError t) := by ring
      _ = (a - 1) * t ^ (a - 1) * (1 + thetaError t) := by rw [hrp]
      _ = (a - 1) * t ^ (a - 1) + (a - 1) * (thetaError t * t ^ (a - 1)) := by ring
  have hI1 : IntervalIntegrable (fun t : ℝ => (a - 1) * t ^ (a - 1)) volume 2 x :=
    (HTGeometry.intervalIntegrable_rpowSubOne a le_rfl hx).const_mul _
  have hI2 : IntervalIntegrable
      (fun t : ℝ => (a - 1) * (thetaError t * t ^ (a - 1))) volume 2 x :=
    (intervalIntegrable_thetaError_mul hx).const_mul _
  rw [intervalIntegral.integral_congr hpt, intervalIntegral.integral_add hI1 hI2,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    integral_rpow_sub_one_of_ne ha le_rfl hx]

/-! ## The tilted sum -/

/-- The tilted prime logarithm sum `∑_{2 < p ≤ Y} p^{-1-δ} log p`. -/
def tiltedPrimeLogSum (δ Y : ℝ) : ℝ := primeRpowLogSumIoc (-δ) Y

/-- The uniform Abel constant of the tilted prime logarithm sum. -/
def tiltedPrimeLogSumConst : ℝ := 4 * Real.log 4 + 8 + 2 * thetaRelMass

theorem tiltedPrimeLogSum_eq {δ Y : ℝ} (hδ : 0 < δ) (hY : 2 ≤ Y) :
    tiltedPrimeLogSum δ Y
      = Y ^ (-δ) * (1 + thetaError Y) - (2 : ℝ) ^ (-δ - 1) * Chebyshev.theta 2
        + (1 + δ) * (((2 : ℝ) ^ (-δ) - Y ^ (-δ)) / δ)
        + (1 + δ) * ∫ t in (2 : ℝ)..Y, thetaError t * t ^ (-δ - 1) := by
  have hY0 : (0 : ℝ) < Y := by linarith
  have hne : (-δ) ≠ 0 := by
    intro h
    exact absurd (by linarith : δ = 0) (ne_of_gt hδ)
  have habel := primeRpowLogSumIoc_eq (a := -δ) hY
  have hsplit := integral_derivRpow_mul_theta_eq_of_ne (a := -δ) hne hY
  have hbdry : Y ^ (-δ - 1) * Chebyshev.theta Y = Y ^ (-δ) * (1 + thetaError Y) := by
    rw [theta_eq_mul_thetaError hY0]
    have hrp : Y ^ (-δ - 1) * Y = Y ^ (-δ) := by
      nth_rewrite 2 [← Real.rpow_one Y]
      rw [← Real.rpow_add hY0, show -δ - 1 + 1 = -δ by ring]
    calc Y ^ (-δ - 1) * (Y * (1 + thetaError Y))
        = (Y ^ (-δ - 1) * Y) * (1 + thetaError Y) := by ring
      _ = Y ^ (-δ) * (1 + thetaError Y) := by rw [hrp]
  have hval : (-δ - 1) * ((Y ^ (-δ) - (2 : ℝ) ^ (-δ)) / (-δ))
      = (1 + δ) * ((Y ^ (-δ) - (2 : ℝ) ^ (-δ)) / δ) := by
    field_simp
  have hswap : (1 + δ) * (((2 : ℝ) ^ (-δ) - Y ^ (-δ)) / δ)
      = -((1 + δ) * ((Y ^ (-δ) - (2 : ℝ) ^ (-δ)) / δ)) := by
    field_simp
    ring
  rw [tiltedPrimeLogSum, habel, hsplit]
  rw [show ((-δ) - 1 : ℝ) = -δ - 1 from rfl] at hbdry
  rw [hbdry, hval, hswap]
  ring

theorem abs_thetaTwo_le : |Chebyshev.theta 2| ≤ 2 * (Real.log 4 + 2) := by
  have h2 : (0 : ℝ) < 2 := by norm_num
  have hval : Chebyshev.theta 2 = 2 * (1 + thetaError 2) := theta_eq_mul_thetaError h2
  have habs : |thetaError 2| ≤ Real.log 4 + 1 := abs_thetaError_le le_rfl
  have hbound := abs_le.mp habs
  rw [hval, abs_le]
  constructor
  · nlinarith [hbound.1, hbound.2]
  · nlinarith [hbound.1, hbound.2]

theorem one_sub_rpow_div_le {δ : ℝ} (hδ : 0 < δ) : (1 - (2 : ℝ) ^ (-δ)) / δ ≤ Real.log 2 := by
  have hrp : (2 : ℝ) ^ (-δ) = Real.exp (-δ * Real.log 2) := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    ring_nf
  have hexp : (1 : ℝ) - δ * Real.log 2 ≤ Real.exp (-δ * Real.log 2) := by
    have h := Real.add_one_le_exp (-δ * Real.log 2)
    linarith
  rw [hrp, div_le_iff₀ hδ]
  linarith

theorem rpow_neg_le_one {δ Y : ℝ} (hδ : 0 ≤ δ) (hY : 1 ≤ Y) : Y ^ (-δ) ≤ 1 := by
  have h := Real.rpow_le_rpow_of_exponent_le hY (show -δ ≤ 0 by linarith)
  rwa [Real.rpow_zero] at h

theorem rpow_neg_pos {δ Y : ℝ} (hY : 0 < Y) : 0 < Y ^ (-δ) := Real.rpow_pos_of_pos hY _

/-- **The tilted prime logarithm sum, uniformly in the tilt.** -/
theorem abs_tiltedPrimeLogSum_sub_le {δ Y : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hY : 2 ≤ Y) :
    |tiltedPrimeLogSum δ Y - (1 - Y ^ (-δ)) / δ| ≤ tiltedPrimeLogSumConst := by
  have hY0 : (0 : ℝ) < Y := by linarith
  have hY1 : (1 : ℝ) ≤ Y := by linarith
  have hrpY := rpow_neg_le_one hδ0.le hY1
  have hrpY0 := rpow_neg_pos (δ := δ) hY0
  have hrp2 := rpow_neg_le_one (δ := δ) hδ0.le (by norm_num : (1 : ℝ) ≤ 2)
  have hrp20 := rpow_neg_pos (δ := δ) (show (0 : ℝ) < 2 by norm_num)
  have heq := tiltedPrimeLogSum_eq hδ0 hY
  -- the four bounded pieces
  have hthetaY : |thetaError Y| ≤ Real.log 4 + 1 := abs_thetaError_le hY
  have hbdry : |Y ^ (-δ) * (1 + thetaError Y)| ≤ Real.log 4 + 2 := by
    rw [abs_mul, abs_of_pos hrpY0]
    have habs : |1 + thetaError Y| ≤ Real.log 4 + 2 := by
      have h := abs_le.mp hthetaY
      rw [abs_le]
      constructor <;> nlinarith [h.1, h.2]
    nlinarith [habs, hrpY0, hrpY, abs_nonneg (1 + thetaError Y)]
  have hbase : |(2 : ℝ) ^ (-δ - 1) * Chebyshev.theta 2| ≤ 2 * (Real.log 4 + 2) := by
    have hrp : (2 : ℝ) ^ (-δ - 1) ≤ 1 := by
      have h := Real.rpow_le_rpow_of_exponent_le (show (1 : ℝ) ≤ 2 by norm_num)
        (show -δ - 1 ≤ 0 by linarith)
      rwa [Real.rpow_zero] at h
    have hrp0 : (0 : ℝ) < (2 : ℝ) ^ (-δ - 1) := Real.rpow_pos_of_pos (by norm_num) _
    rw [abs_mul, abs_of_pos hrp0]
    nlinarith [abs_thetaTwo_le, abs_nonneg (Chebyshev.theta 2)]
  have hlog2 := one_sub_rpow_div_le hδ0
  have hlog2nonneg : 0 ≤ (1 - (2 : ℝ) ^ (-δ)) / δ := by positivity
  have hrem : |(1 + δ) * ∫ t in (2 : ℝ)..Y, thetaError t * t ^ (-δ - 1)| ≤ 2 * thetaRelMass := by
    have hint := abs_integral_thetaError_mul_rpow_le (δ := δ) (x := Y) hδ0.le hY
    rw [abs_mul, abs_of_pos (by linarith : (0 : ℝ) < 1 + δ)]
    nlinarith [hint, thetaRelMass_nonneg, hδ1, hδ0]
  -- the power term splits into the main term and two bounded corrections
  have hpower : (1 + δ) * (((2 : ℝ) ^ (-δ) - Y ^ (-δ)) / δ)
      = (1 - Y ^ (-δ)) / δ - (1 - (2 : ℝ) ^ (-δ)) / δ + ((2 : ℝ) ^ (-δ) - Y ^ (-δ)) := by
    field_simp
    ring
  have hgap : |(2 : ℝ) ^ (-δ) - Y ^ (-δ)| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith
  have hsum : tiltedPrimeLogSum δ Y - (1 - Y ^ (-δ)) / δ
      = Y ^ (-δ) * (1 + thetaError Y) - (2 : ℝ) ^ (-δ - 1) * Chebyshev.theta 2
        - (1 - (2 : ℝ) ^ (-δ)) / δ + ((2 : ℝ) ^ (-δ) - Y ^ (-δ))
        + (1 + δ) * ∫ t in (2 : ℝ)..Y, thetaError t * t ^ (-δ - 1) := by
    rw [heq, hpower]
    ring
  rw [hsum, tiltedPrimeLogSumConst]
  have hb1 := abs_le.mp hbdry
  have hb2 := abs_le.mp hbase
  have hb3 := abs_le.mp hgap
  have hb4 := abs_le.mp hrem
  have hlog4 : Real.log 2 ≤ Real.log 4 := Real.log_le_log (by norm_num) (by norm_num)
  rw [abs_le]
  constructor
  · linarith [hb1.1, hb2.2, hb3.1, hb4.1, hlog2nonneg, hlog2, hlog4]
  · linarith [hb1.2, hb2.1, hb3.2, hb4.2, hlog2nonneg, hlog2, hlog4]

end

end RHTower
