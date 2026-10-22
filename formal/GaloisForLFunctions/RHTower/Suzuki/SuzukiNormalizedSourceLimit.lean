import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.ExpDecay

/-!
# The normalized half-interval sources converge to the Laplace profile

Reflecting `cosh` and `sinh` to the endpoint of the aperture and rescaling by `e^{-a}` gives

`e^{-a} cosh(a - z) = (e^{-z} + e^{-2a+z})/2`,   `e^{-a} sinh(a - z) = (e^{-z} - e^{-2a+z})/2`,

so both normalized sources differ from the fixed Laplace profile `e^{-z}/2` by the same
exponentially small term inside the aperture, and by the profile itself beyond it.  The two errors
combine into the exact expression `(2e^{-2a} - e^{-4a})/8`, which vanishes; the limit profile has
squared norm `1/8`.
-/

open MeasureTheory Filter Topology

noncomputable section

namespace GaloisForLFunctions.RHTower

/-- The reflected, rescaled even source, extended by zero past the aperture. -/
def normalizedEvenSource (a z : ℝ) : ℝ :=
  if z < a then Real.exp (-a) * Real.cosh (a - z) else 0

/-- The reflected, rescaled odd source, extended by zero past the aperture. -/
def normalizedOddSource (a z : ℝ) : ℝ :=
  if z < a then Real.exp (-a) * Real.sinh (a - z) else 0

/-- The limiting Laplace profile. -/
def laplaceSource (z : ℝ) : ℝ := Real.exp (-z) / 2

/-- A negative exponential rate decays at infinity. -/
theorem tendsto_exp_neg_const_mul {c : ℝ} (hc : 0 < c) :
    Tendsto (fun a : ℝ => Real.exp (-c * a)) atTop (𝓝 0) := by
  have h1 : Tendsto (fun a : ℝ => -c * a) atTop atBot := by
    have hpos : Tendsto (fun a : ℝ => c * a) atTop atTop :=
      Filter.Tendsto.const_mul_atTop hc tendsto_id
    refine Filter.Tendsto.congr (fun a => ?_) (tendsto_neg_atTop_atBot.comp hpos)
    show -(c * a) = -c * a
    ring
  exact Real.tendsto_exp_atBot.comp h1

/-! ## The exact pointwise errors -/

theorem normalizedEvenSource_sub {a z : ℝ} (hz : z < a) :
    normalizedEvenSource a z - laplaceSource z = Real.exp (-2 * a + z) / 2 := by
  rw [normalizedEvenSource, if_pos hz, laplaceSource, Real.cosh_eq]
  have h1 : Real.exp (-a) * Real.exp (a - z) = Real.exp (-z) := by
    rw [← Real.exp_add]; congr 1; ring
  have h2 : Real.exp (-a) * Real.exp (-(a - z)) = Real.exp (-2 * a + z) := by
    rw [← Real.exp_add]; congr 1; ring
  have expand : Real.exp (-a) * ((Real.exp (a - z) + Real.exp (-(a - z))) / 2)
      = (Real.exp (-a) * Real.exp (a - z) + Real.exp (-a) * Real.exp (-(a - z))) / 2 := by ring
  rw [expand, h1, h2]
  ring

theorem normalizedOddSource_sub {a z : ℝ} (hz : z < a) :
    normalizedOddSource a z - laplaceSource z = -(Real.exp (-2 * a + z) / 2) := by
  rw [normalizedOddSource, if_pos hz, laplaceSource, Real.sinh_eq]
  have h1 : Real.exp (-a) * Real.exp (a - z) = Real.exp (-z) := by
    rw [← Real.exp_add]; congr 1; ring
  have h2 : Real.exp (-a) * Real.exp (-(a - z)) = Real.exp (-2 * a + z) := by
    rw [← Real.exp_add]; congr 1; ring
  have expand : Real.exp (-a) * ((Real.exp (a - z) - Real.exp (-(a - z))) / 2)
      = (Real.exp (-a) * Real.exp (a - z) - Real.exp (-a) * Real.exp (-(a - z))) / 2 := by ring
  rw [expand, h1, h2]
  ring

theorem normalizedEvenSource_eq_zero {a z : ℝ} (hz : a ≤ z) : normalizedEvenSource a z = 0 := by
  rw [normalizedEvenSource, if_neg (not_lt.mpr hz)]

theorem normalizedOddSource_eq_zero {a z : ℝ} (hz : a ≤ z) : normalizedOddSource a z = 0 := by
  rw [normalizedOddSource, if_neg (not_lt.mpr hz)]

/-! ## The two error integrals -/

/-- The inner error integral. -/
theorem integral_innerError (a : ℝ) :
    (∫ z in (0 : ℝ)..a, (Real.exp (-2 * a + z) / 2) ^ (2 : ℕ))
      = (Real.exp (-2 * a) - Real.exp (-4 * a)) / 8 := by
  have hsq : ∀ z : ℝ, (Real.exp (-2 * a + z) / 2) ^ (2 : ℕ)
      = Real.exp (-4 * a) / 4 * Real.exp (2 * z) := by
    intro z
    rw [div_pow, ← Real.exp_nat_mul]
    have : Real.exp (2 * (-2 * a + z)) = Real.exp (-4 * a) * Real.exp (2 * z) := by
      rw [← Real.exp_add]; congr 1; ring
    push_cast
    rw [this]
    ring
  have hderiv : ∀ u ∈ Set.uIcc (0 : ℝ) a,
      HasDerivAt (fun u : ℝ => Real.exp (2 * u) / 2) (Real.exp (2 * u)) u := by
    intro u _
    have hin : HasDerivAt (fun u : ℝ => 2 * u) (2 : ℝ) u := by
      simpa using (hasDerivAt_id u).const_mul (2 : ℝ)
    have h : HasDerivAt (fun u : ℝ => Real.exp (2 * u)) (Real.exp (2 * u) * 2) u := hin.exp
    have h2 : HasDerivAt (fun u : ℝ => Real.exp (2 * u) / 2)
        (Real.exp (2 * u) * 2 / 2) u := h.div_const 2
    convert h2 using 1
    ring
  have hcont : IntervalIntegrable (fun u : ℝ => Real.exp (2 * u)) volume 0 a :=
    Continuous.intervalIntegrable (by fun_prop) _ _
  rw [intervalIntegral.integral_congr (g := fun z => Real.exp (-4 * a) / 4 * Real.exp (2 * z))
      (fun z _ => hsq z), intervalIntegral.integral_const_mul,
    intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont]
  have hmul : Real.exp (-4 * a) * Real.exp (2 * a) = Real.exp (-2 * a) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [mul_zero, Real.exp_zero]
  have hfin : Real.exp (-4 * a) / 4 * (Real.exp (2 * a) / 2 - 1 / 2)
      = (Real.exp (-4 * a) * Real.exp (2 * a) - Real.exp (-4 * a)) / 8 := by ring
  rw [hfin, hmul]

/-- The tail error integral. -/
theorem integral_tailError (a : ℝ) :
    (∫ z in Set.Ioi a, laplaceSource z ^ (2 : ℕ)) = Real.exp (-2 * a) / 8 := by
  have hsq : ∀ z : ℝ, laplaceSource z ^ (2 : ℕ) = (1 / 4 : ℝ) * Real.exp (-2 * z) := by
    intro z
    have h : Real.exp (-z) ^ (2 : ℕ) = Real.exp (-2 * z) := by
      rw [sq, ← Real.exp_add]; congr 1; ring
    rw [laplaceSource, div_pow, h]
    ring
  have hderiv : ∀ x ∈ Set.Ioi a,
      HasDerivAt (fun u : ℝ => -Real.exp (-2 * u) / 2) (Real.exp (-2 * x)) x := by
    intro x _
    have hin : HasDerivAt (fun u : ℝ => -2 * u) (-2 : ℝ) x := by
      simpa using (hasDerivAt_id x).const_mul (-2 : ℝ)
    have h : HasDerivAt (fun u : ℝ => Real.exp (-2 * u)) (Real.exp (-2 * x) * (-2)) x := hin.exp
    have h2 : HasDerivAt (fun u : ℝ => -Real.exp (-2 * u))
        (-(Real.exp (-2 * x) * (-2))) x := h.neg
    have h3 : HasDerivAt (fun u : ℝ => -Real.exp (-2 * u) / 2)
        (-(Real.exp (-2 * x) * (-2)) / 2) x := h2.div_const 2
    convert h3 using 1
    ring
  have hint : IntegrableOn (fun z : ℝ => Real.exp (-2 * z)) (Set.Ioi a) volume :=
    exp_neg_integrableOn_Ioi a (by norm_num)
  have hcont : ContinuousWithinAt (fun u : ℝ => -Real.exp (-2 * u) / 2) (Set.Ici a) a :=
    (Continuous.continuousWithinAt (by fun_prop))
  have hlim : Tendsto (fun u : ℝ => -Real.exp (-2 * u) / 2) atTop (𝓝 0) := by
    have hbase := tendsto_exp_neg_const_mul (by norm_num : (0:ℝ) < 2)
    simpa using (hbase.neg).div_const 2
  have hIoi := integral_Ioi_of_hasDerivAt_of_tendsto hcont hderiv hint hlim
  rw [setIntegral_congr_fun measurableSet_Ioi (fun z _ => hsq z), integral_const_mul, hIoi]
  ring

/-- **`(281)`: the total squared error of either normalized source.** -/
theorem sourceError_eq (a : ℝ) :
    (∫ z in (0 : ℝ)..a, (Real.exp (-2 * a + z) / 2) ^ (2 : ℕ))
        + (∫ z in Set.Ioi a, laplaceSource z ^ (2 : ℕ))
      = (2 * Real.exp (-2 * a) - Real.exp (-4 * a)) / 8 := by
  rw [integral_innerError, integral_tailError]
  ring

/-- The total squared error vanishes as the aperture grows. -/
theorem tendsto_sourceError_zero :
    Tendsto (fun a : ℝ => (2 * Real.exp (-2 * a) - Real.exp (-4 * a)) / 8) atTop (𝓝 0) := by
  have h2 := tendsto_exp_neg_const_mul (by norm_num : (0:ℝ) < 2)
  have h4 := tendsto_exp_neg_const_mul (by norm_num : (0:ℝ) < 4)
  have := ((h2.const_mul 2).sub h4).div_const 8
  simpa using this

/-- **`(281)`: the squared norm of the limiting Laplace profile is `1/8`.** -/
theorem integral_laplaceSource_sq :
    (∫ z in Set.Ioi (0 : ℝ), laplaceSource z ^ (2 : ℕ)) = 1 / 8 := by
  rw [integral_tailError]
  norm_num

end GaloisForLFunctions.RHTower
