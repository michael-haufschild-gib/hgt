import GaloisForLFunctions.RHTower.Suzuki.SuzukiCarlemanFlatPortProfile

/-!
# The flat profile in the physical chart, and the logistic kernel

In the physical chart `s = e^{-L}` the flat profile `u(s) = F(-log s)` has square-integrable value
and non-square-integrable derivative: the two ray integrals

`∫ exp (-2√L) exp (-L) dL < ∞`,   `∫ exp (L - 2√L) / L dL = ∞`

decide membership, and the second diverges because `L - 2√L - log L → ∞`.  So the profile lies in
the completed boundary class and outside the raw spatial derivative domain.

The logistic kernel `k(y) = e^y/(1+e^y)^(2 : ℕ)` — the `L`-derivative of the Carleman cutoff factor —
is a probability density: its antiderivative is `-(1+e^y)⁻¹`.
-/

open Set MeasureTheory Filter Topology

namespace RHTower

noncomputable section

/-- The physical-chart square of the flat profile. -/
def flatPortValueDensity (L : ℝ) : ℝ := Real.exp (-2 * Real.sqrt L) * Real.exp (-L)

/-- The physical-chart square of the flat profile's spatial derivative. -/
def flatPortDerivativeDensity (L : ℝ) : ℝ := Real.exp (L - 2 * Real.sqrt L) / L

/-- **`(14)`: the flat profile is square integrable on the physical ray.** -/
theorem integrableOn_flatPortValueDensity :
    IntegrableOn flatPortValueDensity (Ioi (1:ℝ)) volume := by
  have hmajor : IntegrableOn (fun L : ℝ => Real.exp (-L)) (Ioi (1:ℝ)) volume :=
    integrableOn_exp_neg_Ioi 1
  refine Integrable.mono' hmajor ?_ ?_
  · apply Measurable.aestronglyMeasurable
    unfold flatPortValueDensity
    fun_prop
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with L hL
    have hLpos : (0:ℝ) < L := lt_trans zero_lt_one hL
    have hsq : 0 ≤ Real.sqrt L := Real.sqrt_nonneg L
    have h1 : Real.exp (-2 * Real.sqrt L) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    rw [Real.norm_eq_abs, flatPortValueDensity,
      abs_of_nonneg (by positivity : (0:ℝ) ≤ Real.exp (-2 * Real.sqrt L) * Real.exp (-L))]
    nlinarith [Real.exp_pos (-L), Real.exp_pos (-2 * Real.sqrt L)]

/-- The physical derivative density blows up: the flat profile is beyond `H¹`. -/
theorem tendsto_flatPortDerivativeDensity :
    Tendsto flatPortDerivativeDensity atTop atTop := by
  have hlogsqrt : ∀ L : ℝ, 0 < L → Real.log L ≤ 2 * Real.sqrt L := by
    intro L hL
    have hs : 0 < Real.sqrt L := Real.sqrt_pos.mpr hL
    have hlog : Real.log (Real.sqrt L) ≤ Real.sqrt L - 1 := Real.log_le_sub_one_of_pos hs
    have hsq : Real.log L = 2 * Real.log (Real.sqrt L) := by
      have h : Real.sqrt L ^ (2 : ℕ) = L := Real.sq_sqrt hL.le
      calc Real.log L = Real.log (Real.sqrt L ^ (2 : ℕ)) := by rw [h]
        _ = 2 * Real.log (Real.sqrt L) := by rw [Real.log_pow]; norm_num
    rw [hsq]
    linarith
  have hev : ∀ᶠ L : ℝ in atTop, L / 2 ≤ L - 2 * Real.sqrt L - Real.log L := by
    filter_upwards [eventually_ge_atTop (64:ℝ)] with L hL
    have hLpos : (0:ℝ) < L := by linarith
    have h4 : (8:ℝ) ≤ Real.sqrt L := by
      have : Real.sqrt 64 ≤ Real.sqrt L := Real.sqrt_le_sqrt hL
      rwa [show (64:ℝ) = 8 ^ (2 : ℕ) by norm_num, Real.sqrt_sq (by norm_num)] at this
    have hsq : Real.sqrt L * Real.sqrt L = L := Real.mul_self_sqrt hLpos.le
    have hlog := hlogsqrt L hLpos
    nlinarith [Real.sqrt_nonneg L]
  have hhalf : Tendsto (fun L : ℝ => L / 2) atTop atTop :=
    tendsto_id.atTop_div_const (by norm_num : (0:ℝ) < 2)
  have hinner : Tendsto (fun L : ℝ => L - 2 * Real.sqrt L - Real.log L) atTop atTop :=
    tendsto_atTop_mono' atTop hev hhalf
  have hexp : Tendsto (fun L : ℝ => Real.exp (L - 2 * Real.sqrt L - Real.log L)) atTop atTop :=
    Real.tendsto_exp_atTop.comp hinner
  refine hexp.congr' ?_
  filter_upwards [eventually_gt_atTop (0:ℝ)] with L hL
  rw [flatPortDerivativeDensity, Real.exp_sub, Real.exp_log hL]

/-- **`(13)`: the flat profile's spatial derivative is not square integrable.** -/
theorem not_integrableOn_flatPortDerivativeDensity :
    ¬ IntegrableOn flatPortDerivativeDensity (Ioi (1:ℝ)) volume :=
  not_integrableOn_Ioi_of_tendsto_atTop tendsto_flatPortDerivativeDensity 1

/-- The logistic kernel `k(y) = e^y/(1+e^y)^(2 : ℕ)`. -/
def logisticKernel (y : ℝ) : ℝ := Real.exp y / (1 + Real.exp y) ^ (2 : ℕ)

theorem logisticKernel_pos (y : ℝ) : 0 < logisticKernel y := by
  have hy := Real.exp_pos y
  unfold logisticKernel
  positivity

theorem continuous_logisticKernel : Continuous logisticKernel := by
  unfold logisticKernel
  have h : ∀ y : ℝ, (1 + Real.exp y) ^ (2 : ℕ) ≠ 0 := by
    intro y
    have := Real.exp_pos y
    positivity
  fun_prop (disch := intro y; exact h y)

/-- The logistic primitive `-(1+e^y)⁻¹`. -/
def logisticPrimitive (y : ℝ) : ℝ := -(1 + Real.exp y)⁻¹

theorem hasDerivAt_logisticPrimitive (y : ℝ) :
    HasDerivAt logisticPrimitive (logisticKernel y) y := by
  have hpos : (0:ℝ) < 1 + Real.exp y := by
    have := Real.exp_pos y
    linarith
  have hne : (1 + Real.exp y) ≠ 0 := ne_of_gt hpos
  have hbase : HasDerivAt (fun x : ℝ => 1 + Real.exp x) (Real.exp y) y := by
    have := (Real.hasDerivAt_exp y).const_add (1:ℝ)
    simpa using this
  have hinv : HasDerivAt (fun x : ℝ => ((1 + Real.exp x)⁻¹))
      (-Real.exp y / (1 + Real.exp y) ^ (2 : ℕ)) y := hbase.inv hne
  have hneg := hinv.neg
  have hfun : logisticPrimitive = fun x : ℝ => -((1 + Real.exp x)⁻¹) := by
    funext x
    rw [logisticPrimitive]
  have hval : -(-Real.exp y / (1 + Real.exp y) ^ (2 : ℕ)) = logisticKernel y := by
    simp only [logisticKernel]
    ring
  rw [hfun, ← hval]
  exact hneg

/-- The logistic kernel is bounded by the two-sided exponential. -/
theorem logisticKernel_le_exp_neg_abs (y : ℝ) : logisticKernel y ≤ Real.exp (-|y|) := by
  simp only [logisticKernel]
  rcases le_total 0 y with hy | hy
  · rw [abs_of_nonneg hy, div_le_iff₀ (by positivity)]
    have h1 : Real.exp y ≤ (1 + Real.exp y) := by
      linarith [Real.exp_pos y]
    have h2 : Real.exp (-y) * (1 + Real.exp y) ^ (2 : ℕ)
        = Real.exp (-y) * (1 + Real.exp y) * (1 + Real.exp y) := by ring
    rw [h2]
    have h3 : (1:ℝ) ≤ Real.exp (-y) * (1 + Real.exp y) := by
      rw [mul_add, mul_one, ← Real.exp_add]
      simp only [neg_add_cancel, Real.exp_zero]
      linarith [Real.exp_pos (-y)]
    nlinarith [Real.exp_pos y, Real.exp_pos (-y)]
  · rw [abs_of_nonpos hy, neg_neg, div_le_iff₀ (by positivity)]
    have h1 : (1:ℝ) ≤ (1 + Real.exp y) ^ (2 : ℕ) := by
      nlinarith [Real.exp_pos y]
    nlinarith [Real.exp_pos y]

end

end RHTower
