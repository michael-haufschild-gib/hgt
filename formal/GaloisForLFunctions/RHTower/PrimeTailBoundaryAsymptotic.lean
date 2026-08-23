import GaloisForLFunctions.RHTower.PrimeTailCoPoissonBoundary
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# The boundary asymptotic of the prime-tail co-Poisson current

The co-Poisson current built from the divided-log von Mangoldt coefficients has an explicit
boundary law at the origin.  Writing `J` for the log-divided prime-power counting function, the
tail Dirichlet sum is recovered from `J` by an Abel transform obtained from Fubini applied to the
elementary identity `u^{-z} = z ∫_u^∞ v^{-z-1} dv`, and the resulting integral is evaluated by an
integration by parts whose remainder carries a second inverse logarithm.

Combining the two with the prime number theorem in log-divided form gives
`∑_{n > y} Λ(n)/log n · n^{-z} ∼ y^{1-z} / ((z-1) log y)`, hence the boundary law
`G_z(x) ∼ 1 / ((z-1) x log(1/x))` and the half-weight `L²` wall at the origin.
-/

namespace RHTower

open MeasureTheory Set Filter Topology

noncomputable section

/-! ## Tail integrals of a complex power divided by a power of the logarithm -/

/-- The tail integrand: a complex power divided by a power of the logarithm. -/
def logPowerTail (z : ℂ) (k : ℕ) (u : ℝ) : ℂ := (u : ℂ) ^ (-z) / (Real.log u : ℂ) ^ k

theorem norm_logPowerTail {z : ℂ} {k : ℕ} {u : ℝ} (hu : 1 < u) :
    ‖logPowerTail z k u‖ = u ^ (-z.re) / (Real.log u) ^ k := by
  have hu0 : (0 : ℝ) < u := by linarith
  have hlog : (0 : ℝ) < Real.log u := Real.log_pos hu
  rw [logPowerTail, norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hu0, norm_pow,
    Complex.norm_real, Real.norm_of_nonneg hlog.le]
  simp

/-- The tail integrand is dominated by a pure power once the logarithm is bounded below. -/
theorem norm_logPowerTail_le {z : ℂ} {k : ℕ} {y u : ℝ} (hy : 1 < y) (hu : y ≤ u) :
    ‖logPowerTail z k u‖ ≤ u ^ (-z.re) / (Real.log y) ^ k := by
  have hu1 : 1 < u := lt_of_lt_of_le hy hu
  have hlogy : (0 : ℝ) < Real.log y := Real.log_pos hy
  have hlogu : Real.log y ≤ Real.log u := Real.log_le_log (by linarith) hu
  rw [norm_logPowerTail hu1]
  have hpow : (Real.log y) ^ k ≤ (Real.log u) ^ k := by gcongr
  exact div_le_div_of_nonneg_left (Real.rpow_pos_of_pos (by linarith) _).le
    (by positivity) hpow

theorem integrableOn_logPowerTail {z : ℂ} {k : ℕ} {y : ℝ} (hy : 1 < y) (hz : 1 < z.re) :
    IntegrableOn (logPowerTail z k) (Ioi y) volume := by
  have hy0 : (0 : ℝ) < y := by linarith
  have hlogy : (0 : ℝ) < Real.log y := Real.log_pos hy
  have hmajor : IntegrableOn (fun u : ℝ => u ^ (-z.re) / (Real.log y) ^ k) (Ioi y) volume := by
    have := (integrableOn_Ioi_rpow_of_lt (a := -z.re) (by linarith) hy0)
    exact this.div_const _
  refine Integrable.mono' hmajor ?_ ?_
  · refine (Measurable.aestronglyMeasurable ?_).restrict
    refine Measurable.div ?_ ?_
    · exact measurable_ofReal_cpow (-z)
    · exact (Complex.measurable_ofReal.comp Real.measurable_log).pow_const k
  · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with u hu
    exact norm_logPowerTail_le hy (le_of_lt hu)

/-- **The tail bound.**  A complex power divided by `log^k` has tail mass at most
`y^{1-σ}/((σ-1) log^k y)`. -/
theorem norm_integral_logPowerTail_le {z : ℂ} {k : ℕ} {y : ℝ} (hy : 1 < y) (hz : 1 < z.re) :
    ‖∫ u in Ioi y, logPowerTail z k u‖
      ≤ y ^ (1 - z.re) / ((z.re - 1) * (Real.log y) ^ k) := by
  have hy0 : (0 : ℝ) < y := by linarith
  have hlogy : (0 : ℝ) < Real.log y := Real.log_pos hy
  have hmajor : IntegrableOn (fun u : ℝ => u ^ (-z.re) / (Real.log y) ^ k) (Ioi y) volume := by
    have := (integrableOn_Ioi_rpow_of_lt (a := -z.re) (by linarith) hy0)
    exact this.div_const _
  have hbound : ‖∫ u in Ioi y, logPowerTail z k u‖
      ≤ ∫ u in Ioi y, u ^ (-z.re) / (Real.log y) ^ k := by
    refine norm_integral_le_of_norm_le hmajor ?_
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with u hu
    exact norm_logPowerTail_le hy (le_of_lt hu)
  refine hbound.trans ?_
  rw [MeasureTheory.integral_div, integral_Ioi_rpow_of_lt (by linarith) hy0]
  have hrw : -y ^ (-z.re + 1) / (-z.re + 1) = y ^ (1 - z.re) / (z.re - 1) := by
    rw [show -z.re + 1 = 1 - z.re by ring]
    rw [show z.re - 1 = -(1 - z.re) by ring, div_neg, neg_div]
  rw [hrw, div_div]

/-! ## Integration by parts on the tail -/

/-- The primitive whose derivative is the tail integrand up to a second-logarithm remainder. -/
def logPowerPrimitive (z : ℂ) (u : ℝ) : ℂ :=
  (u : ℂ) ^ (1 - z) / ((1 - z) * (Real.log u : ℂ))

theorem hasDerivAt_ofReal_cpow (w : ℂ) {u : ℝ} (hu : 0 < u) :
    HasDerivAt (fun t : ℝ => (t : ℂ) ^ w) (w * (u : ℂ) ^ (w - 1)) u := by
  have hslit : (u : ℂ) ∈ Complex.slitPlane := by
    apply Complex.mem_slitPlane_iff.mpr
    left; simpa using hu
  have h := (hasDerivAt_id (u : ℂ)).cpow_const (c := w) (by simpa using hslit)
  simpa using h.comp_ofReal

theorem hasDerivAt_logPowerPrimitive {z : ℂ} (hz : z ≠ 1) {u : ℝ} (hu : 1 < u) :
    HasDerivAt (logPowerPrimitive z)
      (logPowerTail z 1 u - (1 / (1 - z)) * logPowerTail z 2 u) u := by
  have hu0 : (0 : ℝ) < u := by linarith
  have hlog : (0 : ℝ) < Real.log u := Real.log_pos hu
  have hlogc : (Real.log u : ℂ) ≠ 0 := by
    simpa using ne_of_gt hlog
  have huc : (u : ℂ) ≠ 0 := by
    simpa using ne_of_gt hu0
  have hzc : (1 : ℂ) - z ≠ 0 := sub_ne_zero.mpr (Ne.symm hz)
  have hnum : HasDerivAt (fun t : ℝ => (t : ℂ) ^ (1 - z))
      ((1 - z) * (u : ℂ) ^ (-z)) u := by
    have := hasDerivAt_ofReal_cpow (1 - z) hu0
    rwa [show (1 : ℂ) - z - 1 = -z by ring] at this
  have hden : HasDerivAt (fun t : ℝ => (1 - z) * (Real.log t : ℂ))
      ((1 - z) * ((u : ℝ)⁻¹ : ℂ)) u := by
    have hl : HasDerivAt (fun t : ℝ => (Real.log t : ℂ)) (((u : ℝ)⁻¹ : ℝ) : ℂ) u :=
      (Real.hasDerivAt_log (ne_of_gt hu0)).ofReal_comp
    simpa using hl.const_mul (1 - z)
  have hdenne : (1 - z) * (Real.log u : ℂ) ≠ 0 := mul_ne_zero hzc hlogc
  have hquot := hnum.div hden hdenne
  refine hquot.congr_deriv ?_
  have hupow : (u : ℂ) ^ (1 - z) = (u : ℂ) ^ (-z) * (u : ℂ) := by
    rw [show (1 : ℂ) - z = -z + 1 by ring, Complex.cpow_add _ _ huc]
    simp
  rw [logPowerTail, logPowerTail]
  field_simp
  rw [hupow]
  ring

theorem norm_logPowerPrimitive {z : ℂ} {u : ℝ} (hu : 1 < u) :
    ‖logPowerPrimitive z u‖ = u ^ (1 - z.re) / (‖1 - z‖ * Real.log u) := by
  have hu0 : (0 : ℝ) < u := by linarith
  have hlog : (0 : ℝ) < Real.log u := Real.log_pos hu
  rw [logPowerPrimitive, norm_div, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hu0,
    Complex.norm_real, Real.norm_of_nonneg hlog.le]
  simp

theorem tendsto_logPowerPrimitive {z : ℂ} (hz : 1 < z.re) :
    Tendsto (logPowerPrimitive z) atTop (𝓝 0) := by
  have hzne : z ≠ 1 := by
    intro h; rw [h] at hz; simp at hz
  have hnz : (0 : ℝ) < ‖1 - z‖ := by
    refine norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm hzne))
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hmaj : Tendsto (fun u : ℝ => u ^ (1 - z.re) / (‖1 - z‖ * Real.log 2)) atTop (𝓝 0) := by
    have := tendsto_rpow_neg_atTop (y := z.re - 1) (by linarith)
    have heq : (fun x : ℝ => x ^ (-(z.re - 1))) = fun x : ℝ => x ^ (1 - z.re) := by
      funext x; ring_nf
    rw [heq] at this
    simpa using this.div_const (‖1 - z‖ * Real.log 2)
  refine squeeze_zero_norm' ?_ hmaj
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with u hu
  have hu1 : (1 : ℝ) < u := by linarith
  have hlogu : Real.log 2 ≤ Real.log u := Real.log_le_log (by norm_num) hu
  rw [norm_logPowerPrimitive hu1]
  have hpos : (0 : ℝ) < ‖1 - z‖ * Real.log 2 := by positivity
  refine div_le_div_of_nonneg_left (Real.rpow_pos_of_pos (by linarith) _).le hpos ?_
  exact mul_le_mul_of_nonneg_left hlogu hnz.le

/-- **Integration by parts on the tail.**  The first-logarithm tail integral is the boundary term
plus a second-logarithm remainder. -/
theorem integral_logPowerTail_one {z : ℂ} (hz : 1 < z.re) {y : ℝ} (hy : 1 < y) :
    (∫ u in Ioi y, logPowerTail z 1 u)
      = (y : ℂ) ^ (1 - z) / ((z - 1) * (Real.log y : ℂ))
        - (1 / (z - 1)) * ∫ u in Ioi y, logPowerTail z 2 u := by
  have hzne : z ≠ 1 := by
    intro h; rw [h] at hz; simp at hz
  have hzc : (1 : ℂ) - z ≠ 0 := sub_ne_zero.mpr (Ne.symm hzne)
  have hzc' : z - (1 : ℂ) ≠ 0 := sub_ne_zero.mpr hzne
  have hy0 : (0 : ℝ) < y := by linarith
  have hlogy : (0 : ℝ) < Real.log y := Real.log_pos hy
  have hlogyc : (Real.log y : ℂ) ≠ 0 := by simpa using ne_of_gt hlogy
  have h1 : IntegrableOn (logPowerTail z 1) (Ioi y) volume := integrableOn_logPowerTail hy hz
  have h2 : IntegrableOn (logPowerTail z 2) (Ioi y) volume := integrableOn_logPowerTail hy hz
  have hint : IntegrableOn
      (fun u => logPowerTail z 1 u - (1 / (1 - z)) * logPowerTail z 2 u) (Ioi y) volume :=
    h1.sub (h2.const_mul _)
  have hFTC := integral_Ioi_of_hasDerivAt_of_tendsto
    (f := logPowerPrimitive z)
    (f' := fun u => logPowerTail z 1 u - (1 / (1 - z)) * logPowerTail z 2 u)
    ((hasDerivAt_logPowerPrimitive hzne hy).continuousAt.continuousWithinAt)
    (fun x hx => hasDerivAt_logPowerPrimitive hzne (lt_trans hy hx))
    hint (tendsto_logPowerPrimitive hz)
  rw [integral_sub h1 (h2.const_mul _), MeasureTheory.integral_const_mul] at hFTC
  have hFy : logPowerPrimitive z y = (y : ℂ) ^ (1 - z) / ((1 - z) * (Real.log y : ℂ)) := rfl
  rw [hFy] at hFTC
  have hsplit : (y : ℂ) ^ (1 - z) / ((1 - z) * (Real.log y : ℂ))
      = -((y : ℂ) ^ (1 - z) / ((z - 1) * (Real.log y : ℂ))) := by
    rw [show (1 : ℂ) - z = -(z - 1) by ring, neg_mul, div_neg]
  have hcoef : (1 : ℂ) / (1 - z) = -(1 / (z - 1)) := by
    rw [show (1 : ℂ) - z = -(z - 1) by ring, div_neg]
  rw [hsplit, hcoef] at hFTC
  linear_combination hFTC

/-! ## The elementary power tail -/

theorem integrableOn_cpow_neg_sub_one {z : ℂ} (hz : 0 < z.re) {c : ℝ} (hc : 0 < c) :
    IntegrableOn (fun u : ℝ => (u : ℂ) ^ (-z - 1)) (Ioi c) volume := by
  have hmajor : IntegrableOn (fun u : ℝ => u ^ (-z.re - 1)) (Ioi c) volume :=
    integrableOn_Ioi_rpow_of_lt (by linarith) hc
  refine Integrable.mono' hmajor ((measurable_ofReal_cpow (-z - 1)).aestronglyMeasurable.restrict) ?_
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with u hu
  have hu0 : (0 : ℝ) < u := lt_trans hc hu
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hu0]
  simp

/-- The elementary complex power tail: `∫_c^∞ u^{-z-1} du = c^{-z}/z`. -/
theorem integral_Ioi_cpow_neg_sub_one {z : ℂ} (hz : 0 < z.re) {c : ℝ} (hc : 0 < c) :
    (∫ u in Ioi c, (u : ℂ) ^ (-z - 1)) = (c : ℂ) ^ (-z) / z := by
  have hzne : z ≠ 0 := by
    intro h; rw [h] at hz; simp at hz
  have hderiv : ∀ x ∈ Ioi c, HasDerivAt (fun u : ℝ => -(u : ℂ) ^ (-z) / z)
      ((x : ℂ) ^ (-z - 1)) x := by
    intro x hx
    have hx0 : (0 : ℝ) < x := lt_trans hc hx
    have h := (hasDerivAt_ofReal_cpow (-z) hx0).neg.div_const z
    refine h.congr_deriv ?_
    field_simp
  have hlim : Tendsto (fun u : ℝ => -(u : ℂ) ^ (-z) / z) atTop (𝓝 0) := by
    have hmaj : Tendsto (fun u : ℝ => u ^ (-z.re) / ‖z‖) atTop (𝓝 0) := by
      have := tendsto_rpow_neg_atTop (y := z.re) hz
      simpa using this.div_const ‖z‖
    refine squeeze_zero_norm' ?_ hmaj
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with u hu
    rw [norm_div, norm_neg, Complex.norm_cpow_eq_rpow_re_of_pos hu]
    simp
  have := integral_Ioi_of_hasDerivAt_of_tendsto
    (f := fun u : ℝ => -(u : ℂ) ^ (-z) / z)
    (f' := fun u : ℝ => (u : ℂ) ^ (-z - 1))
    (((hasDerivAt_ofReal_cpow (-z) hc).neg.div_const z).continuousAt.continuousWithinAt)
    hderiv (integrableOn_cpow_neg_sub_one hz hc) hlim
  rw [this]
  field_simp
  ring

/-! ## The Abel transform of the prime tail -/

/-- The divided-log coefficient is the complexification of its real avatar. -/
theorem eulerLogDirichletCoeff_eq_ofReal (n : ℕ) :
    eulerLogDirichletCoeff n
      = (((ArithmeticFunction.vonMangoldt n : ℝ) / Real.log n : ℝ) : ℂ) := by
  rw [eulerLogDirichletCoeff, Complex.ofReal_div]
  congr 1
  rw [← Complex.ofReal_natCast, ← Complex.ofReal_log (by positivity)]

/-- The strict prime tail of the divided-log Dirichlet series. -/
def primeTailSum (z : ℂ) (y : ℝ) : ℂ :=
  ∑' n : ℕ, if y < (n : ℝ) then eulerLogDirichletCoeff n * (n : ℂ) ^ (-z) else 0

/-- The Abel integrand attached to a single index. -/
def abelTerm (z : ℂ) (y : ℝ) (n : ℕ) (u : ℝ) : ℂ :=
  if y < (n : ℝ) then
    Set.indicator (Set.Ici (n : ℝ))
      (fun t : ℝ => (t : ℂ) ^ (-z - 1) * eulerLogDirichletCoeff n) u
  else 0

theorem integrableOn_abelTerm {z : ℂ} (hz : 0 < z.re) {y : ℝ} (hy : 0 < y) (n : ℕ) :
    IntegrableOn (abelTerm z y n) (Ioi y) volume := by
  by_cases h : y < (n : ℝ)
  · have hrw : abelTerm z y n = Set.indicator (Set.Ici (n : ℝ))
        (fun t : ℝ => (t : ℂ) ^ (-z - 1) * eulerLogDirichletCoeff n) := by
      funext u; simp [abelTerm, h]
    rw [hrw]
    exact ((integrableOn_cpow_neg_sub_one hz hy).mul_const
      (eulerLogDirichletCoeff n)).indicator measurableSet_Ici
  · have hrw : abelTerm z y n = fun _ : ℝ => (0 : ℂ) := by
      funext u; simp [abelTerm, h]
    rw [hrw]
    exact integrable_zero ℝ ℂ (volume.restrict (Ioi y))

/-- Each Abel integrand contributes exactly one Dirichlet term. -/
theorem integral_abelTerm {z : ℂ} (hz : 0 < z.re) {y : ℝ} (hy : 0 < y) (n : ℕ) :
    (∫ u in Ioi y, abelTerm z y n u)
      = if y < (n : ℝ) then eulerLogDirichletCoeff n * (n : ℂ) ^ (-z) / z else 0 := by
  simp only [abelTerm]
  split_ifs with h
  · have hn0 : (0 : ℝ) < n := lt_trans hy h
    rw [MeasureTheory.setIntegral_indicator measurableSet_Ici,
      Set.inter_eq_right.mpr (Set.Ici_subset_Ioi.mpr h),
      MeasureTheory.integral_Ici_eq_integral_Ioi,
      MeasureTheory.integral_mul_const, integral_Ioi_cpow_neg_sub_one hz hn0,
      Complex.ofReal_natCast]
    ring
  · simp

theorem integral_norm_abelTerm_le {z : ℂ} (hz : 0 < z.re) {y : ℝ} (hy : 0 < y) (n : ℕ) :
    (∫ u in Ioi y, ‖abelTerm z y n u‖) ≤ (n : ℝ) ^ (-z.re) / z.re := by
  simp only [abelTerm]
  split_ifs with h
  · have hn0 : (0 : ℝ) < n := lt_trans hy h
    have hnorm : ∀ u : ℝ, ‖Set.indicator (Set.Ici (n : ℝ))
        (fun t : ℝ => (t : ℂ) ^ (-z - 1) * eulerLogDirichletCoeff n) u‖
        = Set.indicator (Set.Ici (n : ℝ))
          (fun t : ℝ => ‖(t : ℂ) ^ (-z - 1) * eulerLogDirichletCoeff n‖) u := by
      intro u
      by_cases hu : u ∈ Set.Ici (n : ℝ) <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, hu]
    simp only [hnorm]
    rw [MeasureTheory.setIntegral_indicator measurableSet_Ici,
      Set.inter_eq_right.mpr (Set.Ici_subset_Ioi.mpr h),
      MeasureTheory.integral_Ici_eq_integral_Ioi]
    have hpt : ∀ u ∈ Ioi (n : ℝ), ‖(u : ℂ) ^ (-z - 1) * eulerLogDirichletCoeff n‖
        ≤ u ^ (-z.re - 1) := by
      intro u hu
      have hu0 : (0 : ℝ) < u := lt_trans hn0 hu
      rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hu0]
      have h1 : ‖eulerLogDirichletCoeff n‖ ≤ 1 := norm_eulerLogDirichletCoeff_le_one n
      have h2 : (0 : ℝ) < u ^ (-z - 1).re := Real.rpow_pos_of_pos hu0 _
      calc u ^ (-z - 1).re * ‖eulerLogDirichletCoeff n‖ ≤ u ^ (-z - 1).re * 1 :=
            mul_le_mul_of_nonneg_left h1 h2.le
        _ = u ^ (-z.re - 1) := by simp
    have hmajor : IntegrableOn (fun u : ℝ => u ^ (-z.re - 1)) (Ioi (n : ℝ)) volume :=
      integrableOn_Ioi_rpow_of_lt (by linarith) hn0
    have hle : (∫ u in Ioi (n : ℝ), ‖(u : ℂ) ^ (-z - 1) * eulerLogDirichletCoeff n‖)
        ≤ ∫ u in Ioi (n : ℝ), u ^ (-z.re - 1) := by
      refine MeasureTheory.setIntegral_mono_on ?_ hmajor measurableSet_Ioi hpt
      exact ((integrableOn_cpow_neg_sub_one hz hn0).mul_const
        (eulerLogDirichletCoeff n)).norm
    refine hle.trans ?_
    rw [integral_Ioi_rpow_of_lt (by linarith) hn0]
    rw [show -z.re - 1 + 1 = -z.re by ring]
    rw [show -(n : ℝ) ^ (-z.re) / (-z.re) = (n : ℝ) ^ (-z.re) / z.re by
      rw [div_neg, neg_div, neg_neg]]
  · simp
    positivity

/-- The Abel integrands sum pointwise to the window increment of the counting function. -/
theorem tsum_abelTerm {z : ℂ} {y u : ℝ} (hy : 0 ≤ y) (hu : y < u) :
    (∑' n : ℕ, abelTerm z y n u)
      = (u : ℂ) ^ (-z - 1) * ((primeTailCount u : ℂ) - (primeTailCount y : ℂ)) := by
  have hu0 : (0 : ℝ) ≤ u := le_trans hy hu.le
  have hfl : ⌊y⌋₊ ≤ ⌊u⌋₊ := Nat.floor_mono hu.le
  have hsupp : ∀ n ∉ Finset.Ioc ⌊y⌋₊ ⌊u⌋₊, abelTerm z y n u = 0 := by
    intro n hn
    rw [Finset.mem_Ioc] at hn
    by_cases hyn : y < (n : ℝ)
    · have hlow : ⌊y⌋₊ < n := by
        have : (⌊y⌋₊ : ℝ) ≤ y := Nat.floor_le hy
        exact_mod_cast lt_of_le_of_lt this hyn
      have hup : ⌊u⌋₊ < n := Nat.lt_of_not_le (fun hle => hn ⟨hlow, hle⟩)
      have hun : u < (n : ℝ) := by
        refine lt_of_lt_of_le (Nat.lt_floor_add_one u) ?_
        exact_mod_cast hup
      simp only [abelTerm, if_pos hyn]
      exact Set.indicator_of_notMem (by simpa using not_le.mpr hun) _
    · simp only [abelTerm, if_neg hyn]
  rw [tsum_eq_sum hsupp]
  have hterm : ∀ n ∈ Finset.Ioc ⌊y⌋₊ ⌊u⌋₊,
      abelTerm z y n u = (u : ℂ) ^ (-z - 1) * eulerLogDirichletCoeff n := by
    intro n hn
    rw [Finset.mem_Ioc] at hn
    have hyn : y < (n : ℝ) := by
      refine lt_of_lt_of_le (Nat.lt_floor_add_one y) ?_
      exact_mod_cast hn.1
    have hnu : (n : ℝ) ≤ u := le_trans (by exact_mod_cast hn.2) (Nat.floor_le hu0)
    simp only [abelTerm, if_pos hyn]
    rw [Set.indicator_of_mem (by simpa using hnu)]
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
  congr 1
  have hsum := primeTailCount_split (X := u) hfl
  have hsplit : ∑ n ∈ Finset.Ioc ⌊y⌋₊ ⌊u⌋₊,
      (ArithmeticFunction.vonMangoldt n : ℝ) / Real.log n
      = primeTailCount u - primeTailCount y := by
    rw [hsum]
    simp [primeTailCount]
  rw [← Complex.ofReal_sub, ← hsplit, Complex.ofReal_sum]
  exact Finset.sum_congr rfl (fun n _ => eulerLogDirichletCoeff_eq_ofReal n)

/-- **The Abel transform.**  The strict prime tail is `z` times the Mellin-type integral of the
window increment of the log-divided counting function. -/
theorem primeTailSum_eq_integral {z : ℂ} (hz : 1 < z.re) {y : ℝ} (hy : 1 ≤ y) :
    primeTailSum z y
      = z * ∫ u in Ioi y,
          (u : ℂ) ^ (-z - 1) * ((primeTailCount u : ℂ) - (primeTailCount y : ℂ)) := by
  have hz0 : (0 : ℝ) < z.re := by linarith
  have hy0 : (0 : ℝ) < y := by linarith
  have hzne : z ≠ 0 := by
    intro h; rw [h] at hz0; simp at hz0
  have hsum : Summable (fun n : ℕ => ∫ u in Ioi y, ‖abelTerm z y n u‖) := by
    refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => integral_norm_abelTerm_le hz0 hy0 n) ?_
    · exact MeasureTheory.integral_nonneg (fun u => norm_nonneg _)
    · exact (summable_rpow_neg hz).div_const z.re
  have hpoint : ∀ᵐ u : ℝ ∂(volume.restrict (Ioi y)),
      (u : ℂ) ^ (-z - 1) * ((primeTailCount u : ℂ) - (primeTailCount y : ℂ))
        = ∑' n : ℕ, abelTerm z y n u := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with u hu
    exact (tsum_abelTerm (by linarith) hu).symm
  rw [MeasureTheory.integral_congr_ae hpoint,
    ← MeasureTheory.integral_tsum_of_summable_integral_norm
      (fun n => integrableOn_abelTerm hz0 hy0 n) hsum]
  rw [tsum_congr (fun n => integral_abelTerm hz0 hy0 n), primeTailSum]
  rw [← tsum_mul_left]
  refine tsum_congr (fun n => ?_)
  split_ifs with h
  · field_simp
  · simp

/-! ## Splitting the Abel integral -/

theorem primeTailCount_mono : Monotone primeTailCount := by
  intro a b hab
  refine Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.Ioc_subset_Ioc_right (Nat.floor_mono hab)) (fun n _ _ => ?_)
  exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.log_natCast_nonneg n)

theorem measurable_primeTailCount : Measurable primeTailCount :=
  primeTailCount_mono.measurable

/-- The log-divided counting function obeys a linear bound. -/
theorem exists_primeTailCount_le_linear :
    ∃ C : ℝ, 0 < C ∧ ∀ u : ℝ, 1 ≤ u → primeTailCount u ≤ C * u := by
  obtain ⟨C, hC0, hC⟩ := exists_chebyshevPsiReal_le_linear
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨C / Real.log 2, by positivity, fun u hu => ?_⟩
  have h1 : primeTailCount u ≤ chebyshevPsi ⌊u⌋₊ / Real.log 2 :=
    primeTailCount_low_le ⌊u⌋₊
  have h2 : chebyshevPsi ⌊u⌋₊ ≤ C * u := hC u hu
  calc primeTailCount u ≤ chebyshevPsi ⌊u⌋₊ / Real.log 2 := h1
    _ ≤ C * u / Real.log 2 := by gcongr
    _ = C / Real.log 2 * u := by ring

/-- The deviation of the counting function from its principal term. -/
def primeTailError (u : ℝ) : ℝ := primeTailCount u - u / Real.log u

theorem integrableOn_cpow_mul_primeTailCount {z : ℂ} (hz : 1 < z.re) {y : ℝ} (hy : 1 ≤ y) :
    IntegrableOn (fun u : ℝ => (u : ℂ) ^ (-z - 1) * (primeTailCount u : ℂ)) (Ioi y) volume := by
  obtain ⟨C, hC0, hC⟩ := exists_primeTailCount_le_linear
  have hy0 : (0 : ℝ) < y := by linarith
  have hmajor : IntegrableOn (fun u : ℝ => C * u ^ (-z.re)) (Ioi y) volume :=
    (integrableOn_Ioi_rpow_of_lt (a := -z.re) (by linarith) hy0).const_mul C
  refine Integrable.mono' hmajor ?_ ?_
  · exact ((measurable_ofReal_cpow (-z - 1)).mul
      (Complex.measurable_ofReal.comp measurable_primeTailCount)).aestronglyMeasurable.restrict
  · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with u hu
    have hu0 : (0 : ℝ) < u := lt_trans hy0 hu
    have hu1 : (1 : ℝ) ≤ u := le_trans hy (le_of_lt hu)
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hu0, Complex.norm_real,
      Real.norm_of_nonneg (primeTailCount_nonneg u)]
    have hpow : u ^ (-z - 1).re = u ^ (-z.re) * u⁻¹ := by
      rw [← Real.rpow_neg_one u, ← Real.rpow_add hu0]
      congr 1
      simp
    rw [hpow]
    have hsmall : u⁻¹ * primeTailCount u ≤ C := by
      rw [inv_mul_eq_div, div_le_iff₀ hu0]
      exact hC u hu1
    calc u ^ (-z.re) * u⁻¹ * primeTailCount u = u ^ (-z.re) * (u⁻¹ * primeTailCount u) := by ring
      _ ≤ u ^ (-z.re) * C := by
          exact mul_le_mul_of_nonneg_left hsmall (Real.rpow_pos_of_pos hu0 _).le
      _ = C * u ^ (-z.re) := by ring

end

end RHTower
