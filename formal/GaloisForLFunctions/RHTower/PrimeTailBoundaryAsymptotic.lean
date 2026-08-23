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
    rw [hpow]
    have hsmall : u⁻¹ * primeTailCount u ≤ C := by
      rw [inv_mul_eq_div, div_le_iff₀ hu0]
      exact hC u hu1
    calc u ^ (-z.re) * u⁻¹ * primeTailCount u = u ^ (-z.re) * (u⁻¹ * primeTailCount u) := by ring
      _ ≤ u ^ (-z.re) * C := by
          exact mul_le_mul_of_nonneg_left hsmall (Real.rpow_pos_of_pos hu0 _).le
      _ = C * u ^ (-z.re) := by ring

theorem cpow_mul_primeTailCount_eq {z : ℂ} {u : ℝ} (hu : 1 < u) :
    (u : ℂ) ^ (-z - 1) * (primeTailCount u : ℂ)
      = logPowerTail z 1 u + (u : ℂ) ^ (-z - 1) * (primeTailError u : ℂ) := by
  have hu0 : (0 : ℝ) < u := by linarith
  have huc : (u : ℂ) ≠ 0 := by simpa using ne_of_gt hu0
  have hmain : (u : ℂ) ^ (-z - 1) * (((u / Real.log u : ℝ)) : ℂ) = logPowerTail z 1 u := by
    rw [Complex.ofReal_div, logPowerTail, pow_one]
    rw [show (u : ℂ) ^ (-z - 1) * ((u : ℂ) / (Real.log u : ℂ))
        = ((u : ℂ) ^ (-z - 1) * (u : ℂ)) / (Real.log u : ℂ) by ring]
    congr 1
    have hstep : (u : ℂ) ^ (-z) = (u : ℂ) ^ (-z - 1) * (u : ℂ) := by
      rw [show (-z : ℂ) = (-z - 1) + 1 by ring, Complex.cpow_add _ _ huc]
      simp
    exact hstep.symm
  have hsplit : (primeTailCount u : ℂ)
      = (primeTailError u : ℂ) + (((u / Real.log u : ℝ)) : ℂ) := by
    rw [primeTailError]
    push_cast
    ring
  rw [hsplit, mul_add, hmain]
  ring

theorem integrableOn_cpow_mul_primeTailError {z : ℂ} (hz : 1 < z.re) {y : ℝ} (hy : 1 < y) :
    IntegrableOn (fun u : ℝ => (u : ℂ) ^ (-z - 1) * (primeTailError u : ℂ)) (Ioi y) volume := by
  have h1 := integrableOn_cpow_mul_primeTailCount hz hy.le
  have h2 := integrableOn_logPowerTail (k := 1) hy hz
  have hcongr : ∀ u ∈ Ioi y, (u : ℂ) ^ (-z - 1) * (primeTailError u : ℂ)
      = (u : ℂ) ^ (-z - 1) * (primeTailCount u : ℂ) - logPowerTail z 1 u := by
    intro u hu
    rw [cpow_mul_primeTailCount_eq (lt_trans hy hu)]
    ring
  refine (h1.sub h2).congr_fun_ae ?_
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with u hu
  exact (hcongr u hu).symm

/-- **Splitting the Abel integral.**  The window integral separates into the principal tail, the
error tail and the boundary value of the counting function. -/
theorem integral_abel_split {z : ℂ} (hz : 1 < z.re) {y : ℝ} (hy : 1 < y) :
    (∫ u in Ioi y, (u : ℂ) ^ (-z - 1) * ((primeTailCount u : ℂ) - (primeTailCount y : ℂ)))
      = (∫ u in Ioi y, logPowerTail z 1 u)
        + (∫ u in Ioi y, (u : ℂ) ^ (-z - 1) * (primeTailError u : ℂ))
        - (primeTailCount y : ℂ) * ((y : ℂ) ^ (-z) / z) := by
  have hz0 : (0 : ℝ) < z.re := by linarith
  have hy0 : (0 : ℝ) < y := by linarith
  have h1 := integrableOn_logPowerTail (k := 1) hy hz
  have h2 := integrableOn_cpow_mul_primeTailError hz hy
  have h3 := integrableOn_cpow_neg_sub_one hz0 hy0
  have hcongr : ∀ᵐ u : ℝ ∂(volume.restrict (Ioi y)),
      (u : ℂ) ^ (-z - 1) * ((primeTailCount u : ℂ) - (primeTailCount y : ℂ))
        = (logPowerTail z 1 u + (u : ℂ) ^ (-z - 1) * (primeTailError u : ℂ))
          - (primeTailCount y : ℂ) * (u : ℂ) ^ (-z - 1) := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with u hu
    rw [mul_sub, cpow_mul_primeTailCount_eq (lt_trans hy hu)]
    ring
  rw [MeasureTheory.integral_congr_ae hcongr,
    MeasureTheory.integral_sub
      (f := fun u : ℝ => logPowerTail z 1 u + (u : ℂ) ^ (-z - 1) * (primeTailError u : ℂ))
      (g := fun u : ℝ => (primeTailCount y : ℂ) * (u : ℂ) ^ (-z - 1))
      (h1.add h2) (h3.const_mul _),
    MeasureTheory.integral_add h1 h2, MeasureTheory.integral_const_mul,
    integral_Ioi_cpow_neg_sub_one hz0 hy0]

/-- The remainder in the boundary asymptotic. -/
def primeTailRemainder (z : ℂ) (y : ℝ) : ℂ :=
  -(z / (z - 1)) * (∫ u in Ioi y, logPowerTail z 2 u)
    + z * (∫ u in Ioi y, (u : ℂ) ^ (-z - 1) * (primeTailError u : ℂ))
    - (primeTailError y : ℂ) * (y : ℂ) ^ (-z)

/-- **The boundary decomposition.**  The strict prime tail is the principal term plus the
remainder. -/
theorem primeTailSum_eq_main_add_remainder {z : ℂ} (hz : 1 < z.re) {y : ℝ} (hy : 1 < y) :
    primeTailSum z y
      = (y : ℂ) ^ (1 - z) / ((z - 1) * (Real.log y : ℂ)) + primeTailRemainder z y := by
  have hz0 : (0 : ℝ) < z.re := by linarith
  have hy0 : (0 : ℝ) < y := by linarith
  have hzne : z ≠ 0 := by intro h; rw [h] at hz0; simp at hz0
  have hzne1 : z - (1 : ℂ) ≠ 0 := by
    refine sub_ne_zero.mpr ?_
    intro h; rw [h] at hz; simp at hz
  have hlogy : (0 : ℝ) < Real.log y := Real.log_pos hy
  have hlogyc : (Real.log y : ℂ) ≠ 0 := by simpa using ne_of_gt hlogy
  have hyc : (y : ℂ) ≠ 0 := by simpa using ne_of_gt hy0
  rw [primeTailSum_eq_integral hz hy.le, integral_abel_split hz hy,
    integral_logPowerTail_one hz hy, primeTailRemainder]
  have hJy : (primeTailCount y : ℂ)
      = (primeTailError y : ℂ) + (y : ℂ) / (Real.log y : ℂ) := by
    rw [primeTailError]
    push_cast
    ring
  rw [hJy]
  have hpow : (y : ℂ) ^ (1 - z) = (y : ℂ) ^ (-z) * (y : ℂ) := by
    rw [show (1 : ℂ) - z = -z + 1 by ring, Complex.cpow_add _ _ hyc]
    simp
  field_simp
  rw [hpow]
  ring

/-! ## Bounding the remainder -/

/-- The error tail is small once the counting error is relatively small. -/
theorem norm_integral_cpow_mul_primeTailError_le {z : ℂ} (hz : 1 < z.re) {y δ : ℝ} (hy : 1 < y)
    (hδ : 0 ≤ δ) (hE : ∀ u : ℝ, y ≤ u → |primeTailError u| ≤ δ * (u / Real.log u)) :
    ‖∫ u in Ioi y, (u : ℂ) ^ (-z - 1) * (primeTailError u : ℂ)‖
      ≤ δ * y ^ (1 - z.re) / ((z.re - 1) * Real.log y) := by
  have hy0 : (0 : ℝ) < y := by linarith
  have hlogy : (0 : ℝ) < Real.log y := Real.log_pos hy
  have hmajor : IntegrableOn (fun u : ℝ => δ / Real.log y * u ^ (-z.re)) (Ioi y) volume :=
    (integrableOn_Ioi_rpow_of_lt (a := -z.re) (by linarith) hy0).const_mul _
  have hbound : ‖∫ u in Ioi y, (u : ℂ) ^ (-z - 1) * (primeTailError u : ℂ)‖
      ≤ ∫ u in Ioi y, δ / Real.log y * u ^ (-z.re) := by
    refine norm_integral_le_of_norm_le hmajor ?_
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with u hu
    have hu0 : (0 : ℝ) < u := lt_trans hy0 hu
    have hu1 : (1 : ℝ) < u := lt_trans hy hu
    have hlogu : (0 : ℝ) < Real.log u := Real.log_pos hu1
    have hlogle : Real.log y ≤ Real.log u := Real.log_le_log hy0 hu.le
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hu0, Complex.norm_real,
      Real.norm_eq_abs]
    have hEu : |primeTailError u| ≤ δ * (u / Real.log u) := hE u hu.le
    have hpow : u ^ (-z - 1).re = u ^ (-z.re) * u⁻¹ := by
      rw [← Real.rpow_neg_one u, ← Real.rpow_add hu0]
      congr 1
    rw [hpow]
    have hstep : u ^ (-z.re) * u⁻¹ * |primeTailError u|
        ≤ u ^ (-z.re) * u⁻¹ * (δ * (u / Real.log u)) := by
      refine mul_le_mul_of_nonneg_left hEu ?_
      positivity
    refine hstep.trans ?_
    have hcalc : u ^ (-z.re) * u⁻¹ * (δ * (u / Real.log u))
        = δ / Real.log u * u ^ (-z.re) := by
      field_simp
    rw [hcalc]
    refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_pos_of_pos hu0 _).le
    exact div_le_div_of_nonneg_left hδ hlogy hlogle
  refine hbound.trans ?_
  rw [MeasureTheory.integral_const_mul, integral_Ioi_rpow_of_lt (by linarith) hy0,
    show -z.re + 1 = 1 - z.re by ring,
    show -y ^ (1 - z.re) / (1 - z.re) = y ^ (1 - z.re) / (z.re - 1) by
      rw [show z.re - 1 = -(1 - z.re) by ring, div_neg, neg_div]]
  refine le_of_eq ?_
  field_simp

theorem norm_primeTailRemainder_le {z : ℂ} (hz : 1 < z.re) {y δ : ℝ} (hy : 1 < y) (hδ : 0 ≤ δ)
    (hE : ∀ u : ℝ, y ≤ u → |primeTailError u| ≤ δ * (u / Real.log u)) :
    ‖primeTailRemainder z y‖
      ≤ ‖z‖ / ‖z - 1‖ * (y ^ (1 - z.re) / ((z.re - 1) * (Real.log y) ^ 2))
        + ‖z‖ * (δ * y ^ (1 - z.re) / ((z.re - 1) * Real.log y))
        + δ * (y ^ (1 - z.re) / Real.log y) := by
  have hy0 : (0 : ℝ) < y := by linarith
  have hlogy : (0 : ℝ) < Real.log y := Real.log_pos hy
  have hzne1 : z - (1 : ℂ) ≠ 0 := by
    refine sub_ne_zero.mpr ?_
    intro h; rw [h] at hz; simp at hz
  have h1 : ‖-(z / (z - 1)) * ∫ u in Ioi y, logPowerTail z 2 u‖
      ≤ ‖z‖ / ‖z - 1‖ * (y ^ (1 - z.re) / ((z.re - 1) * (Real.log y) ^ 2)) := by
    rw [norm_mul, norm_neg, norm_div]
    refine mul_le_mul_of_nonneg_left (norm_integral_logPowerTail_le hy hz) ?_
    positivity
  have h2 : ‖z * ∫ u in Ioi y, (u : ℂ) ^ (-z - 1) * (primeTailError u : ℂ)‖
      ≤ ‖z‖ * (δ * y ^ (1 - z.re) / ((z.re - 1) * Real.log y)) := by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left
      (norm_integral_cpow_mul_primeTailError_le hz hy hδ hE) (norm_nonneg _)
  have h3 : ‖(primeTailError y : ℂ) * (y : ℂ) ^ (-z)‖ ≤ δ * (y ^ (1 - z.re) / Real.log y) := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      Complex.norm_cpow_eq_rpow_re_of_pos hy0]
    have hEy : |primeTailError y| ≤ δ * (y / Real.log y) := hE y le_rfl
    have hpow : y ^ (-z).re = y ^ (1 - z.re) * y⁻¹ := by
      rw [← Real.rpow_neg_one y, ← Real.rpow_add hy0]
      congr 1
      simp
      ring
    rw [hpow]
    have hstep : |primeTailError y| * (y ^ (1 - z.re) * y⁻¹)
        ≤ (δ * (y / Real.log y)) * (y ^ (1 - z.re) * y⁻¹) := by
      refine mul_le_mul_of_nonneg_right hEy ?_
      positivity
    refine hstep.trans ?_
    rw [le_iff_eq_or_lt]
    left
    field_simp
  rw [primeTailRemainder]
  calc ‖-(z / (z - 1)) * (∫ u in Ioi y, logPowerTail z 2 u)
        + z * (∫ u in Ioi y, (u : ℂ) ^ (-z - 1) * (primeTailError u : ℂ))
        - (primeTailError y : ℂ) * (y : ℂ) ^ (-z)‖
      ≤ ‖-(z / (z - 1)) * (∫ u in Ioi y, logPowerTail z 2 u)
          + z * (∫ u in Ioi y, (u : ℂ) ^ (-z - 1) * (primeTailError u : ℂ))‖
        + ‖(primeTailError y : ℂ) * (y : ℂ) ^ (-z)‖ := norm_sub_le _ _
    _ ≤ (‖-(z / (z - 1)) * (∫ u in Ioi y, logPowerTail z 2 u)‖
          + ‖z * (∫ u in Ioi y, (u : ℂ) ^ (-z - 1) * (primeTailError u : ℂ))‖)
        + ‖(primeTailError y : ℂ) * (y : ℂ) ^ (-z)‖ := by
        gcongr
        exact norm_add_le _ _
    _ ≤ _ := by gcongr

/-! ## The boundary asymptotic -/

theorem eventually_abs_primeTailError_le {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ u : ℝ in atTop, |primeTailError u| ≤ δ * (u / Real.log u) := by
  have hlim : Tendsto (fun u : ℝ => primeTailCount u * Real.log u / u - 1) atTop (𝓝 0) := by
    simpa using tendsto_primeTailCount.sub (tendsto_const_nhds (x := (1 : ℝ)))
  filter_upwards [eventually_gt_atTop (1 : ℝ), Metric.tendsto_nhds.mp hlim δ hδ] with u hu hsmall
  have hu0 : (0 : ℝ) < u := by linarith
  have hlogu : (0 : ℝ) < Real.log u := Real.log_pos hu
  have habs : |primeTailCount u * Real.log u / u - 1| < δ := by
    rw [Real.dist_eq, sub_zero] at hsmall
    exact hsmall
  have hid : primeTailError u
      = (u / Real.log u) * (primeTailCount u * Real.log u / u - 1) := by
    rw [primeTailError]
    field_simp
  rw [hid, abs_mul, abs_of_pos (by positivity)]
  calc (u / Real.log u) * |primeTailCount u * Real.log u / u - 1|
      ≤ (u / Real.log u) * δ := mul_le_mul_of_nonneg_left habs.le (by positivity)
    _ = δ * (u / Real.log u) := by ring

/-- **Card equations (13)–(15).**  The strict prime tail obeys the boundary law
`∑_{n > y} Λ(n)/log n · n^{-z} ∼ y^{1-z} / ((z-1) log y)`. -/
theorem tendsto_primeTailSum_div {z : ℂ} (hz : 1 < z.re) :
    Tendsto (fun y : ℝ => primeTailSum z y * ((z - 1) * (Real.log y : ℂ)) / (y : ℂ) ^ (1 - z))
      atTop (𝓝 1) := by
  have hzne1 : z - (1 : ℂ) ≠ 0 := by
    refine sub_ne_zero.mpr ?_
    intro h; rw [h] at hz; simp at hz
  have hnz1 : (0 : ℝ) < ‖z - 1‖ := norm_pos_iff.mpr hzne1
  have hs1 : (0 : ℝ) < z.re - 1 := by linarith
  set K : ℝ := ‖z - 1‖ * (‖z‖ / (z.re - 1) + 1) with hK
  have hK0 : (0 : ℝ) < K := by
    rw [hK]
    have : (0 : ℝ) < ‖z‖ / (z.re - 1) + 1 := by positivity
    positivity
  refine Metric.tendsto_nhds.mpr (fun ε hε => ?_)
  set δ : ℝ := ε / (4 * K) with hδdef
  have hδ : 0 < δ := by rw [hδdef]; positivity
  obtain ⟨Y, hY⟩ := Filter.eventually_atTop.mp (eventually_abs_primeTailError_le hδ)
  have hlogsmall : ∀ᶠ y : ℝ in atTop, ‖z‖ / ((z.re - 1) * Real.log y) ≤ ε / 4 := by
    have hlim : Tendsto (fun y : ℝ => ‖z‖ / ((z.re - 1) * Real.log y)) atTop (𝓝 0) :=
      Tendsto.div_atTop tendsto_const_nhds
        (Filter.Tendsto.const_mul_atTop hs1 Real.tendsto_log_atTop)
    exact hlim.eventually (eventually_le_nhds (by positivity))
  filter_upwards [eventually_gt_atTop (1 : ℝ), eventually_ge_atTop Y, hlogsmall]
    with y hy1 hyY hylog
  have hy0 : (0 : ℝ) < y := by linarith
  have hlogy : (0 : ℝ) < Real.log y := Real.log_pos hy1
  have hlogyc : (Real.log y : ℂ) ≠ 0 := by simpa using ne_of_gt hlogy
  have hyc : (y : ℂ) ≠ 0 := by simpa using ne_of_gt hy0
  have hypow : (y : ℂ) ^ (1 - z) ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl hyc)
  have hE : ∀ u : ℝ, y ≤ u → |primeTailError u| ≤ δ * (u / Real.log u) :=
    fun u hu => hY u (le_trans hyY hu)
  have hdec := primeTailSum_eq_main_add_remainder hz hy1
  have hratio : primeTailSum z y * ((z - 1) * (Real.log y : ℂ)) / (y : ℂ) ^ (1 - z) - 1
      = primeTailRemainder z y * ((z - 1) * (Real.log y : ℂ)) / (y : ℂ) ^ (1 - z) := by
    rw [hdec]
    field_simp
    ring
  have hnormpow : ‖(y : ℂ) ^ (1 - z)‖ = y ^ (1 - z.re) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hy0]
    congr 1
  have hRbound := norm_primeTailRemainder_le hz hy1 hδ.le hE
  have hpowpos : (0 : ℝ) < y ^ (1 - z.re) := Real.rpow_pos_of_pos hy0 _
  have hdistrw : ‖primeTailSum z y * ((z - 1) * (Real.log y : ℂ)) / (y : ℂ) ^ (1 - z) - 1‖
      = ‖primeTailRemainder z y‖ * (‖z - 1‖ * Real.log y) / y ^ (1 - z.re) := by
    rw [hratio, norm_div, norm_mul, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg hlogy.le, hnormpow]
  rw [Complex.dist_eq, hdistrw]
  have hfinal : ‖primeTailRemainder z y‖ * (‖z - 1‖ * Real.log y) / y ^ (1 - z.re)
      ≤ ‖z‖ / ((z.re - 1) * Real.log y) + K * δ := by
    rw [div_le_iff₀ hpowpos]
    have hexp : (‖z‖ / ‖z - 1‖ * (y ^ (1 - z.re) / ((z.re - 1) * (Real.log y) ^ 2))
        + ‖z‖ * (δ * y ^ (1 - z.re) / ((z.re - 1) * Real.log y))
        + δ * (y ^ (1 - z.re) / Real.log y)) * (‖z - 1‖ * Real.log y)
        = (‖z‖ / ((z.re - 1) * Real.log y) + K * δ) * y ^ (1 - z.re) := by
      rw [hK]
      field_simp
      ring
    calc ‖primeTailRemainder z y‖ * (‖z - 1‖ * Real.log y)
        ≤ (‖z‖ / ‖z - 1‖ * (y ^ (1 - z.re) / ((z.re - 1) * (Real.log y) ^ 2))
            + ‖z‖ * (δ * y ^ (1 - z.re) / ((z.re - 1) * Real.log y))
            + δ * (y ^ (1 - z.re) / Real.log y)) * (‖z - 1‖ * Real.log y) := by
          refine mul_le_mul_of_nonneg_right hRbound ?_
          positivity
      _ = (‖z‖ / ((z.re - 1) * Real.log y) + K * δ) * y ^ (1 - z.re) := hexp
  have hKδ : K * δ = ε / 4 := by
    rw [hδdef]
    field_simp
  refine lt_of_le_of_lt hfinal ?_
  rw [hKδ]
  linarith

/-! ## The co-Poisson current at the boundary -/

/-- On the unit interval the current is the strict prime tail cut at the ceiling of `1/x`. -/
theorem primeTailCurrent_eq_primeTailSum {z : ℂ} {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) :
    primeTailCurrent z x = (x : ℂ) ^ (-z) * primeTailSum z ((⌈x⁻¹⌉₊ : ℝ) - 1 / 2) := by
  rw [primeTailCurrent, primeTailSum, ← tsum_mul_left]
  refine tsum_congr (fun n => ?_)
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    simp
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hiff : ((n : ℝ)⁻¹ ≤ x) ↔ ((⌈x⁻¹⌉₊ : ℝ) - 1 / 2 < (n : ℝ)) := by
    constructor
    · intro h
      have hxn : x⁻¹ ≤ (n : ℝ) := by
        rw [inv_le_comm₀ hn0 hx] at h
        exact h
      have hceil : ⌈x⁻¹⌉₊ ≤ n := Nat.ceil_le.mpr hxn
      have : ((⌈x⁻¹⌉₊ : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hceil
      linarith
    · intro h
      have hceil : ⌈x⁻¹⌉₊ ≤ n := by
        by_contra hcon
        have : (n : ℝ) + 1 ≤ ((⌈x⁻¹⌉₊ : ℕ) : ℝ) := by
          exact_mod_cast Nat.succ_le_of_lt (Nat.lt_of_not_le hcon)
        linarith
      have hxn : x⁻¹ ≤ (n : ℝ) := le_trans (Nat.le_ceil _) (by exact_mod_cast hceil)
      rw [← inv_le_comm₀ hn0 hx] at hxn
      exact hxn
  have hseed : primeTailSeed n z x
      = if (n : ℝ)⁻¹ ≤ x then (n : ℂ) ^ (-z) * (x : ℂ) ^ (-z) else 0 := by
    rw [primeTailSeed]
    by_cases h : (n : ℝ)⁻¹ ≤ x
    · rw [if_pos h, Set.indicator_of_mem (by exact ⟨h, hx1⟩)]
    · rw [if_neg h, Set.indicator_of_notMem (by
        intro hmem
        exact h hmem.1)]
  rw [hseed]
  by_cases h : (n : ℝ)⁻¹ ≤ x
  · rw [if_pos h, if_pos (hiff.mp h)]
    ring
  · rw [if_neg h, if_neg (fun hc => h (hiff.mpr hc))]
    ring

/-- The half-integer cut just below the ceiling of `1/x`. -/
def ceilCut (x : ℝ) : ℝ := (⌈x⁻¹⌉₊ : ℝ) - 1 / 2

theorem ceilCut_bounds {x : ℝ} (hx : 0 < x) :
    x⁻¹ - 1 / 2 ≤ ceilCut x ∧ ceilCut x < x⁻¹ + 1 / 2 := by
  have h1 : x⁻¹ ≤ (⌈x⁻¹⌉₊ : ℝ) := Nat.le_ceil _
  have h2 : (⌈x⁻¹⌉₊ : ℝ) < x⁻¹ + 1 := Nat.ceil_lt_add_one (by positivity)
  constructor <;> · rw [ceilCut]; linarith

theorem one_lt_ceilCut {x : ℝ} (hx : 0 < x) (hx3 : x < 1 / 4) : 1 < ceilCut x := by
  have h1 : x⁻¹ - 1 / 2 ≤ ceilCut x := (ceilCut_bounds hx).1
  have h2 : (4 : ℝ) < x⁻¹ := by
    rw [lt_inv_comm₀ (by norm_num) hx]
    linarith
  linarith

theorem tendsto_mul_ceilCut : Tendsto (fun x : ℝ => x * ceilCut x) (𝓝[>] 0) (𝓝 1) := by
  have hsq : ∀ x : ℝ, 0 < x → ‖x * ceilCut x - 1‖ ≤ 3 / 2 * x := by
    intro x hx
    obtain ⟨h1, h2⟩ := ceilCut_bounds hx
    have hxinv : x * x⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt hx)
    have hlow : x * (x⁻¹ - 1 / 2) ≤ x * ceilCut x := mul_le_mul_of_nonneg_left h1 hx.le
    have hup : x * ceilCut x ≤ x * (x⁻¹ + 1 / 2) := mul_le_mul_of_nonneg_left h2.le hx.le
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> nlinarith [hxinv]
  have hmaj : Tendsto (fun x : ℝ => 3 / 2 * x) (𝓝[>] 0) (𝓝 0) := by
    have hcont : Continuous (fun x : ℝ => 3 / 2 * x) := continuous_const.mul continuous_id
    have hc : Tendsto (fun x : ℝ => 3 / 2 * x) (𝓝 0) (𝓝 0) := by
      simpa using hcont.tendsto (0 : ℝ)
    exact hc.mono_left nhdsWithin_le_nhds
  have hdiff : Tendsto (fun x : ℝ => x * ceilCut x - 1) (𝓝[>] 0) (𝓝 0) := by
    refine squeeze_zero_norm' ?_ hmaj
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact hsq x hx
  simpa using hdiff.add_const 1

theorem tendsto_ceilCut_atTop : Tendsto ceilCut (𝓝[>] 0) atTop := by
  have hbase : Tendsto (fun x : ℝ => x⁻¹ + -(1 / 2)) (𝓝[>] 0) atTop :=
    tendsto_atTop_add_const_right _ (-(1 / 2)) tendsto_inv_nhdsGT_zero
  refine tendsto_atTop_mono' _ ?_ hbase
  filter_upwards [self_mem_nhdsWithin] with x hx
  have := (ceilCut_bounds hx).1
  linarith

/-- The two logarithmic scales agree in the limit. -/
theorem tendsto_log_ceilCut_ratio :
    Tendsto (fun x : ℝ => Real.log x⁻¹ / Real.log (ceilCut x)) (𝓝[>] 0) (𝓝 1) := by
  have hprod : Tendsto (fun x : ℝ => Real.log (x * ceilCut x)) (𝓝[>] 0) (𝓝 0) := by
    have := (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp tendsto_mul_ceilCut
    simpa [Function.comp_def] using this
  have hinv : Tendsto (fun x : ℝ => Real.log x⁻¹) (𝓝[>] 0) atTop :=
    Real.tendsto_log_atTop.comp tendsto_inv_nhdsGT_zero
  have hratio : Tendsto (fun x : ℝ => Real.log (ceilCut x) / Real.log x⁻¹) (𝓝[>] 0) (𝓝 1) := by
    have hsplit : ∀ᶠ x : ℝ in 𝓝[>] 0,
        Real.log (ceilCut x) / Real.log x⁻¹
          = Real.log (x * ceilCut x) / Real.log x⁻¹ + 1 := by
      filter_upwards [self_mem_nhdsWithin, Ioo_mem_nhdsGT (by norm_num : (0:ℝ) < 1 / 4)]
        with x hx hx4
      have hx0 : (0 : ℝ) < x := hx
      have hy1 : 1 < ceilCut x := one_lt_ceilCut hx0 hx4.2
      have hlogx : Real.log x⁻¹ ≠ 0 := by
        have : (1 : ℝ) < x⁻¹ := by
          rw [one_lt_inv_iff₀]
          exact ⟨hx0, by linarith [hx4.2]⟩
        exact ne_of_gt (Real.log_pos this)
      have hlx : Real.log x ≠ 0 := by
        intro h
        rw [Real.log_inv, h] at hlogx
        exact hlogx neg_zero
      rw [Real.log_mul (ne_of_gt hx0) (by linarith), Real.log_inv]
      field_simp
      ring
    refine Tendsto.congr' (Filter.EventuallyEq.symm hsplit) ?_
    simpa using (Tendsto.div_atTop hprod hinv).add_const 1
  have hne : (1 : ℝ) ≠ 0 := by norm_num
  have hinv2 : Tendsto (fun x : ℝ => (Real.log (ceilCut x) / Real.log x⁻¹)⁻¹) (𝓝[>] 0) (𝓝 1) := by
    simpa using hratio.inv₀ hne
  refine Tendsto.congr' ?_ hinv2
  filter_upwards [self_mem_nhdsWithin, Ioo_mem_nhdsGT (by norm_num : (0:ℝ) < 1 / 4)]
    with x hx hx4
  have hx0 : (0 : ℝ) < x := hx
  have hy1 : 1 < ceilCut x := one_lt_ceilCut hx0 hx4.2
  have hlogy : Real.log (ceilCut x) ≠ 0 := ne_of_gt (Real.log_pos hy1)
  have hlogx : Real.log x⁻¹ ≠ 0 := by
    have : (1 : ℝ) < x⁻¹ := by
      rw [one_lt_inv_iff₀]
      exact ⟨hx0, by linarith [hx4.2]⟩
    exact ne_of_gt (Real.log_pos this)
  field_simp

/-- **Card equation (16).**  The boundary law of the prime-tail co-Poisson current:
`G_z(x) ∼ 1 / ((z-1) x log(1/x))` as `x ↓ 0`. -/
theorem tendsto_primeTailCurrent_boundary {z : ℂ} (hz : 1 < z.re) :
    Tendsto (fun x : ℝ => primeTailCurrent z x * ((z - 1) * (x : ℂ) * (Real.log x⁻¹ : ℂ)))
      (𝓝[>] 0) (𝓝 1) := by
  have hPhi : Tendsto (fun x : ℝ => primeTailSum z (ceilCut x)
      * ((z - 1) * (Real.log (ceilCut x) : ℂ)) / (ceilCut x : ℂ) ^ (1 - z)) (𝓝[>] 0) (𝓝 1) := by
    simpa [Function.comp_def] using (tendsto_primeTailSum_div hz).comp tendsto_ceilCut_atTop
  have hcont : ContinuousAt (fun t : ℝ => (t : ℂ) ^ (1 - z)) 1 :=
    (hasDerivAt_ofReal_cpow (1 - z) (by norm_num : (0:ℝ) < 1)).continuousAt
  have hP : Tendsto (fun x : ℝ => (((x * ceilCut x : ℝ)) : ℂ) ^ (1 - z)) (𝓝[>] 0) (𝓝 1) := by
    have := hcont.tendsto.comp tendsto_mul_ceilCut
    simpa [Function.comp_def] using this
  have hL : Tendsto (fun x : ℝ => ((Real.log x⁻¹ / Real.log (ceilCut x) : ℝ) : ℂ))
      (𝓝[>] 0) (𝓝 1) := by
    have := Complex.continuous_ofReal.continuousAt.tendsto.comp tendsto_log_ceilCut_ratio
    simpa [Function.comp_def] using this
  have hlim := (hPhi.mul hP).mul hL
  rw [mul_one, mul_one] at hlim
  refine Tendsto.congr' ?_ hlim
  filter_upwards [self_mem_nhdsWithin, Ioo_mem_nhdsGT (by norm_num : (0:ℝ) < 1 / 4)]
    with x hx hx4
  have hx0 : (0 : ℝ) < x := hx
  have hx1 : x ≤ 1 := by linarith [hx4.2]
  have hy1 : 1 < ceilCut x := one_lt_ceilCut hx0 hx4.2
  have hy0 : (0 : ℝ) < ceilCut x := by linarith
  have hlogy : (0 : ℝ) < Real.log (ceilCut x) := Real.log_pos hy1
  have hlogyc : (Real.log (ceilCut x) : ℂ) ≠ 0 := by simpa using ne_of_gt hlogy
  have hxc : (x : ℂ) ≠ 0 := by simpa using ne_of_gt hx0
  have hyc : ((ceilCut x : ℝ) : ℂ) ≠ 0 := by simpa using ne_of_gt hy0
  have hypow : ((ceilCut x : ℝ) : ℂ) ^ (1 - z) ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl hyc)
  have hsplit : (((x * ceilCut x : ℝ)) : ℂ) ^ (1 - z)
      = (x : ℂ) ^ (1 - z) * ((ceilCut x : ℝ) : ℂ) ^ (1 - z) := by
    rw [Complex.ofReal_mul]
    exact Complex.mul_cpow_ofReal_nonneg hx0.le hy0.le _
  have hxpow : (x : ℂ) ^ (-z) * (x : ℂ) = (x : ℂ) ^ (1 - z) := by
    rw [show (1 : ℂ) - z = -z + 1 by ring, Complex.cpow_add _ _ hxc]
    simp
  rw [primeTailCurrent_eq_primeTailSum hx0 hx1,
    show ((⌈x⁻¹⌉₊ : ℕ) : ℝ) - 1 / 2 = ceilCut x from rfl, hsplit, Complex.ofReal_div, ← hxpow]
  field_simp

end

end RHTower
