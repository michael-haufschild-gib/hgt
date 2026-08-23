import GaloisForLFunctions.RHTower.PrimeTailHalfWeightWall

/-!
# The continuous prime vacuum of the co-Poisson current

The leading boundary singularity of the prime-tail current is supplied by the continuous
logarithmic density `1/log t`, not by the primes themselves.  Its interval suspension is the
vacuum current, and the vacuum obeys the same Abel transform as the arithmetic tail: both are
`z` times the Mellin-type integral of the window increment of their counting function.

The Abel identity for the continuous density is proved by differentiation rather than by Fubini:
both sides have derivative `-y^{-z}/log y` in the cut and vanish at infinity.
-/

namespace RHTower

open MeasureTheory Set Filter Topology

noncomputable section

/-! ## Riemann's logarithmic integral -/

/-- **Card equation (20a).**  The continuous logarithmic counting function. -/
def logIntegralCount (X : ℝ) : ℝ := ∫ t in (Real.exp 1)..X, (Real.log t)⁻¹

theorem continuousAt_inv_log {t : ℝ} (ht : 1 < t) :
    ContinuousAt (fun s : ℝ => (Real.log s)⁻¹) t := by
  have h0 : (0 : ℝ) < t := by linarith
  have hlog : Real.log t ≠ 0 := ne_of_gt (Real.log_pos ht)
  exact (Real.continuousAt_log (ne_of_gt h0)).inv₀ hlog

theorem intervalIntegrable_inv_log {a b : ℝ} (ha : 1 < a) (hb : 1 < b) :
    IntervalIntegrable (fun t : ℝ => (Real.log t)⁻¹) volume a b := by
  refine ContinuousOn.intervalIntegrable ?_
  intro t ht
  rw [Set.uIcc_eq_union] at ht
  have ht1 : 1 < t := by
    rcases ht with h | h
    · exact lt_of_lt_of_le ha h.1
    · exact lt_of_lt_of_le hb h.1
  exact (continuousAt_inv_log ht1).continuousWithinAt

theorem hasDerivAt_logIntegralCount {X : ℝ} (hX : 1 < X) :
    HasDerivAt logIntegralCount (Real.log X)⁻¹ X := by
  have he : (1 : ℝ) < Real.exp 1 := by
    have := Real.add_one_le_exp (1 : ℝ)
    linarith
  refine intervalIntegral.integral_hasDerivAt_right (intervalIntegrable_inv_log he hX) ?_
    (continuousAt_inv_log hX)
  refine ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioi ?_ X hX
  intro t ht
  exact (continuousAt_inv_log ht).continuousWithinAt

/-! ## Differentiating a tail integral in its cut -/

theorem integral_Ioi_eq_sub {f : ℝ → ℂ} {c u : ℝ} (hcu : c ≤ u)
    (hint : IntegrableOn f (Ioi c) volume) :
    (∫ t in Ioi u, f t) = (∫ t in Ioi c, f t) - ∫ t in c..u, f t := by
  have hsplit : Ioi c = Ioc c u ∪ Ioi u := by
    ext t
    constructor
    · intro ht
      rcases le_or_gt t u with h | h
      · exact Or.inl ⟨ht, h⟩
      · exact Or.inr h
    · rintro (⟨h1, _⟩ | h)
      · exact h1
      · exact lt_of_le_of_lt hcu h
  have hdisj : Disjoint (Ioc c u) (Ioi u) := by
    rw [Set.disjoint_left]
    rintro t ⟨_, ht2⟩ ht3
    exact absurd ht3 (not_lt.mpr ht2)
  have hunion : (∫ t in Ioi c, f t) = (∫ t in Ioc c u, f t) + ∫ t in Ioi u, f t := by
    rw [hsplit]
    exact MeasureTheory.setIntegral_union hdisj measurableSet_Ioi
      (hint.mono_set (by rw [hsplit]; exact Set.subset_union_left))
      (hint.mono_set (by rw [hsplit]; exact Set.subset_union_right))
  rw [intervalIntegral.integral_of_le hcu, hunion]
  ring

theorem hasDerivAt_integral_Ioi {f : ℝ → ℂ} {c y : ℝ} (hcy : c < y)
    (hint : IntegrableOn f (Ioi c) volume)
    (hmeas : StronglyMeasurableAtFilter f (𝓝 y) volume)
    (hcont : ContinuousAt f y) :
    HasDerivAt (fun u : ℝ => ∫ t in Ioi u, f t) (-f y) y := by
  have hII : IntervalIntegrable f volume c y :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hcy.le).mpr
      (hint.mono_set Ioc_subset_Ioi_self)
  have hd : HasDerivAt (fun u : ℝ => (∫ t in Ioi c, f t) - ∫ t in c..u, f t) (-f y) y := by
    have hbase := intervalIntegral.integral_hasDerivAt_right hII hmeas hcont
    simpa using hbase.const_sub (∫ t in Ioi c, f t)
  refine hd.congr_of_eventuallyEq ?_
  filter_upwards [Ioi_mem_nhds hcy] with u hu
  exact integral_Ioi_eq_sub (le_of_lt hu) hint

/-! ## The vacuum current -/

theorem one_lt_exp_one : (1 : ℝ) < Real.exp 1 := by
  have := Real.add_one_le_exp (1 : ℝ)
  linarith

theorem logIntegralCount_nonneg {v : ℝ} (hv : Real.exp 1 ≤ v) : 0 ≤ logIntegralCount v := by
  refine intervalIntegral.integral_nonneg hv (fun t ht => ?_)
  have ht1 : (1 : ℝ) < t := lt_of_lt_of_le one_lt_exp_one ht.1
  exact le_of_lt (inv_pos.mpr (Real.log_pos ht1))

theorem logIntegralCount_le {v : ℝ} (hv : Real.exp 1 ≤ v) : logIntegralCount v ≤ v := by
  have hle : logIntegralCount v ≤ ∫ _t in (Real.exp 1)..v, (1 : ℝ) := by
    refine intervalIntegral.integral_mono_on hv
      (intervalIntegrable_inv_log one_lt_exp_one (lt_of_lt_of_le one_lt_exp_one hv))
      intervalIntegrable_const (fun t ht => ?_)
    have ht1 : (1 : ℝ) ≤ Real.log t := by
      have : Real.log (Real.exp 1) ≤ Real.log t :=
        Real.log_le_log (Real.exp_pos 1) ht.1
      simpa using this
    have hpos : (0 : ℝ) < Real.log t := by linarith
    rw [inv_le_one₀ hpos]
    exact ht1
  have hconst : (∫ _t in (Real.exp 1)..v, (1 : ℝ)) = v - Real.exp 1 := by simp
  have hepos : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  linarith [hle, hconst ▸ hle]

theorem continuousOn_logIntegralCount : ContinuousOn logIntegralCount (Ioi 1) := by
  intro y hy
  exact ((hasDerivAt_logIntegralCount hy).continuousAt).continuousWithinAt

/-- The tail of the continuous logarithmic density. -/
def primeVacuumTail (z : ℂ) (y : ℝ) : ℂ := ∫ t in Ioi y, logPowerTail z 1 t

/-- **Card equation (20c).**  The vacuum constant `V(z)`. -/
def primeVacuumValue (z : ℂ) : ℂ := primeVacuumTail z (Real.exp 1)

/-- **Card equation (20b).**  The interval suspension of the continuous vacuum. -/
def primeVacuumCurrent (z : ℂ) (x : ℝ) : ℂ :=
  (x : ℂ) ^ (-z) * primeVacuumTail z (max (Real.exp 1) x⁻¹)

/-- The Abel integrand of the continuous vacuum. -/
def vacuumAbelIntegrand (z : ℂ) (v : ℝ) : ℂ := (v : ℂ) ^ (-z - 1) * (logIntegralCount v : ℂ)

theorem integrableOn_vacuumAbelIntegrand {z : ℂ} (hz : 1 < z.re) {y : ℝ}
    (hy : Real.exp 1 ≤ y) : IntegrableOn (vacuumAbelIntegrand z) (Ioi y) volume := by
  have hy0 : (0 : ℝ) < y := lt_of_lt_of_le (by linarith [one_lt_exp_one]) hy
  have hmajor : IntegrableOn (fun v : ℝ => v ^ (-z.re)) (Ioi y) volume :=
    integrableOn_Ioi_rpow_of_lt (by linarith) hy0
  refine Integrable.mono' hmajor ?_ ?_
  · refine AEStronglyMeasurable.mul
      ((measurable_ofReal_cpow (-z - 1)).aestronglyMeasurable.restrict) ?_
    refine (Complex.continuous_ofReal.comp_continuousOn
      (continuousOn_logIntegralCount.mono ?_)).aestronglyMeasurable measurableSet_Ioi
    exact fun t ht => lt_of_lt_of_le one_lt_exp_one (le_trans hy (le_of_lt ht))
  · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with v hv
    have hv0 : (0 : ℝ) < v := lt_trans hy0 hv
    have hvy : Real.exp 1 ≤ v := le_trans hy hv.le
    rw [vacuumAbelIntegrand, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hv0,
      Complex.norm_real, Real.norm_of_nonneg (logIntegralCount_nonneg hvy)]
    have hpow : v ^ (-z - 1).re = v ^ (-z.re) * v⁻¹ := by
      rw [← Real.rpow_neg_one v, ← Real.rpow_add hv0]
      congr 1
    rw [hpow, mul_assoc]
    have hsmall : v⁻¹ * logIntegralCount v ≤ 1 := by
      rw [inv_mul_eq_div, div_le_one hv0]
      exact logIntegralCount_le hvy
    calc v ^ (-z.re) * (v⁻¹ * logIntegralCount v)
        ≤ v ^ (-z.re) * 1 :=
          mul_le_mul_of_nonneg_left hsmall (Real.rpow_pos_of_pos hv0 _).le
      _ = v ^ (-z.re) := by ring

/-! ## The Abel transform of the vacuum -/

theorem continuousAt_logPowerTail {z : ℂ} {y : ℝ} (hy : 1 < y) :
    ContinuousAt (logPowerTail z 1) y := by
  have hy0 : (0 : ℝ) < y := by linarith
  have hlog : Real.log y ≠ 0 := ne_of_gt (Real.log_pos hy)
  have h1 : ContinuousAt (fun t : ℝ => (t : ℂ) ^ (-z)) y :=
    (hasDerivAt_ofReal_cpow (-z) hy0).continuousAt
  have h2 : ContinuousAt (fun t : ℝ => ((Real.log t : ℝ) : ℂ) ^ (1 : ℕ)) y := by
    refine ContinuousAt.pow ?_ 1
    exact Complex.continuous_ofReal.continuousAt.comp (Real.continuousAt_log (ne_of_gt hy0))
  have hne : ((Real.log y : ℝ) : ℂ) ^ (1 : ℕ) ≠ 0 := by
    simpa using (by simpa using hlog : ((Real.log y : ℝ) : ℂ) ≠ 0)
  exact h1.div h2 hne

theorem continuousAt_vacuumAbelIntegrand {z : ℂ} {y : ℝ} (hy : 1 < y) :
    ContinuousAt (vacuumAbelIntegrand z) y := by
  have hy0 : (0 : ℝ) < y := by linarith
  refine ContinuousAt.mul ((hasDerivAt_ofReal_cpow (-z - 1) hy0).continuousAt) ?_
  exact Complex.continuous_ofReal.continuousAt.comp
    ((continuousOn_logIntegralCount.continuousAt (Ioi_mem_nhds hy)))

theorem stronglyMeasurableAtFilter_logPowerTail {z : ℂ} {y : ℝ} (hy : 1 < y) :
    StronglyMeasurableAtFilter (logPowerTail z 1) (𝓝 y) volume := by
  refine ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioi ?_ y hy
  intro t ht
  exact (continuousAt_logPowerTail ht).continuousWithinAt

theorem stronglyMeasurableAtFilter_vacuumAbelIntegrand {z : ℂ} {y : ℝ} (hy : 1 < y) :
    StronglyMeasurableAtFilter (vacuumAbelIntegrand z) (𝓝 y) volume := by
  refine ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioi ?_ y hy
  intro t ht
  exact (continuousAt_vacuumAbelIntegrand ht).continuousWithinAt

/-- The right-hand side of the vacuum Abel transform. -/
def vacuumAbelRHS (z : ℂ) (y : ℝ) : ℂ :=
  z * (∫ v in Ioi y, vacuumAbelIntegrand z v) - (logIntegralCount y : ℂ) * (y : ℂ) ^ (-z)

theorem hasDerivAt_primeVacuumTail {z : ℂ} (hz : 1 < z.re) {y : ℝ} (hy : Real.exp 1 < y) :
    HasDerivAt (primeVacuumTail z) (-logPowerTail z 1 y) y := by
  have hy1 : (1 : ℝ) < y := lt_trans one_lt_exp_one hy
  exact hasDerivAt_integral_Ioi hy (integrableOn_logPowerTail one_lt_exp_one hz)
    (stronglyMeasurableAtFilter_logPowerTail hy1) (continuousAt_logPowerTail hy1)

theorem hasDerivAt_vacuumAbelRHS {z : ℂ} (hz : 1 < z.re) {y : ℝ} (hy : Real.exp 1 < y) :
    HasDerivAt (vacuumAbelRHS z) (-logPowerTail z 1 y) y := by
  have hy1 : (1 : ℝ) < y := lt_trans one_lt_exp_one hy
  have hy0 : (0 : ℝ) < y := by linarith
  have hlog : Real.log y ≠ 0 := ne_of_gt (Real.log_pos hy1)
  have hd1 : HasDerivAt (fun u : ℝ => ∫ v in Ioi u, vacuumAbelIntegrand z v)
      (-vacuumAbelIntegrand z y) y :=
    hasDerivAt_integral_Ioi hy (integrableOn_vacuumAbelIntegrand hz le_rfl)
      (stronglyMeasurableAtFilter_vacuumAbelIntegrand hy1)
      (continuousAt_vacuumAbelIntegrand hy1)
  have hd2 : HasDerivAt (fun u : ℝ => ((logIntegralCount u : ℝ) : ℂ)) (((Real.log y)⁻¹ : ℝ) : ℂ) y :=
    (hasDerivAt_logIntegralCount hy1).ofReal_comp
  have hd3 : HasDerivAt (fun u : ℝ => (u : ℂ) ^ (-z)) (-z * (y : ℂ) ^ (-z - 1)) y := by
    have := hasDerivAt_ofReal_cpow (-z) hy0
    rwa [show (-z : ℂ) - 1 = -z - 1 from rfl] at this
  have hfull := (hd1.const_mul z).sub (hd2.mul hd3)
  refine hfull.congr_deriv ?_
  rw [vacuumAbelIntegrand, logPowerTail, pow_one, Complex.ofReal_inv]
  have hlogc : ((Real.log y : ℝ) : ℂ) ≠ 0 := by simpa using hlog
  field_simp
  ring

end

end RHTower
