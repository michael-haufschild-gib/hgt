import GaloisForLFunctions.RHTower.BurnolPrimeTailVacuumHalfLaplaceWall
import GaloisForLFunctions.RHTower.BurnolPrimeTailFoldedMultiRatePort
import GaloisForLFunctions.RHTower.PrimeVacuumMellin
import GaloisForLFunctions.RHTower.SuzukiStieltjesMoments

/-!
# Literal tail ports for the vacuum-subtracted prime current

The prime-vacuum subtraction gives a measurable source and a full integrable
logarithmic port for every folded Laplace rate at least `1 / 2`. This creates
literal arithmetic functionals for the two-rate HJ receiver without using
zero data. The file deliberately stops before a source-to-mode identity: that
identity is the remaining substantive HJ transport problem.
-/

open Complex MeasureTheory Set Filter Topology

noncomputable section

namespace RHTower

private theorem continuousOn_primeVacuumCurrent_small {z : ℂ} (hz : 1 < z.re) :
    ContinuousOn (primeVacuumCurrent z) (Ioo 0 (Real.exp (-1))) := by
  have hprod : ContinuousOn
      (fun x : ℝ => (x : ℂ) ^ (-z) * primeVacuumTail z x⁻¹)
      (Ioo 0 (Real.exp (-1))) := by
    intro x hx
    have hxp : ContinuousAt (fun y : ℝ => (y : ℂ) ^ (-z)) x :=
      Complex.continuousAt_ofReal_cpow_const x (-z) (Or.inr (ne_of_gt hx.1))
    have hx1 : x < 1 := by
      refine lt_of_lt_of_le hx.2 ?_
      exact Real.exp_le_one_iff.mpr (by norm_num)
    have htail : ContinuousAt (fun y : ℝ => primeVacuumTail z y⁻¹) x :=
      (hasDerivAt_primeVacuumTail_inv hz hx.1 hx1).continuousAt
    exact (hxp.mul htail).continuousWithinAt
  refine hprod.congr (fun x hx => ?_)
  apply primeVacuumCurrent_eq_tail hx.1
  simpa [Real.exp_neg] using hx.2.le

private theorem continuousOn_primeVacuumCurrent_exp_tail {z : ℂ} (hz : 1 < z.re) :
    ContinuousOn (fun L : ℝ => primeVacuumCurrent z (Real.exp (-L))) (Ioi 1) := by
  apply (continuousOn_primeVacuumCurrent_small hz).comp
  · exact (Real.continuous_exp.comp continuous_neg).continuousOn
  · intro L hL
    change 1 < L at hL
    constructor
    · exact Real.exp_pos _
    · exact Real.exp_lt_exp.mpr (by linarith)

private theorem aestronglyMeasurable_primeTailCurrent_exp_tail (z : ℂ) :
    AEStronglyMeasurable (fun L : ℝ => primeTailCurrent z (Real.exp (-L)))
      (volume.restrict (Ioi 1)) := by
  refine ((measurable_primeTailStep z).comp
    (Real.continuous_exp.comp continuous_neg).measurable).aestronglyMeasurable.restrict.congr ?_
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with L hL
  change 1 < L at hL
  apply (primeTailCurrent_eq_primeTailSum (Real.exp_pos _) ?_).symm
  have hneg : -L ≤ 0 := by linarith
  exact (Real.exp_le_one_iff).mpr hneg

/-- The log-half-density of the canonical prime-vacuum remainder is strongly
measurable on the literal logarithmic tail. -/
theorem aestronglyMeasurable_logHalfDensity_primeRemainderCurrent_exp_tail
    {z : ℂ} (hz : 1 < z.re) :
    AEStronglyMeasurable (fun L : ℝ => logHalfDensity (primeRemainderCurrent z) L)
      (volume.restrict (Ioi 1)) := by
  have hprime := aestronglyMeasurable_primeTailCurrent_exp_tail z
  have hvac : AEStronglyMeasurable
      (fun L : ℝ => primeVacuumCurrent z (Real.exp (-L)))
      (volume.restrict (Ioi 1)) :=
    (continuousOn_primeVacuumCurrent_exp_tail hz).aestronglyMeasurable measurableSet_Ioi
  have hrem : AEStronglyMeasurable
      (fun L : ℝ => primeRemainderCurrent z (Real.exp (-L)))
      (volume.restrict (Ioi 1)) := by
    refine (hprime.sub hvac).congr ?_
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with L hL
    rfl
  have hhalf : AEStronglyMeasurable (fun L : ℝ => (Real.exp (-L / 2) : ℂ))
      (volume.restrict (Ioi 1)) := by
    exact ((Complex.continuous_ofReal.comp
      (Real.continuous_exp.comp (continuous_neg.div_const 2))).aestronglyMeasurable).restrict
  refine (hhalf.mul hrem).congr ?_
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with L hL
  rfl

/-- Every folded Laplace rate `a ≥ 1 / 2` admits a literal integrable tail
port of the vacuum-subtracted prime source. -/
theorem exists_integrableOn_routeRFoldedLaplaceIntegrandAt_logHalfDensity_primeRemainderCurrent_tail
    {z : ℂ} (hz : 1 < z.re) {a : ℝ} (ha : 1 / 2 ≤ a) :
    ∃ T : ℝ, 1 ≤ T ∧ IntegrableOn
      (routeRFoldedLaplaceIntegrandAt a (logHalfDensity (primeRemainderCurrent z)))
      (Ioi T) := by
  obtain ⟨K, c, hc, hK, hbound⟩ :=
    exists_norm_routeRFoldedHalfLaplaceIntegrand_logHalfDensity_primeRemainderCurrent_bound hz
  obtain ⟨T₀, hT₀⟩ := eventually_atTop.1 hbound
  refine ⟨max 1 T₀, le_max_left _ _, ?_⟩
  have hTpos : 0 < max 1 T₀ := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hmajor : IntegrableOn (fun L : ℝ => K * Real.exp (-(c * Real.sqrt L)))
      (Ioi (max 1 T₀)) := by
    change Integrable (fun L : ℝ => K * Real.exp (-(c * Real.sqrt L)))
      (volume.restrict (Ioi (max 1 T₀)))
    simpa using ((integrableOn_pow_mul_exp_neg_sqrt 0 hc).mono_set
      (Ioi_subset_Ioi hTpos.le)).const_mul K
  have hlog : AEStronglyMeasurable
      (logHalfDensity (primeRemainderCurrent z))
      (volume.restrict (Ioi (max 1 T₀))) :=
    (aestronglyMeasurable_logHalfDensity_primeRemainderCurrent_exp_tail hz).mono_measure
      (Measure.restrict_mono (Ioi_subset_Ioi (le_max_left _ _)) le_rfl)
  have hweight : AEStronglyMeasurable
      (fun L : ℝ => Complex.exp (-((a : ℂ) * (L : ℂ))))
      (volume.restrict (Ioi (max 1 T₀))) := by
    exact ((by fun_prop : Continuous fun L : ℝ => Complex.exp (-((a : ℂ) * (L : ℂ)))
      ).aestronglyMeasurable).restrict
  refine Integrable.mono' hmajor (hweight.mul hlog) ?_
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with L hL
  have hLpos : 0 < L := lt_of_lt_of_le hTpos (le_of_lt hL)
  have henv := hT₀ L (le_trans (le_max_right _ _) hL.le)
  rw [routeRFoldedHalfLaplaceIntegrand, norm_mul, Complex.norm_exp] at henv
  have hhalfReal : (-((1 / 2 : ℂ) * (L : ℂ))).re = -L / 2 := by
    norm_num
    ring
  rw [hhalfReal] at henv
  have hdecay : K * Real.exp (-c * Real.sqrt L) =
      K * Real.exp (-(c * Real.sqrt L)) := by
    congr 2
    ring
  rw [hdecay] at henv
  rw [routeRFoldedLaplaceIntegrandAt, norm_mul, Complex.norm_exp]
  have hrateReal : (-((a : ℂ) * (L : ℂ))).re = -a * L := by
    norm_num
  rw [hrateReal]
  have hrate : Real.exp (-a * L) ≤ Real.exp (-L / 2) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  have hmul : Real.exp (-a * L) * ‖logHalfDensity (primeRemainderCurrent z) L‖ ≤
      Real.exp (-L / 2) * ‖logHalfDensity (primeRemainderCurrent z) L‖ :=
    mul_le_mul_of_nonneg_right hrate (norm_nonneg _)
  exact hmul.trans henv

private theorem continuousOn_primeVacuumCurrent_exp_Icc {z : ℂ} (hz : 1 < z.re)
    (T : ℝ) :
    ContinuousOn (fun L : ℝ => primeVacuumCurrent z (Real.exp (-L))) (Icc 1 T) := by
  have hprod : ContinuousOn
      (fun x : ℝ => (x : ℂ) ^ (-z) * primeVacuumTail z x⁻¹)
      (Icc (Real.exp (-T)) (Real.exp (-1))) := by
    intro x hx
    have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos _) hx.1
    have hx1 : x < 1 :=
      lt_of_le_of_lt hx.2 (Real.exp_lt_one_iff.mpr (by norm_num))
    have hxp : ContinuousAt (fun y : ℝ => (y : ℂ) ^ (-z)) x :=
      Complex.continuousAt_ofReal_cpow_const x (-z) (Or.inr (ne_of_gt hx0))
    have htail : ContinuousAt (fun y : ℝ => primeVacuumTail z y⁻¹) x :=
      (hasDerivAt_primeVacuumTail_inv hz hx0 hx1).continuousAt
    exact (hxp.mul htail).continuousWithinAt
  have hcur : ContinuousOn (primeVacuumCurrent z)
      (Icc (Real.exp (-T)) (Real.exp (-1))) := by
    refine hprod.congr ?_
    intro x hx
    apply primeVacuumCurrent_eq_tail (lt_of_lt_of_le (Real.exp_pos _) hx.1)
    simpa [Real.exp_neg] using hx.2
  refine hcur.comp (Real.continuous_exp.comp continuous_neg).continuousOn ?_
  intro L hL
  change 1 ≤ L ∧ L ≤ T at hL
  constructor <;> apply Real.exp_le_exp.mpr <;> linarith

private theorem integrableOn_routeRFoldedLaplaceIntegrandAt_logHalfDensity_primeTailCurrent_head
    {z : ℂ} (hz : 1 < z.re) {a T : ℝ} (ha : 1 / 2 ≤ a) :
    IntegrableOn
      (routeRFoldedLaplaceIntegrandAt a (logHalfDensity (primeTailCurrent z)))
      (Ioc 0 T) := by
  let step : ℝ → ℂ := fun L =>
    (Real.exp (-L) : ℂ) ^ (-z) *
      primeTailSum z ((⌈(Real.exp (-L))⁻¹⌉₊ : ℝ) - 1 / 2)
  let g : ℝ → ℂ := fun L =>
    Complex.exp (-((a : ℂ) * (L : ℂ))) * ((Real.exp (-L / 2) : ℂ) * step L)
  have hstep : AEStronglyMeasurable step volume := by
    exact ((measurable_primeTailStep z).comp
      (Real.continuous_exp.comp continuous_neg).measurable).aestronglyMeasurable
  have hweight : AEStronglyMeasurable
      (fun L : ℝ => Complex.exp (-((a : ℂ) * (L : ℂ)))) volume := by
    exact ((by fun_prop : Continuous fun L : ℝ => Complex.exp (-((a : ℂ) * (L : ℂ)))
      ).aestronglyMeasurable)
  have hhalf : AEStronglyMeasurable (fun L : ℝ => (Real.exp (-L / 2) : ℂ)) volume := by
    exact (Complex.continuous_ofReal.comp
      (Real.continuous_exp.comp (continuous_neg.div_const 2))).aestronglyMeasurable
  have hgmeas : AEStronglyMeasurable g volume := by
    exact (hweight.mul (hhalf.mul hstep)).congr (by
      filter_upwards with L
      rfl)
  have hGint : IntegrableOn g (Ioc 0 T) := by
    refine Measure.integrableOn_of_bounded
      (M := Real.exp (T * z.re) * primeTailBound z.re) ?_ hgmeas ?_
    · rw [Real.volume_Ioc]
      exact ENNReal.ofReal_ne_top
    · filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with L hL
      have hL0 : 0 ≤ L := hL.1.le
      have ha0 : 0 ≤ a := by linarith
      have hx0 : 0 < Real.exp (-L) := Real.exp_pos _
      have hx1 : Real.exp (-L) ≤ 1 := (Real.exp_le_one_iff).mpr (by linarith)
      have hstepEq : step L = primeTailCurrent z (Real.exp (-L)) := by
        dsimp only [step]
        exact (primeTailCurrent_eq_primeTailSum hx0 hx1).symm
      have hcurrent := norm_primeTailCurrent_le hz hx0 hx1
      have hpow : (Real.exp (-L)) ^ (-z.re) = Real.exp (L * z.re) := by
        rw [exp_rpow]
        congr 1
        ring
      rw [hpow] at hcurrent
      have hTbound : Real.exp (L * z.re) ≤ Real.exp (T * z.re) := by
        apply Real.exp_le_exp.mpr
        exact mul_le_mul_of_nonneg_right hL.2 (by linarith [hz])
      have hcurrentBound : ‖primeTailCurrent z (Real.exp (-L))‖ ≤
          Real.exp (T * z.re) * primeTailBound z.re := by
        exact hcurrent.trans (mul_le_mul_of_nonneg_right hTbound
          (primeTailBound_nonneg z.re))
      have hA : Real.exp (-a * L) ≤ 1 :=
        Real.exp_le_one_iff.mpr (by nlinarith)
      have hH : Real.exp (-L / 2) ≤ 1 :=
        Real.exp_le_one_iff.mpr (by nlinarith)
      have hweights : Real.exp (-a * L) * Real.exp (-L / 2) ≤ 1 := by
        calc
          Real.exp (-a * L) * Real.exp (-L / 2) ≤ 1 * 1 :=
            mul_le_mul hA hH (Real.exp_pos _).le (by norm_num)
          _ = 1 := by ring
      dsimp only [g]
      rw [norm_mul, norm_mul, Complex.norm_exp]
      have hAre : (-((a : ℂ) * (L : ℂ))).re = -a * L := by norm_num
      rw [hAre, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le, hstepEq]
      calc
        Real.exp (-a * L) * (Real.exp (-L / 2) *
            ‖primeTailCurrent z (Real.exp (-L))‖) =
          (Real.exp (-a * L) * Real.exp (-L / 2)) *
            ‖primeTailCurrent z (Real.exp (-L))‖ := by ring
        _ ≤
          1 * ‖primeTailCurrent z (Real.exp (-L))‖ :=
            mul_le_mul_of_nonneg_right hweights (norm_nonneg _)
        _ = ‖primeTailCurrent z (Real.exp (-L))‖ := by ring
        _ ≤ Real.exp (T * z.re) * primeTailBound z.re := hcurrentBound
  refine hGint.congr_fun ?_ measurableSet_Ioc
  intro L hL
  have hL0 : 0 < L := hL.1
  have hx0 : 0 < Real.exp (-L) := Real.exp_pos _
  have hx1 : Real.exp (-L) ≤ 1 := (Real.exp_le_one_iff).mpr (by linarith)
  dsimp only [g]
  dsimp only [step]
  rw [routeRFoldedLaplaceIntegrandAt, logHalfDensity,
    primeTailCurrent_eq_primeTailSum hx0 hx1]

private theorem continuous_routeRFoldedLaplaceIntegrandAt_logHalfDensity_primeVacuumCurrent_lower
    (z : ℂ) (a : ℝ) :
    ContinuousOn
      (routeRFoldedLaplaceIntegrandAt a (logHalfDensity (primeVacuumCurrent z)))
      (Icc 0 1) := by
  have hpow : Continuous (fun L : ℝ => (Real.exp (-L) : ℂ) ^ (-z)) := by
    rw [continuous_iff_continuousAt]
    intro L
    have hexp : ContinuousAt (fun y : ℝ => (Real.exp y : ℂ) ^ (-z)) (-L) :=
      (Complex.continuousAt_ofReal_cpow_const (Real.exp (-L)) (-z)
        (Or.inr (ne_of_gt (Real.exp_pos _)))).comp
        (show ContinuousAt Real.exp (-L) from Real.continuous_exp.continuousAt)
    exact hexp.comp (show ContinuousAt (fun y : ℝ => -y) L from continuous_neg.continuousAt)
  have hweight : Continuous (fun L : ℝ => Complex.exp (-((a : ℂ) * (L : ℂ)))) := by
    fun_prop
  have hhalf : Continuous (fun L : ℝ => (Real.exp (-L / 2) : ℂ)) := by
    exact Complex.continuous_ofReal.comp
      (Real.continuous_exp.comp (continuous_neg.div_const 2))
  have hbase : Continuous (fun L : ℝ =>
      Complex.exp (-((a : ℂ) * (L : ℂ))) *
        ((Real.exp (-L / 2) : ℂ) * ((Real.exp (-L) : ℂ) ^ (-z) * primeVacuumValue z))) :=
    hweight.mul (hhalf.mul (hpow.mul continuous_const))
  refine hbase.continuousOn.congr ?_
  intro L hL
  have hcut : (Real.exp 1)⁻¹ ≤ Real.exp (-L) := by
    rw [← Real.exp_neg]
    apply Real.exp_le_exp.mpr
    linarith [hL.2]
  rw [routeRFoldedLaplaceIntegrandAt, logHalfDensity,
    primeVacuumCurrent_eq_const hcut]

private theorem continuousOn_routeRFoldedLaplaceIntegrandAt_logHalfDensity_primeVacuumCurrent_upper
    {z : ℂ} (hz : 1 < z.re) {a T : ℝ} :
    ContinuousOn
      (routeRFoldedLaplaceIntegrandAt a (logHalfDensity (primeVacuumCurrent z)))
      (Icc 1 T) := by
  have hweight : Continuous (fun L : ℝ => Complex.exp (-((a : ℂ) * (L : ℂ)))) := by
    fun_prop
  have hhalf : Continuous (fun L : ℝ => (Real.exp (-L / 2) : ℂ)) := by
    exact Complex.continuous_ofReal.comp
      (Real.continuous_exp.comp (continuous_neg.div_const 2))
  refine (hweight.continuousOn.mul
    (hhalf.continuousOn.mul (continuousOn_primeVacuumCurrent_exp_Icc hz T))).congr ?_
  intro L hL
  rfl

private theorem integrableOn_routeRFoldedLaplaceIntegrandAt_logHalfDensity_primeVacuumCurrent_head
    {z : ℂ} (hz : 1 < z.re) {a T : ℝ} (hT : 1 ≤ T) :
    IntegrableOn
      (routeRFoldedLaplaceIntegrandAt a (logHalfDensity (primeVacuumCurrent z)))
      (Ioc 0 T) := by
  have hlower : IntegrableOn
      (routeRFoldedLaplaceIntegrandAt a (logHalfDensity (primeVacuumCurrent z)))
      (Ioc 0 1) :=
    ((ContinuousOn.integrableOn_Icc
      (continuous_routeRFoldedLaplaceIntegrandAt_logHalfDensity_primeVacuumCurrent_lower z a)).mono_set
        Ioc_subset_Icc_self)
  have hupper : IntegrableOn
      (routeRFoldedLaplaceIntegrandAt a (logHalfDensity (primeVacuumCurrent z)))
      (Ioc 1 T) :=
    ((ContinuousOn.integrableOn_Icc
      (continuousOn_routeRFoldedLaplaceIntegrandAt_logHalfDensity_primeVacuumCurrent_upper hz)).mono_set
        Ioc_subset_Icc_self)
  have hsplit : Ioc (0 : ℝ) T = Ioc 0 1 ∪ Ioc 1 T := by
    ext L
    constructor
    · intro hL
      by_cases hL1 : L ≤ 1
      · exact Or.inl ⟨hL.1, hL1⟩
      · exact Or.inr ⟨lt_of_not_ge hL1, hL.2⟩
    · intro hL
      rcases hL with hL | hL
      · exact ⟨hL.1, hL.2.trans hT⟩
      · exact ⟨lt_trans zero_lt_one hL.1, hL.2⟩
  rw [hsplit]
  exact hlower.union hupper

private theorem integrableOn_routeRFoldedLaplaceIntegrandAt_logHalfDensity_primeRemainderCurrent_head
    {z : ℂ} (hz : 1 < z.re) {a T : ℝ} (ha : 1 / 2 ≤ a) (hT : 1 ≤ T) :
    IntegrableOn
      (routeRFoldedLaplaceIntegrandAt a (logHalfDensity (primeRemainderCurrent z)))
      (Ioc 0 T) := by
  have hprime :=
    integrableOn_routeRFoldedLaplaceIntegrandAt_logHalfDensity_primeTailCurrent_head
      (T := T) hz ha
  have hvac :=
    integrableOn_routeRFoldedLaplaceIntegrandAt_logHalfDensity_primeVacuumCurrent_head
      (a := a) hz hT
  refine (hprime.sub hvac).congr_fun ?_ measurableSet_Ioc
  intro L hL
  simp only [Pi.sub_apply, routeRFoldedLaplaceIntegrandAt, logHalfDensity,
    primeRemainderCurrent]
  ring

/-- The canonical prime-vacuum remainder has a literal folded Laplace port on
the full positive logarithmic half-line at every rate `a ≥ 1 / 2`. -/
theorem integrableOn_routeRFoldedLaplaceIntegrandAt_logHalfDensity_primeRemainderCurrent
    {z : ℂ} (hz : 1 < z.re) {a : ℝ} (ha : 1 / 2 ≤ a) :
    IntegrableOn
      (routeRFoldedLaplaceIntegrandAt a (logHalfDensity (primeRemainderCurrent z)))
      (Ioi 0) := by
  obtain ⟨T, hT, htail⟩ :=
    exists_integrableOn_routeRFoldedLaplaceIntegrandAt_logHalfDensity_primeRemainderCurrent_tail
      hz ha
  rw [← Ioc_union_Ioi_eq_Ioi (show (0 : ℝ) ≤ T by linarith)]
  exact
    (integrableOn_routeRFoldedLaplaceIntegrandAt_logHalfDensity_primeRemainderCurrent_head
      hz ha hT).union htail

/-! ## Exact logarithmic--Mellin transport -/

private theorem hasDerivWithinAt_exp_neg_Ioi :
    ∀ L ∈ Ioi (0 : ℝ),
      HasDerivWithinAt (Real.exp ∘ Neg.neg) (-Real.exp (-L)) (Ioi 0) L :=
  fun L _ => mul_neg_one (Real.exp (-L)) ▸
    ((Real.hasDerivAt_exp (-L)).comp L (hasDerivAt_neg L)).hasDerivWithinAt

private theorem image_exp_neg_Ioi : (Real.exp ∘ Neg.neg) '' Ioi (0 : ℝ) = Ioo 0 1 := by
  ext x
  constructor
  · rintro ⟨L, hL, rfl⟩
    change 0 < L at hL
    constructor
    · exact Real.exp_pos _
    · change Real.exp (-L) < 1
      exact Real.exp_lt_one_iff.mpr (by linarith)
  · intro hx
    refine ⟨-Real.log x, ?_, ?_⟩
    · change 0 < -Real.log x
      exact neg_pos.mpr (Real.log_neg hx.1 hx.2)
    · simp [Real.exp_log hx.1]

private theorem injOn_exp_neg_Ioi : (Ioi (0 : ℝ)).InjOn (Real.exp ∘ Neg.neg) :=
  Real.exp_injective.injOn.comp neg_injective.injOn (fun _ _ => Set.mem_univ _)

private theorem exp_neg_cpow_weight
    (L : ℝ) (s : ℂ) (f : ℂ) :
    Real.exp (-L) • (Complex.exp (-(L : ℂ)) ^ (s - 1) • f) =
      Complex.exp (-s * (L : ℂ)) • f := by
  change (Real.exp (-L) : ℂ) * (Complex.exp (-(L : ℂ)) ^ (s - 1) * f) =
    Complex.exp (-s * (L : ℂ)) * f
  have hneg : ((-L : ℝ) : ℂ) = -(L : ℂ) := by
    push_cast
    ring
  rw [Complex.ofReal_exp, hneg, ← mul_assoc]
  have hpow : Complex.exp (-(L : ℂ)) * Complex.exp (-(L : ℂ)) ^ (s - 1)
      = Complex.exp (-(L : ℂ)) ^ s := by
    calc
      Complex.exp (-(L : ℂ)) * Complex.exp (-(L : ℂ)) ^ (s - 1)
        = Complex.exp (-(L : ℂ)) ^ (1 : ℂ) * Complex.exp (-(L : ℂ)) ^ (s - 1) := by
          rw [Complex.cpow_one]
      _ = Complex.exp (-(L : ℂ)) ^ (1 + (s - 1)) := by
          rw [← Complex.cpow_add _ _ (Complex.exp_ne_zero _)]
      _ = Complex.exp (-(L : ℂ)) ^ s := by
          congr 1
          ring
  rw [hpow, Complex.cpow_def_of_ne_zero (Complex.exp_ne_zero _),
    Complex.log_exp (by simp [Real.pi_pos]) (by simpa using Real.pi_nonneg)]
  ring_nf

private theorem exp_neg_cpow_port (L a : ℝ) (f : ℂ) :
    Real.exp (-L) •
        (Complex.exp (-(L : ℂ)) ^ (((a : ℂ) + 1 / 2) - 1) • f) =
      routeRFoldedLaplaceIntegrandAt a (fun t => (Real.exp (-t / 2) : ℂ) * f) L := by
  rw [exp_neg_cpow_weight L ((a : ℂ) + 1 / 2) f]
  simp only [routeRFoldedLaplaceIntegrandAt, smul_eq_mul]
  rw [Complex.ofReal_exp, ← mul_assoc, ← Complex.exp_add]
  congr 1
  push_cast
  ring_nf

/-- The folded logarithmic Laplace port is exactly the right Mellin integral
at `w = a + 1 / 2`; no continuity or integrability assumption on the source is used. -/
theorem routeRFoldedLaplaceIntegral_logHalfDensity_eq_mellin (a : ℝ) (r : ℝ → ℂ) :
    (∫ L : ℝ in Ioi 0, routeRFoldedLaplaceIntegrandAt a (logHalfDensity r) L) =
      ∫ x : ℝ in Ioc 0 1, r x * (x : ℂ) ^ (((a : ℂ) + 1 / 2) - 1) := by
  let g : ℝ → ℂ := fun x => (x : ℂ) ^ (((a : ℂ) + 1 / 2) - 1) • r x
  have hchange := MeasureTheory.integral_image_eq_integral_abs_deriv_smul
    (s := Ioi (0 : ℝ)) (f := Real.exp ∘ Neg.neg) (f' := fun L => -Real.exp (-L))
    measurableSet_Ioi hasDerivWithinAt_exp_neg_Ioi injOn_exp_neg_Ioi g
  rw [image_exp_neg_Ioi] at hchange
  calc
    (∫ L : ℝ in Ioi 0, routeRFoldedLaplaceIntegrandAt a (logHalfDensity r) L)
      = ∫ L : ℝ in Ioi 0, |(-Real.exp (-L))| • g ((Real.exp ∘ Neg.neg) L) := by
        apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
        intro L _
        change routeRFoldedLaplaceIntegrandAt a (logHalfDensity r) L =
          |(-Real.exp (-L))| • g ((Real.exp ∘ Neg.neg) L)
        rw [abs_neg, abs_of_pos (Real.exp_pos _)]
        have haux := (exp_neg_cpow_port L a (r (Real.exp (-L)))).symm
        have hneg : (-(L : ℂ)) = ((-L : ℝ) : ℂ) := by
          push_cast
          ring
        rw [hneg, ← Complex.ofReal_exp] at haux
        simpa only [g, Function.comp_apply, routeRFoldedLaplaceIntegrandAt, logHalfDensity] using haux
    _ = ∫ x : ℝ in Ioo 0 1, g x := hchange.symm
    _ = ∫ x : ℝ in Ioo 0 1, r x * (x : ℂ) ^ (((a : ℂ) + 1 / 2) - 1) := by
      apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioo
      intro x _
      simp only [g, smul_eq_mul]
      ring
    _ = ∫ x : ℝ in Ioc 0 1, r x * (x : ℂ) ^ (((a : ℂ) + 1 / 2) - 1) := by
      rw [MeasureTheory.integral_Ioc_eq_integral_Ioo]

/-- The exact logarithmic--Mellin transport preserves `L¹` admission. -/
theorem integrableOn_routeRFoldedLaplaceIntegrandAt_logHalfDensity_iff_mellin
    (a : ℝ) (r : ℝ → ℂ) :
    IntegrableOn (routeRFoldedLaplaceIntegrandAt a (logHalfDensity r)) (Ioi 0) ↔
      IntegrableOn (fun x : ℝ => r x * (x : ℂ) ^ (((a : ℂ) + 1 / 2) - 1)) (Ioc 0 1) := by
  let g : ℝ → ℂ := fun x => (x : ℂ) ^ (((a : ℂ) + 1 / 2) - 1) • r x
  have hchange := MeasureTheory.integrableOn_image_iff_integrableOn_abs_deriv_smul
    (s := Ioi (0 : ℝ)) (f := Real.exp ∘ Neg.neg) (f' := fun L => -Real.exp (-L))
    measurableSet_Ioi hasDerivWithinAt_exp_neg_Ioi injOn_exp_neg_Ioi g
  rw [image_exp_neg_Ioi] at hchange
  have hport : ∀ L : ℝ,
      routeRFoldedLaplaceIntegrandAt a (logHalfDensity r) L =
        |(-Real.exp (-L))| • g ((Real.exp ∘ Neg.neg) L) := by
    intro L
    rw [abs_neg, abs_of_pos (Real.exp_pos _)]
    have haux := (exp_neg_cpow_port L a (r (Real.exp (-L)))).symm
    have hneg : (-(L : ℂ)) = ((-L : ℝ) : ℂ) := by
      push_cast
      ring
    rw [hneg, ← Complex.ofReal_exp] at haux
    simpa only [g, Function.comp_apply, routeRFoldedLaplaceIntegrandAt, logHalfDensity] using haux
  have hmul : ∀ x : ℝ, g x = r x * (x : ℂ) ^ (((a : ℂ) + 1 / 2) - 1) := by
    intro x
    simp only [g, smul_eq_mul]
    ring
  constructor
  · intro h
    have hjac : IntegrableOn
        (fun L : ℝ => |(-Real.exp (-L))| • g ((Real.exp ∘ Neg.neg) L)) (Ioi 0) :=
      h.congr_fun (fun L _ => hport L) measurableSet_Ioi
    have hg : IntegrableOn g (Ioo 0 1) := hchange.mpr hjac
    have hmul' : IntegrableOn
        (fun x : ℝ => r x * (x : ℂ) ^ (((a : ℂ) + 1 / 2) - 1)) (Ioo 0 1) :=
      hg.congr_fun (fun x _ => hmul x) measurableSet_Ioo
    rwa [integrableOn_Ioc_iff_integrableOn_Ioo]
  · intro h
    rw [integrableOn_Ioc_iff_integrableOn_Ioo] at h
    have hmul' : IntegrableOn
        (fun x : ℝ => r x * (x : ℂ) ^ (((a : ℂ) + 1 / 2) - 1)) (Ioo 0 1) :=
      h
    have hg : IntegrableOn g (Ioo 0 1) :=
      hmul'.congr_fun (fun x _ => (hmul x).symm) measurableSet_Ioo
    have hjac : IntegrableOn
        (fun L : ℝ => |(-Real.exp (-L))| • g ((Real.exp ∘ Neg.neg) L)) (Ioi 0) :=
      hchange.mp hg
    exact hjac.congr_fun (fun L _ => (hport L).symm) measurableSet_Ioi

private theorem integrableOn_vacuumMellin
    {z w : ℂ} (hz : 1 < z.re) (hw : 1 < w.re) :
    IntegrableOn (fun x : ℝ => primeVacuumCurrent z x * (x : ℂ) ^ (w - 1)) (Ioc 0 1) := by
  have he : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  have hinvpos : (0 : ℝ) < (Real.exp 1)⁻¹ := by positivity
  have hinvlt : (Real.exp 1)⁻¹ < 1 := by
    rw [inv_lt_one₀ he]
    exact one_lt_exp_one
  have hsplit : Ioc (0 : ℝ) 1 =
      Ioc 0 ((Real.exp 1)⁻¹) ∪ Ioc ((Real.exp 1)⁻¹) 1 :=
    (Set.Ioc_union_Ioc_eq_Ioc hinvpos.le hinvlt.le).symm
  rw [hsplit]
  exact (integrableOn_vacuumMellin_lower hz hw).union integrableOn_vacuumMellin_upper

/-- The literal vacuum-normalized source port is an exact, zero-independent
Euler-minus-vacuum divided difference at every strict Mellin rate. -/
theorem routeRFoldedLaplaceIntegral_logHalfDensity_primeRemainderCurrent_eq
    {z : ℂ} (hz : 1 < z.re) {a : ℝ} (ha : 1 / 2 < a)
    (hzw : z ≠ ((a : ℂ) + 1 / 2)) :
    (∫ L : ℝ in Ioi 0,
      routeRFoldedLaplaceIntegrandAt a (logHalfDensity (primeRemainderCurrent z)) L) =
      (canonicalEulerLogZeta z - canonicalEulerLogZeta ((a : ℂ) + 1 / 2)) /
          (((a : ℂ) + 1 / 2) - z) -
        (primeVacuumValue z - primeVacuumValue ((a : ℂ) + 1 / 2)) /
          ((a : ℂ) + 1 / 2 - z) := by
  let w : ℂ := (a : ℂ) + 1 / 2
  have hw : 1 < w.re := by
    dsimp [w]
    norm_num
    linarith
  have hrem : IntegrableOn
      (fun x : ℝ => primeRemainderCurrent z x * (x : ℂ) ^ (w - 1)) (Ioc 0 1) := by
    dsimp [w]
    rw [← integrableOn_routeRFoldedLaplaceIntegrandAt_logHalfDensity_iff_mellin]
    exact integrableOn_routeRFoldedLaplaceIntegrandAt_logHalfDensity_primeRemainderCurrent
      hz ha.le
  have hvac : IntegrableOn
      (fun x : ℝ => primeVacuumCurrent z x * (x : ℂ) ^ (w - 1)) (Ioc 0 1) :=
    integrableOn_vacuumMellin hz hw
  have hsum :
      (∫ x : ℝ in Ioc 0 1, primeTailCurrent z x * (x : ℂ) ^ (w - 1)) =
        (∫ x : ℝ in Ioc 0 1, primeRemainderCurrent z x * (x : ℂ) ^ (w - 1)) +
          ∫ x : ℝ in Ioc 0 1, primeVacuumCurrent z x * (x : ℂ) ^ (w - 1) := by
    rw [← integral_add hrem hvac]
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioc
    intro x _
    simp only [primeRemainderCurrent]
    ring
  calc
    (∫ L : ℝ in Ioi 0,
      routeRFoldedLaplaceIntegrandAt a (logHalfDensity (primeRemainderCurrent z)) L) =
        ∫ x : ℝ in Ioc 0 1, primeRemainderCurrent z x * (x : ℂ) ^ (w - 1) := by
          dsimp [w]
          exact routeRFoldedLaplaceIntegral_logHalfDensity_eq_mellin a _
    _ =
        ((∫ x : ℝ in Ioc 0 1, primeRemainderCurrent z x * (x : ℂ) ^ (w - 1)) +
          ∫ x : ℝ in Ioc 0 1, primeVacuumCurrent z x * (x : ℂ) ^ (w - 1)) -
          ∫ x : ℝ in Ioc 0 1, primeVacuumCurrent z x * (x : ℂ) ^ (w - 1) := by ring
    _ =
        (∫ x : ℝ in Ioc 0 1, primeTailCurrent z x * (x : ℂ) ^ (w - 1)) -
          ∫ x : ℝ in Ioc 0 1, primeVacuumCurrent z x * (x : ℂ) ^ (w - 1) := by
            rw [hsum]
    _ =
        (canonicalEulerLogZeta z - canonicalEulerLogZeta w) / (w - z) -
          (primeVacuumValue z - primeVacuumValue w) / (w - z) := by
            rw [primeTailCurrent_mellin hz hw (by simpa [w] using hzw),
              integral_vacuumMellin hz hw (by simpa [w] using hzw)]
    _ =
        (canonicalEulerLogZeta z - canonicalEulerLogZeta ((a : ℂ) + 1 / 2)) /
            (((a : ℂ) + 1 / 2) - z) -
          (primeVacuumValue z - primeVacuumValue ((a : ℂ) + 1 / 2)) /
            ((a : ℂ) + 1 / 2 - z) := by
              dsimp [w]

end RHTower
