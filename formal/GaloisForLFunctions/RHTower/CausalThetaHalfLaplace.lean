import GaloisForLFunctions.RHTower.ThetaPrimeDeletionSpectralEscape
import GaloisForLFunctions.RHTower.MobiusThetaNativeMeyerAdmission
import GaloisForLFunctions.RHTower.HedenmalmThetaPrimeTranslationFixedFibre
import GaloisForLFunctions.RHTower.ThetaCuspReflectedSourceOddStationary
import GaloisForLFunctions.RHTower.HedenmalmThetaKernelEnergy

/-!
# The half-line Laplace transform of the theta source

For the completed theta source `k = thetaCuspFullSource` put
`K(w) = ∫_0^∞ k(u) e^{wu} du`.  The source decays faster than every exponential, so `K` is entire,
and so is every truncated tail `∫_L^∞ k(u) e^{wu} du`.  Evenness of `k` and its exact bilateral
transform give the reflection law `K(w) + K(−w) = Ξ(iw) = ξ(1/2 − w)`.

Monotonicity of `k` on the positive ray makes the reflected half-line transform zero-free on the
right half-plane: with `ν = −k' ≥ 0` of total mass `k(0)`,
`Re(w K(−w)) = ∫_0^∞ (1 − Re e^{−wu}) ν(u) du > 0`.
Hence at any zero `ρ` of `ζ` with `1/2 < Re ρ < 1`, `K(ρ − 1/2) ≠ 0`.

The source also has the Gaussian atom bound `|k(log u)| + |k'(log u)| ≤ C (1+u)^C e^{−π u²}` for
`u ≥ 1`, from its atom expansion `k(log u) = √u ∑_{m ≥ 1} g(mu)`.
-/

open Complex MeasureTheory Set Filter Topology Polynomial Asymptotics

namespace RHTower

noncomputable section

/-! ### Exponential decay at every rate -/

theorem exists_abs_iteratedDeriv_thetaCuspFullSource_le (A : ℝ) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ,
      |iteratedDeriv m thetaCuspFullSource x| ≤ C * Real.exp (-(A * |x|)) := by
  obtain ⟨C, hC⟩ := thetaCuspFullSource_derivative_exp_bound A m
  have hC0 : 0 ≤ C := le_trans (by positivity) (hC 0)
  refine ⟨C, hC0, fun x => ?_⟩
  have h := hC x
  rw [Real.exp_neg, ← div_eq_mul_inv, le_div_iff₀ (Real.exp_pos _), mul_comm]
  exact h

theorem exists_abs_thetaCuspFullSource_le (A : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, |thetaCuspFullSource x| ≤ C * Real.exp (-(A * |x|)) := by
  obtain ⟨C, hC0, hC⟩ := exists_abs_iteratedDeriv_thetaCuspFullSource_le A 0
  exact ⟨C, hC0, fun x => by simpa using hC x⟩

theorem exists_abs_deriv_thetaCuspFullSource_le (A : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, |deriv thetaCuspFullSource x| ≤ C * Real.exp (-(A * |x|)) := by
  obtain ⟨C, hC0, hC⟩ := exists_abs_iteratedDeriv_thetaCuspFullSource_le A 1
  exact ⟨C, hC0, fun x => by simpa [iteratedDeriv_one] using hC x⟩

theorem differentiable_thetaCuspFullSource : Differentiable ℝ thetaCuspFullSource :=
  contDiff_thetaCuspFullSource.differentiable (by simp)

theorem continuous_deriv_thetaCuspFullSource : Continuous (deriv thetaCuspFullSource) :=
  contDiff_thetaCuspFullSource.continuous_deriv (by simp)

/-- The source is non-increasing on the positive ray: `k' ≤ 0` there. -/
theorem deriv_thetaCuspFullSource_nonpos {x : ℝ} (hx : 0 < x) :
    deriv thetaCuspFullSource x ≤ 0 := by
  have hanti : AntitoneOn thetaCuspFullSource (Ioi 0) :=
    HedenmalmThetaSource.antitoneOn_thetaCuspFullSource.mono Ioi_subset_Ici_self
  have h := hanti.derivWithin_nonpos (x := x)
  rwa [derivWithin_of_isOpen isOpen_Ioi hx] at h

/-! ### Truncated half-line transforms -/

/-- The truncated half-line transform `∫_L^∞ k(u) e^{wu} du`. -/
def thetaHalfLaplaceTail (L : ℝ) (w : ℂ) : ℂ :=
  ∫ u in Ioi L, Complex.exp (w * u) * (thetaCuspFullSource u : ℂ)

/-- The half-line transform `K(w) = ∫_0^∞ k(u) e^{wu} du`. -/
def thetaHalfLaplace (w : ℂ) : ℂ := thetaHalfLaplaceTail 0 w

theorem integrableOn_cexp_mul_thetaCuspFullSource (w : ℂ) (s : Set ℝ) :
    IntegrableOn (fun u : ℝ => Complex.exp (w * u) * (thetaCuspFullSource u : ℂ)) s :=
  (integrable_cexp_mul_thetaCuspFullSource w).integrableOn

private theorem ofReal_exp_cpow (x : ℝ) (z : ℂ) :
    ((Real.exp x : ℝ) : ℂ) ^ z = Complex.exp ((x : ℂ) * z) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_pos x).ne'),
    ← Complex.ofReal_log (Real.exp_pos x).le, Real.log_exp]

/-- The logarithmic source restricted beyond `e^L`, as a function on the multiplicative ray. -/
def thetaLogSourceBeyond (L : ℝ) (t : ℝ) : ℂ :=
  Set.indicator (Ioi (Real.exp L)) (fun t => (thetaCuspFullSource (Real.log t) : ℂ)) t

/-- **The truncated transform is a Mellin transform.** -/
theorem thetaHalfLaplaceTail_eq_mellin (L : ℝ) (w : ℂ) :
    thetaHalfLaplaceTail L w = mellin (thetaLogSourceBeyond L) w := by
  rw [mellin, integral_Ioi_comp_exp_complex, thetaHalfLaplaceTail,
    ← integral_indicator measurableSet_Ioi]
  refine integral_congr_ae (Eventually.of_forall (fun x => ?_))
  simp only [thetaLogSourceBeyond, smul_eq_mul]
  by_cases hx : L < x
  · rw [Set.indicator_of_mem (show x ∈ Ioi L from hx),
      Set.indicator_of_mem (show Real.exp x ∈ Ioi (Real.exp L) from Real.exp_lt_exp.mpr hx),
      Real.log_exp, ofReal_exp_cpow, Complex.ofReal_exp, ← mul_assoc, ← Complex.exp_add]
    congr 2
    ring
  · rw [Set.indicator_of_notMem (show x ∉ Ioi L from hx),
      Set.indicator_of_notMem (show Real.exp x ∉ Ioi (Real.exp L) from
        fun h => hx (Real.exp_lt_exp.mp h))]
    simp

theorem measurable_thetaLogSourceBeyond (L : ℝ) : Measurable (thetaLogSourceBeyond L) := by
  refine Measurable.indicator ?_ measurableSet_Ioi
  exact Complex.continuous_ofReal.measurable.comp
    (continuous_thetaCuspFullSource.measurable.comp Real.measurable_log)

theorem exists_norm_thetaLogSourceBeyond_le (L : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, ‖thetaLogSourceBeyond L t‖ ≤ C := by
  obtain ⟨C, hC0, hC⟩ := exists_abs_thetaCuspFullSource_le 0
  refine ⟨C, hC0, fun t => ?_⟩
  simp only [thetaLogSourceBeyond]
  by_cases ht : t ∈ Ioi (Real.exp L)
  · rw [Set.indicator_of_mem ht, Complex.norm_real, Real.norm_eq_abs]
    simpa using hC (Real.log t)
  · rw [Set.indicator_of_notMem ht, norm_zero]; exact hC0

theorem locallyIntegrableOn_thetaLogSourceBeyond (L : ℝ) :
    LocallyIntegrableOn (thetaLogSourceBeyond L) (Ioi 0) := by
  obtain ⟨C, _, hC⟩ := exists_norm_thetaLogSourceBeyond_le L
  have hLI : LocallyIntegrable (thetaLogSourceBeyond L) volume := by
    refine locallyIntegrable_iff.mpr (fun K hK => ?_)
    exact Measure.integrableOn_of_bounded (M := C) hK.measure_lt_top.ne
      (measurable_thetaLogSourceBeyond L).aestronglyMeasurable (ae_of_all _ (fun t => hC t))
  exact hLI.locallyIntegrableOn _

/-- The logarithmic source decays faster than every power at infinity. -/
theorem thetaLogSourceBeyond_isBigO_rpow (L a : ℝ) :
    thetaLogSourceBeyond L =O[atTop] (fun t : ℝ => t ^ (-a)) := by
  obtain ⟨C, _, hC⟩ := exists_abs_thetaCuspFullSource_le a
  refine IsBigO.of_bound C ?_
  filter_upwards [eventually_ge_atTop 1] with t ht
  have ht0 : 0 < t := zero_lt_one.trans_le ht
  have hlog : 0 ≤ Real.log t := Real.log_nonneg ht
  rw [Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos ht0 _)]
  simp only [thetaLogSourceBeyond]
  by_cases hmem : t ∈ Ioi (Real.exp L)
  · rw [Set.indicator_of_mem hmem, Complex.norm_real, Real.norm_eq_abs]
    refine (hC _).trans (le_of_eq ?_)
    rw [abs_of_nonneg hlog, Real.rpow_def_of_pos ht0]
    congr 2
    ring
  · rw [Set.indicator_of_notMem hmem, norm_zero]
    exact mul_nonneg (le_trans (abs_nonneg _) ((hC 0).trans (by simp))) (Real.rpow_pos_of_pos ht0 _).le

/-- The logarithmic source vanishes near the origin. -/
theorem thetaLogSourceBeyond_isBigO_zero (L b : ℝ) :
    thetaLogSourceBeyond L =O[𝓝[>] 0] (fun t : ℝ => t ^ (-b)) := by
  refine IsBigO.of_bound 0 ?_
  filter_upwards [Ioo_mem_nhdsGT (Real.exp_pos L)] with t ht
  simp only [thetaLogSourceBeyond]
  rw [Set.indicator_of_notMem (show t ∉ Ioi (Real.exp L) from fun h => (lt_asymm h ht.2)),
    norm_zero, zero_mul]

/-- **Every truncated transform is entire.** -/
theorem differentiable_thetaHalfLaplaceTail (L : ℝ) :
    Differentiable ℂ (thetaHalfLaplaceTail L) := by
  intro w
  have hfun : thetaHalfLaplaceTail L = mellin (thetaLogSourceBeyond L) :=
    funext (thetaHalfLaplaceTail_eq_mellin L)
  rw [hfun]
  exact mellin_differentiableAt_of_isBigO_rpow (a := w.re + 1) (b := w.re - 1)
    (locallyIntegrableOn_thetaLogSourceBeyond L) (thetaLogSourceBeyond_isBigO_rpow L _)
    (by linarith) (thetaLogSourceBeyond_isBigO_zero L _) (by linarith)

theorem differentiable_thetaHalfLaplace : Differentiable ℂ thetaHalfLaplace :=
  differentiable_thetaHalfLaplaceTail 0

/-- A uniform bound for the truncated transforms: for `Re w ≤ σ < A` and `L ≥ 0`,
`|∫_L^∞ k(u) e^{wu} du| ≤ C_A e^{−(A−σ)L}/(A−σ)`. -/
theorem norm_thetaHalfLaplaceTail_le {A C σ L : ℝ} (hC : ∀ x, |thetaCuspFullSource x| ≤
    C * Real.exp (-(A * |x|))) (hσA : σ < A) (hL : 0 ≤ L) {w : ℂ} (hw : w.re ≤ σ) :
    ‖thetaHalfLaplaceTail L w‖ ≤ C * Real.exp (-((A - σ) * L)) / (A - σ) := by
  have hAσ : 0 < A - σ := sub_pos.mpr hσA
  have hC0 : 0 ≤ C := le_trans (abs_nonneg _) ((hC 0).trans (by simp))
  have hbound : ∀ u ∈ Ioi L, ‖Complex.exp (w * u) * (thetaCuspFullSource u : ℂ)‖ ≤
      C * Real.exp (-(A - σ) * u) := by
    intro u hu
    have hu0 : 0 ≤ u := hL.trans hu.le
    rw [norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs]
    have h1 : (w * (u : ℂ)).re = w.re * u := by simp
    rw [h1]
    have h2 := mul_le_mul_of_nonneg_left (hC u) (Real.exp_pos (w.re * u)).le
    have h3 : Real.exp (w.re * u) * (C * Real.exp (-(A * |u|))) =
        C * Real.exp (w.re * u - A * u) := by
      rw [abs_of_nonneg hu0, mul_left_comm, ← Real.exp_add]; ring_nf
    have h4 : C * Real.exp (w.re * u - A * u) ≤ C * Real.exp (-(A - σ) * u) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith)) hC0
    linarith
  have hint : IntegrableOn (fun u : ℝ => C * Real.exp (-(A - σ) * u)) (Ioi L) :=
    (integrableOn_exp_mul_Ioi (neg_lt_zero.mpr hAσ) L).const_mul C
  calc ‖thetaHalfLaplaceTail L w‖
      ≤ ∫ u in Ioi L, ‖Complex.exp (w * u) * (thetaCuspFullSource u : ℂ)‖ :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ u in Ioi L, C * Real.exp (-(A - σ) * u) :=
        setIntegral_mono_on (integrableOn_cexp_mul_thetaCuspFullSource w _).norm hint
          measurableSet_Ioi hbound
    _ = C * Real.exp (-((A - σ) * L)) / (A - σ) := by
        rw [integral_const_mul, integral_exp_mul_Ioi (neg_lt_zero.mpr hAσ)]
        field_simp

/-! ### Reflection to Xi -/

/-- **Reflection law.**  `K(w) + K(−w) = Ξ(iw)`, the full bilateral transform of the even source. -/
theorem thetaHalfLaplace_add_neg (w : ℂ) :
    thetaHalfLaplace w + thetaHalfLaplace (-w) = XiC (I * w) := by
  rw [← integral_cexp_mul_thetaCuspFullSource]
  have hneg : thetaHalfLaplace (-w) =
      ∫ u in Iic (0 : ℝ), Complex.exp (w * u) * (thetaCuspFullSource u : ℂ) := by
    rw [thetaHalfLaplace, thetaHalfLaplaceTail]
    have h := integral_comp_neg_Ioi (0 : ℝ)
      (fun u : ℝ => Complex.exp (w * u) * (thetaCuspFullSource u : ℂ))
    simp only [neg_zero] at h
    rw [← h]
    refine setIntegral_congr_fun measurableSet_Ioi (fun u _ => ?_)
    simp only [thetaCuspFullSource_neg]
    push_cast
    ring_nf
  have hunion : (∫ u : ℝ, Complex.exp (w * u) * (thetaCuspFullSource u : ℂ)) =
      (∫ u in Iic (0 : ℝ), Complex.exp (w * u) * (thetaCuspFullSource u : ℂ)) +
        ∫ u in Ioi (0 : ℝ), Complex.exp (w * u) * (thetaCuspFullSource u : ℂ) := by
    rw [← setIntegral_univ, ← Iic_union_Ioi (a := (0 : ℝ))]
    exact setIntegral_union (Set.disjoint_left.mpr (fun x hx hx' =>
      (not_lt.mpr (show x ≤ 0 from hx)) (show (0 : ℝ) < x from hx')))
      measurableSet_Ioi (integrableOn_cexp_mul_thetaCuspFullSource w _)
      (integrableOn_cexp_mul_thetaCuspFullSource w _)
  rw [hneg, hunion, thetaHalfLaplace, thetaHalfLaplaceTail, add_comm]

/-! ### Positivity from monotonicity -/

theorem integrableOn_Ioi_deriv_thetaCuspFullSource :
    IntegrableOn (deriv thetaCuspFullSource) (Ioi 0) := by
  obtain ⟨C, _, hC⟩ := exists_abs_deriv_thetaCuspFullSource_le 1
  refine Integrable.mono' ((integrableOn_exp_mul_Ioi (a := -1) (by norm_num) 0).const_mul C)
    continuous_deriv_thetaCuspFullSource.aestronglyMeasurable.restrict ?_
  refine (ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ (fun x hx => ?_))
  rw [Real.norm_eq_abs]
  have h := hC x
  rw [abs_of_pos (show (0 : ℝ) < x from hx), one_mul] at h
  simpa [neg_mul, one_mul] using h

/-- The total mass of `ν = −k'` on the positive ray is `k(0)`. -/
theorem integral_Ioi_deriv_thetaCuspFullSource :
    ∫ u in Ioi (0 : ℝ), deriv thetaCuspFullSource u = -thetaCuspFullSource 0 := by
  rw [integral_Ioi_of_hasDerivAt_of_tendsto (m := 0)
    continuous_thetaCuspFullSource.continuousWithinAt
    (fun x _ => (differentiable_thetaCuspFullSource x).hasDerivAt)
    integrableOn_Ioi_deriv_thetaCuspFullSource tendsto_thetaCuspFullSource_atTop_zero, zero_sub]

/-- **Integration by parts on the positive ray.**
`w K(−w) = ∫_0^∞ (−k'(u)) (1 − e^{−wu}) du` for `Re w > 0`. -/
theorem mul_thetaHalfLaplace_neg {w : ℂ} (hw : 0 < w.re) :
    w * thetaHalfLaplace (-w) = ∫ u in Ioi (0 : ℝ),
      (((-deriv thetaCuspFullSource u : ℝ)) : ℂ) * (1 - Complex.exp (-(w * u))) := by
  have hw0 : w ≠ 0 := fun h => by rw [h] at hw; simp at hw
  obtain ⟨Cd, _, hCd⟩ := exists_abs_deriv_thetaCuspFullSource_le 1
  have hcd := continuous_deriv_thetaCuspFullSource
  have hck := continuous_thetaCuspFullSource
  have hexp_le : ∀ x : ℝ, 0 < x → ‖Complex.exp (-(w * x))‖ ≤ 1 := by
    intro x hx
    rw [Complex.norm_exp]
    have : (-(w * (x : ℂ))).re = -(w.re * x) := by simp
    rw [this, Real.exp_le_one_iff]
    nlinarith
  have hUd : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt (fun y : ℝ => (thetaCuspFullSource y : ℂ))
      ((deriv thetaCuspFullSource x : ℝ) : ℂ) x := fun x _ =>
    ((differentiable_thetaCuspFullSource x).hasDerivAt).ofReal_comp
  have hVd : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt (fun y : ℝ => -(Complex.exp (-(w * y))) / w)
      (Complex.exp (-(w * x))) x := by
    intro x _
    have h1 : HasDerivAt (fun y : ℝ => -(w * (y : ℂ))) (-w) x := by
      have h := ((hasDerivAt_id x).ofReal_comp.const_mul w).neg
      simp only [id, Complex.ofReal_one, mul_one] at h
      exact h
    exact ((h1.cexp).neg.div_const w).congr_deriv (by field_simp)
  have hUV' : IntegrableOn (fun x : ℝ => (thetaCuspFullSource x : ℂ) *
      Complex.exp (-(w * x))) (Ioi 0) := by
    refine (integrableOn_cexp_mul_thetaCuspFullSource (-w) (Ioi 0)).congr_fun
      (fun x _ => ?_) measurableSet_Ioi
    simp only
    rw [mul_comm, neg_mul]
  have hbd : ∀ x ∈ Ioi (0 : ℝ), ‖((deriv thetaCuspFullSource x : ℝ) : ℂ)‖ ≤
      Cd * Real.exp (-1 * x) := by
    intro x hx
    rw [Complex.norm_real, Real.norm_eq_abs]
    have := hCd x
    rwa [abs_of_pos (show (0 : ℝ) < x from hx), one_mul, ← neg_one_mul] at this
  have hU'V : IntegrableOn (fun x : ℝ => ((deriv thetaCuspFullSource x : ℝ) : ℂ) *
      (-(Complex.exp (-(w * x))) / w)) (Ioi 0) := by
    refine Integrable.mono' ((integrableOn_exp_mul_Ioi (a := -1) (by norm_num) 0).const_mul
      (Cd / ‖w‖)) (by fun_prop : Continuous (fun x : ℝ =>
        ((deriv thetaCuspFullSource x : ℝ) : ℂ) * (-(Complex.exp (-(w * x))) / w))).aestronglyMeasurable
      ((ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ (fun x hx => ?_)))
    rw [norm_mul, norm_div, norm_neg]
    have h1 := hbd x hx
    have h2 := hexp_le x hx
    calc ‖((deriv thetaCuspFullSource x : ℝ) : ℂ)‖ * (‖Complex.exp (-(w * x))‖ / ‖w‖)
        ≤ Cd * Real.exp (-1 * x) * (1 / ‖w‖) :=
          mul_le_mul h1 (div_le_div_of_nonneg_right h2 (norm_nonneg _)) (by positivity)
            (le_trans (norm_nonneg _) h1)
      _ = Cd / ‖w‖ * Real.exp (-1 * x) := by ring
  have hzero : Tendsto (fun x : ℝ => (thetaCuspFullSource x : ℂ) *
      (-(Complex.exp (-(w * x))) / w)) (𝓝[>] (0 : ℝ))
      (𝓝 (-(thetaCuspFullSource 0 : ℂ) / w)) := by
    have hc : Continuous (fun x : ℝ => (thetaCuspFullSource x : ℂ) *
        (-(Complex.exp (-(w * x))) / w)) := by fun_prop
    have := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    convert this using 2
    simp
    ring
  have hinf : Tendsto (fun x : ℝ => (thetaCuspFullSource x : ℂ) *
      (-(Complex.exp (-(w * x))) / w)) atTop (𝓝 0) := by
    have hk : Tendsto (fun x : ℝ => (thetaCuspFullSource x : ℂ)) atTop (𝓝 0) := by
      simpa using tendsto_thetaCuspFullSource_atTop_zero.ofReal
    have hk' := hk.norm.mul_const (1 / ‖w‖)
    rw [norm_zero, zero_mul] at hk'
    refine squeeze_zero_norm' ?_ hk'
    filter_upwards [eventually_gt_atTop 0] with x hx
    rw [norm_mul, norm_div, norm_neg]
    exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right (hexp_le x hx) (norm_nonneg _))
      (norm_nonneg _)
  have hibp := integral_Ioi_mul_deriv_eq_deriv_mul hUd hVd hUV' hU'V hzero hinf
  have hK : thetaHalfLaplace (-w) = ∫ x in Ioi (0 : ℝ), (thetaCuspFullSource x : ℂ) *
      Complex.exp (-(w * x)) := by
    rw [thetaHalfLaplace, thetaHalfLaplaceTail]
    refine setIntegral_congr_fun measurableSet_Ioi (fun x _ => ?_)
    rw [mul_comm, neg_mul]
  have hmass : ∫ u in Ioi (0 : ℝ), ((deriv thetaCuspFullSource u : ℝ) : ℂ) =
      -(thetaCuspFullSource 0 : ℂ) := by
    rw [integral_complex_ofReal, integral_Ioi_deriv_thetaCuspFullSource, Complex.ofReal_neg]
  have hint1 : IntegrableOn (fun u : ℝ => ((deriv thetaCuspFullSource u : ℝ) : ℂ)) (Ioi 0) :=
    integrableOn_Ioi_deriv_thetaCuspFullSource.ofReal
  have hint2 : IntegrableOn (fun u : ℝ => ((deriv thetaCuspFullSource u : ℝ) : ℂ) *
      Complex.exp (-(w * u))) (Ioi 0) := by
    refine IntegrableOn.congr_fun (hU'V.const_mul (-w)) (fun x _ => ?_) measurableSet_Ioi
    field_simp
  have hUVint : ∫ x in Ioi (0 : ℝ), ((deriv thetaCuspFullSource x : ℝ) : ℂ) *
      (-(Complex.exp (-(w * x))) / w) =
      -(∫ u in Ioi (0 : ℝ), ((deriv thetaCuspFullSource u : ℝ) : ℂ) *
        Complex.exp (-(w * u))) / w := by
    rw [neg_div, ← integral_div, ← integral_neg]
    refine setIntegral_congr_fun measurableSet_Ioi (fun x _ => ?_)
    ring
  have hsplit : ∫ u in Ioi (0 : ℝ),
      (((-deriv thetaCuspFullSource u : ℝ)) : ℂ) * (1 - Complex.exp (-(w * u))) =
      -(∫ u in Ioi (0 : ℝ), ((deriv thetaCuspFullSource u : ℝ) : ℂ)) +
        ∫ u in Ioi (0 : ℝ), ((deriv thetaCuspFullSource u : ℝ) : ℂ) *
          Complex.exp (-(w * u)) := by
    have hneg1 : IntegrableOn (fun u : ℝ => -((deriv thetaCuspFullSource u : ℝ) : ℂ)) (Ioi 0) :=
      hint1.neg
    rw [← integral_neg, ← integral_add hneg1 hint2]
    refine setIntegral_congr_fun measurableSet_Ioi (fun x _ => ?_)
    push_cast
    ring
  rw [hK, hibp, hUVint, hsplit, hmass]
  field_simp
  ring

/-- **The reflected half-line transform is zero-free on the right half-plane.**
`Re(w K(−w)) > 0` whenever `Re w > 0`. -/
theorem re_mul_thetaHalfLaplace_neg_pos {w : ℂ} (hw : 0 < w.re) :
    0 < (w * thetaHalfLaplace (-w)).re := by
  rw [mul_thetaHalfLaplace_neg hw]
  set ν : ℝ → ℝ := fun u => -deriv thetaCuspFullSource u with hν
  have hν0 : ∀ u ∈ Ioi (0 : ℝ), 0 ≤ ν u := fun u hu => by
    simp only [hν]; linarith [deriv_thetaCuspFullSource_nonpos (show (0 : ℝ) < u from hu)]
  have hνint : IntegrableOn ν (Ioi 0) := integrableOn_Ioi_deriv_thetaCuspFullSource.neg
  have hνmass : ∫ u in Ioi (0 : ℝ), ν u = thetaCuspFullSource 0 := by
    simp only [hν]; rw [integral_neg, integral_Ioi_deriv_thetaCuspFullSource, neg_neg]
  -- the complex integrand is integrable
  have hint : IntegrableOn (fun u : ℝ => (((-deriv thetaCuspFullSource u : ℝ)) : ℂ) *
      (1 - Complex.exp (-(w * u)))) (Ioi 0) := by
    refine Integrable.mono' (hνint.norm.mul_const 2) ?_ ?_
    · have hcd := continuous_deriv_thetaCuspFullSource
      exact (by fun_prop : Continuous (fun u : ℝ => (((-deriv thetaCuspFullSource u : ℝ)) : ℂ) *
        (1 - Complex.exp (-(w * u))))).aestronglyMeasurable
    · refine (ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ (fun x hx => ?_))
      rw [norm_mul]
      have h1 : ‖(((-deriv thetaCuspFullSource x : ℝ)) : ℂ)‖ = ‖ν x‖ := by
        simp [hν, Complex.norm_real]
      have h2 : ‖(1 : ℂ) - Complex.exp (-(w * x))‖ ≤ 2 := by
        refine (norm_sub_le _ _).trans ?_
        rw [norm_one, Complex.norm_exp]
        have : (-(w * (x : ℂ))).re = -(w.re * x) := by simp
        rw [this]
        have : Real.exp (-(w.re * x)) ≤ 1 := by
          rw [Real.exp_le_one_iff]; nlinarith [show (0 : ℝ) < x from hx]
        linarith
      rw [h1]
      exact mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
  have hre_int := integral_re hint
  simp only [RCLike.re_to_complex] at hre_int
  rw [← hre_int]
  -- compare with `ν (1 − e^{−σu})`
  set g : ℝ → ℝ := fun u => ν u * (1 - Real.exp (-(w.re * u))) with hg
  have hgint : IntegrableOn g (Ioi 0) := by
    refine Integrable.mono' (hνint.norm.mul_const 1) ?_ ?_
    · have hcd := continuous_deriv_thetaCuspFullSource
      exact (by fun_prop : Continuous (fun u : ℝ => -deriv thetaCuspFullSource u *
        (1 - Real.exp (-(w.re * u))))).aestronglyMeasurable
    · refine (ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ (fun x hx => ?_))
      have hx0 : (0 : ℝ) < x := hx
      rw [Real.norm_eq_abs, abs_mul, mul_one]
      refine mul_le_of_le_one_right (abs_nonneg _) ?_
      rw [abs_of_nonneg (sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by nlinarith)))]
      linarith [Real.exp_pos (-(w.re * x))]
  have hgpos : 0 < ∫ u in Ioi (0 : ℝ), g u := by
    have hg0 : 0 ≤ᵐ[volume.restrict (Ioi 0)] g :=
      (ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ (fun x hx => by
        have hx0 : (0 : ℝ) < x := hx
        exact mul_nonneg (hν0 x hx) (sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by nlinarith)))))
    rw [setIntegral_pos_iff_support_of_nonneg_ae hg0 hgint]
    have hνpos : 0 < ∫ u in Ioi (0 : ℝ), ν u := by
      rw [hνmass]; exact thetaCuspFullSource_pos_all 0
    have hν0' : 0 ≤ᵐ[volume.restrict (Ioi 0)] ν :=
      (ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ hν0)
    rw [setIntegral_pos_iff_support_of_nonneg_ae hν0' hνint] at hνpos
    refine lt_of_lt_of_le hνpos (measure_mono ?_)
    intro x ⟨hx1, hx2⟩
    refine ⟨?_, hx2⟩
    have hx0 : (0 : ℝ) < x := hx2
    simp only [Function.mem_support, hg] at hx1 ⊢
    refine mul_ne_zero hx1 (sub_ne_zero.mpr ?_)
    have : Real.exp (-(w.re * x)) < 1 := Real.exp_lt_one_iff.mpr (by nlinarith)
    exact this.ne'
  refine lt_of_lt_of_le hgpos (setIntegral_mono_on hgint hint.re measurableSet_Ioi ?_)
  intro x hx
  have hx0 : (0 : ℝ) < x := hx
  simp only [hg, hν]
  have hre : ((((-deriv thetaCuspFullSource x : ℝ)) : ℂ) * (1 - Complex.exp (-(w * x)))).re =
      -(deriv thetaCuspFullSource x) * (1 - (Complex.exp (-(w * x))).re) := by
    rw [Complex.re_ofReal_mul, Complex.sub_re, Complex.one_re]
  rw [hre]
  refine mul_le_mul_of_nonneg_left ?_ (hν0 x hx)
  have hle : (Complex.exp (-(w * x))).re ≤ Real.exp (-(w.re * x)) := by
    refine (Complex.re_le_norm _).trans (le_of_eq ?_)
    rw [Complex.norm_exp]
    simp
  linarith

theorem thetaHalfLaplace_neg_ne_zero {w : ℂ} (hw : 0 < w.re) : thetaHalfLaplace (-w) ≠ 0 := by
  intro h
  have := re_mul_thetaHalfLaplace_neg_pos hw
  rw [h, mul_zero, Complex.zero_re] at this
  exact lt_irrefl _ this

/-- **No right-of-centre zero hides in the numerator.**  At a zero `ρ` of `ζ` with
`1/2 < Re ρ < 1`, the half-line transform does not vanish at `ρ − 1/2`. -/
theorem thetaHalfLaplace_ne_zero_of_riemannZeta_eq_zero {ρ : ℂ} (hρ : riemannZeta ρ = 0)
    (h1 : 1 / 2 < ρ.re) (h2 : ρ.re < 1) : thetaHalfLaplace (ρ - 1 / 2) ≠ 0 := by
  intro hK
  have hρ1 : ρ ≠ 1 := fun h => by rw [h] at h2; simp at h2
  have hxi : xi ρ = 0 := (xi_eq_zero_iff (by linarith) hρ1).mpr hρ
  have hXi : XiC (I * (ρ - 1 / 2)) = 0 := by
    rw [XiC, show 1 / 2 + I * (ρ - 1 / 2) * I = 1 - ρ by
      rw [mul_comm I, mul_assoc, Complex.I_mul_I]; ring, xi_one_sub, hxi]
  have hsum := thetaHalfLaplace_add_neg (ρ - 1 / 2)
  rw [hK, zero_add, hXi] at hsum
  exact thetaHalfLaplace_neg_ne_zero (w := ρ - 1 / 2) (by simp; linarith) hsum

end

end RHTower
