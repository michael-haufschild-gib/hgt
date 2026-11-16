import GaloisForLFunctions.RHTower.ConnesConvolutionKernelField
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.CausalReflection.ModulatedCausalReflectionMoments
import GaloisForLFunctions.ExclusionOfTheCriticalState.TheExplicitFormulaHoldsAtTheStateAgainstSmoothTests

/-!
# The zero values of the state are a negative vector of the zero pairing

For the critical state `F` and every profile `G` of the energy domain,

  `lim_{ε→0⁺} Σ_z L F(z) L G(−z) e^{εz²} = W(F, G)`,

Weil's bare form of the pair, the sum over the centred zeros with multiplicity: the explicit formula
holds at the state against the whole domain, with Gaussian summation. For `G = F`,

  `lim_{ε→0⁺} Σ_z L F(z) L F(−z) e^{εz²} = −a ∫ F² e^{−8u} < 0`.

So the vector `c = (L F(z))_z` of zero values is negative for the pairing `β(c, d) = Σ_z c_z d_{−z}`.
A zero on the line contributes `|L F(z)|² e^{−ε (Im z)²} ≥ 0`: the negative mass is carried by the
zeros off the line.

Mechanism. `L G(−z) = ∫ G(T) e^{−zT} dT`, so the weighted pairing is the integral of `G(T)` against the
heated zero series `Σ_z L F(z) e^{εz² − zT} = a (k_ε * F⁺ − k_ε * (e^{−8u} F))(T)`. After the exponential
weights are moved to the profiles, each term is `∫ κ_ε(s) C(s) ds` for a tilted heat kernel `κ_ε` and
the correlation `C(s) = ∫ p(T) q(T + s) dT` of two square-integrable profiles. `C` is continuous and
bounded, so the limit is `C(0)`: the confinement pairing of `G` and `F` for the state term, and zero
for the term beyond the wall, whose profiles have disjoint supports. The weak equation of the state
identifies the limit with Weil's form.
-/

noncomputable section
open MeasureTheory Set Filter Zeta23 Complex Metric Topology

namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri
  CriticalArithmeticCorrelationTheory HTGeometry _root_.RHTower

/-! ### The correlation of two square-integrable profiles -/

/-- The correlation of two profiles, `∫ p(T) q(T + s) dT`. -/
def profileCorrelation (p q : ℝ → ℂ) (s : ℝ) : ℂ := ∫ T : ℝ, p T * q (T + s)

theorem integrable_mul_translate_of_sq {p q : ℝ → ℂ} (hp : Measurable p) (hq : Measurable q)
    (hp2 : Integrable fun T => ‖p T‖ ^ 2) (hq2 : Integrable fun u => ‖q u‖ ^ 2) (s : ℝ) :
    Integrable fun T : ℝ => p T * q (T + s) := by
  have hq2' : Integrable fun T : ℝ => ‖q (T + s)‖ ^ 2 := hq2.comp_add_right s
  refine ((hp2.add hq2').div_const 2).mono' ?_ (Eventually.of_forall fun T => ?_)
  · exact (hp.mul (hq.comp (measurable_id.add_const s))).aestronglyMeasurable
  · show ‖p T * q (T + s)‖ ≤ (‖p T‖ ^ 2 + ‖q (T + s)‖ ^ 2) / 2
    rw [norm_mul]
    nlinarith [sq_nonneg (‖p T‖ - ‖q (T + s)‖)]

/-- The product of a profile with a translate has mass at most the mean of the two square masses,
uniformly in the translation. -/
theorem integral_norm_mul_translate_le {p q : ℝ → ℂ} (hp : Measurable p) (hq : Measurable q)
    (hp2 : Integrable fun T => ‖p T‖ ^ 2) (hq2 : Integrable fun u => ‖q u‖ ^ 2) (s : ℝ) :
    ∫ T : ℝ, ‖p T * q (T + s)‖ ≤ ((∫ T, ‖p T‖ ^ 2) + ∫ u, ‖q u‖ ^ 2) / 2 := by
  have hq2' : Integrable fun T : ℝ => ‖q (T + s)‖ ^ 2 := hq2.comp_add_right s
  have hq2i : (∫ T : ℝ, ‖q (T + s)‖ ^ 2) = ∫ u, ‖q u‖ ^ 2 :=
    integral_add_right_eq_self (fun u => ‖q u‖ ^ 2) s
  calc ∫ T : ℝ, ‖p T * q (T + s)‖
      ≤ ∫ T : ℝ, (‖p T‖ ^ 2 + ‖q (T + s)‖ ^ 2) / 2 := by
        refine integral_mono (integrable_mul_translate_of_sq hp hq hp2 hq2 s).norm
          ((hp2.add hq2').div_const 2) fun T => ?_
        show ‖p T * q (T + s)‖ ≤ (‖p T‖ ^ 2 + ‖q (T + s)‖ ^ 2) / 2
        rw [norm_mul]
        nlinarith [sq_nonneg (‖p T‖ - ‖q (T + s)‖)]
    _ = ((∫ T, ‖p T‖ ^ 2) + ∫ u, ‖q u‖ ^ 2) / 2 := by
        rw [integral_div, integral_add hp2 hq2', hq2i]

theorem norm_profileCorrelation_le {p q : ℝ → ℂ} (hp : Measurable p) (hq : Measurable q)
    (hp2 : Integrable fun T => ‖p T‖ ^ 2) (hq2 : Integrable fun u => ‖q u‖ ^ 2) (s : ℝ) :
    ‖profileCorrelation p q s‖ ≤ ((∫ T, ‖p T‖ ^ 2) + ∫ u, ‖q u‖ ^ 2) / 2 :=
  (norm_integral_le_integral_norm _).trans (integral_norm_mul_translate_le hp hq hp2 hq2 s)

/-- The correlation is continuous: translation is continuous in `L²`. -/
theorem continuous_profileCorrelation {p q : ℝ → ℂ} (hp : Measurable p) (hq : Measurable q)
    (hp2 : Integrable fun T => ‖p T‖ ^ 2) (hq2 : Integrable fun u => ‖q u‖ ^ 2) :
    Continuous (profileCorrelation p q) := by
  have hpc : Measurable fun T : ℝ => (starRingEnd ℂ) (p T) := Complex.continuous_conj.measurable.comp hp
  have hpm : MemLp (fun T : ℝ => (starRingEnd ℂ) (p T)) 2 volume := by
    rw [memLp_two_iff_integrable_sq_norm hpc.aestronglyMeasurable]
    refine hp2.congr (Eventually.of_forall fun T => ?_)
    show ‖p T‖ ^ 2 = ‖(starRingEnd ℂ) (p T)‖ ^ 2
    rw [Complex.norm_conj]
  have hqm : MemLp q 2 volume := (memLp_two_iff_integrable_sq_norm hq.aestronglyMeasurable).mpr hq2
  have hcont : Continuous fun s : ℝ => inner ℂ (hpm.toLp _)
      (GaloisForLFunctions.RHTower.connesL2Translate (-s) (hqm.toLp q)) :=
    continuous_const.inner
      ((GaloisForLFunctions.RHTower.continuous_connesL2Translate (hqm.toLp q)).comp continuous_neg)
  have heq : profileCorrelation p q = fun s : ℝ => inner ℂ (hpm.toLp _)
      (GaloisForLFunctions.RHTower.connesL2Translate (-s) (hqm.toLp q)) := by
    funext s
    rw [MeasureTheory.L2.inner_def]
    unfold profileCorrelation
    refine integral_congr_ae ?_
    have h3 := (measurePreserving_add_right volume s).quasiMeasurePreserving.ae_eq_comp
      hqm.coeFn_toLp
    filter_upwards [hpm.coeFn_toLp,
      GaloisForLFunctions.RHTower.connesL2Translate_ae (-s) (hqm.toLp q), h3] with T h1 h2 h3
    have h3' : (hqm.toLp q : ℝ → ℂ) (T + s) = q (T + s) := h3
    rw [h1, h2, sub_neg_eq_add, h3', RCLike.inner_apply, Complex.conj_conj]
    first | rfl | exact mul_comm _ _
  rw [heq]
  exact hcont

/-! ### Fubini against a kernel of the difference -/

theorem mul_integral_kernel_eq {p q : ℝ → ℂ} (κ : ℝ → ℝ) (T : ℝ) :
    p T * ∫ u : ℝ, ((κ (u - T) : ℝ) : ℂ) * q u =
      ∫ s : ℝ, p T * ((κ s : ℝ) : ℂ) * q (T + s) := by
  have h := integral_add_left_eq_self (μ := volume) (fun u : ℝ => ((κ (u - T) : ℝ) : ℂ) * q u) T
  rw [← h, ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun s => ?_)
  show p T * (((κ (T + s - T) : ℝ) : ℂ) * q (T + s)) = p T * ((κ s : ℝ) : ℂ) * q (T + s)
  rw [add_sub_cancel_left, mul_assoc]

theorem integrable_mul_kernel_translate {p q : ℝ → ℂ} (hp : Measurable p) (hq : Measurable q)
    (hp2 : Integrable fun T => ‖p T‖ ^ 2) (hq2 : Integrable fun u => ‖q u‖ ^ 2) {κ : ℝ → ℝ}
    (hκc : Continuous κ) (hκ : Integrable κ) :
    Integrable (Function.uncurry fun (T s : ℝ) => p T * ((κ s : ℝ) : ℂ) * q (T + s))
      ((volume : Measure ℝ).prod (volume : Measure ℝ)) := by
  have hmeas : Measurable (Function.uncurry fun (T s : ℝ) => p T * ((κ s : ℝ) : ℂ) * q (T + s)) :=
    ((hp.comp measurable_fst).mul
      (Complex.measurable_ofReal.comp (hκc.measurable.comp measurable_snd))).mul
      (hq.comp (measurable_fst.add measurable_snd))
  rw [integrable_prod_iff' hmeas.aestronglyMeasurable]
  constructor
  · refine Eventually.of_forall fun s => ?_
    refine ((integrable_mul_translate_of_sq hp hq hp2 hq2 s).const_mul ((κ s : ℝ) : ℂ)).congr
      (Eventually.of_forall fun T => ?_)
    show ((κ s : ℝ) : ℂ) * (p T * q (T + s)) = p T * ((κ s : ℝ) : ℂ) * q (T + s)
    ring
  · have hmaj : Integrable fun s : ℝ =>
        |κ s| * (((∫ T, ‖p T‖ ^ 2) + ∫ u, ‖q u‖ ^ 2) / 2) := hκ.abs.mul_const _
    refine hmaj.mono' (hmeas.norm.stronglyMeasurable.integral_prod_left').aestronglyMeasurable
      (Eventually.of_forall fun s => ?_)
    show ‖∫ T : ℝ, ‖p T * ((κ s : ℝ) : ℂ) * q (T + s)‖‖ ≤
      |κ s| * (((∫ T, ‖p T‖ ^ 2) + ∫ u, ‖q u‖ ^ 2) / 2)
    rw [Real.norm_of_nonneg (integral_nonneg fun T => norm_nonneg _)]
    have e : (∫ T : ℝ, ‖p T * ((κ s : ℝ) : ℂ) * q (T + s)‖) =
        |κ s| * ∫ T : ℝ, ‖p T * q (T + s)‖ := by
      rw [← integral_const_mul]
      refine integral_congr_ae (Eventually.of_forall fun T => ?_)
      show ‖p T * ((κ s : ℝ) : ℂ) * q (T + s)‖ = |κ s| * ‖p T * q (T + s)‖
      rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      ring
    rw [e]
    exact mul_le_mul_of_nonneg_left (integral_norm_mul_translate_le hp hq hp2 hq2 s) (abs_nonneg _)

theorem integrable_mul_integral_kernel {p q : ℝ → ℂ} (hp : Measurable p) (hq : Measurable q)
    (hp2 : Integrable fun T => ‖p T‖ ^ 2) (hq2 : Integrable fun u => ‖q u‖ ^ 2) {κ : ℝ → ℝ}
    (hκc : Continuous κ) (hκ : Integrable κ) :
    Integrable fun T : ℝ => p T * ∫ u : ℝ, ((κ (u - T) : ℝ) : ℂ) * q u := by
  refine (integrable_mul_kernel_translate hp hq hp2 hq2 hκc hκ).integral_prod_left.congr
    (Eventually.of_forall fun T => ?_)
  exact (mul_integral_kernel_eq κ T).symm

/-- **Fubini.** A double integral against a kernel of the difference is the integral of the kernel
against the correlation: `∫∫ p(T) κ(u − T) q(u) du dT = ∫ κ(s) (∫ p(T) q(T + s) dT) ds`. -/
theorem integral_mul_integral_kernel {p q : ℝ → ℂ} (hp : Measurable p) (hq : Measurable q)
    (hp2 : Integrable fun T => ‖p T‖ ^ 2) (hq2 : Integrable fun u => ‖q u‖ ^ 2) {κ : ℝ → ℝ}
    (hκc : Continuous κ) (hκ : Integrable κ) :
    ∫ T : ℝ, p T * ∫ u : ℝ, ((κ (u - T) : ℝ) : ℂ) * q u =
      ∫ s : ℝ, ((κ s : ℝ) : ℂ) * profileCorrelation p q s := by
  calc ∫ T : ℝ, p T * ∫ u : ℝ, ((κ (u - T) : ℝ) : ℂ) * q u
      = ∫ T : ℝ, ∫ s : ℝ, p T * ((κ s : ℝ) : ℂ) * q (T + s) :=
        integral_congr_ae (Eventually.of_forall fun T => mul_integral_kernel_eq κ T)
    _ = ∫ s : ℝ, (∫ T : ℝ, p T * ((κ s : ℝ) : ℂ) * q (T + s)) :=
        integral_integral_swap (integrable_mul_kernel_translate hp hq hp2 hq2 hκc hκ)
    _ = ∫ s : ℝ, ((κ s : ℝ) : ℂ) * profileCorrelation p q s := by
        refine integral_congr_ae (Eventually.of_forall fun s => ?_)
        show (∫ T : ℝ, p T * ((κ s : ℝ) : ℂ) * q (T + s)) =
          ((κ s : ℝ) : ℂ) * profileCorrelation p q s
        unfold profileCorrelation
        rw [← integral_const_mul]
        refine integral_congr_ae (Eventually.of_forall fun T => ?_)
        show p T * ((κ s : ℝ) : ℂ) * q (T + s) = ((κ s : ℝ) : ℂ) * (p T * q (T + s))
        ring

/-! ### The tilted heat kernel is an approximate identity -/

theorem continuous_stateHeatKernel (ε : ℝ) : Continuous (stateHeatKernel ε) := by
  unfold stateHeatKernel
  fun_prop

/-- The heat kernel at time one has mass one. -/
theorem integral_stateHeatKernel_one : ∫ y : ℝ, stateHeatKernel 1 y = 1 := by
  have hg := integral_gaussian (1 / 4)
  have hs : Real.sqrt (Real.pi / (1 / 4)) = 2 * Real.sqrt Real.pi := by
    rw [show Real.pi / (1 / 4) = 2 ^ 2 * Real.pi by ring, Real.sqrt_mul (by positivity),
      Real.sqrt_sq (by norm_num)]
  have hfun : (fun y : ℝ => stateHeatKernel 1 y) = fun y : ℝ =>
      (2 * Real.pi)⁻¹ * Real.sqrt Real.pi * Real.exp (-(1 / 4) * y ^ 2) := by
    funext y
    unfold stateHeatKernel
    rw [div_one, show -(y ^ 2 / (4 * 1)) = -(1 / 4) * y ^ 2 by ring]
  rw [hfun, integral_const_mul, hg, hs]
  have hpi : Real.sqrt Real.pi * Real.sqrt Real.pi = Real.pi := Real.mul_self_sqrt Real.pi_pos.le
  have hne : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp
  linear_combination hpi

/-- The heat kernel tilted by an exponential, `k_ε(s) e^{λs}`. -/
def tiltedHeatKernel (ε lam s : ℝ) : ℝ := stateHeatKernel ε s * Real.exp (lam * s)

theorem continuous_tiltedHeatKernel (ε lam : ℝ) : Continuous (tiltedHeatKernel ε lam) := by
  unfold tiltedHeatKernel
  exact (continuous_stateHeatKernel ε).mul (by fun_prop)

theorem integrable_tiltedHeatKernel {ε : ℝ} (hε : 0 < ε) (lam : ℝ) :
    Integrable (tiltedHeatKernel ε lam) := by
  have hb : (0 : ℝ) < 1 / (8 * ε) := by positivity
  have hmaj : Integrable fun s : ℝ => (2 * Real.pi)⁻¹ * Real.sqrt (Real.pi / ε) *
      Real.exp (2 * ε * lam ^ 2) * Real.exp (-(1 / (8 * ε)) * s ^ 2) :=
    (integrable_exp_neg_mul_sq hb).const_mul _
  refine hmaj.mono' (continuous_tiltedHeatKernel ε lam).aestronglyMeasurable
    (Eventually.of_forall fun s => ?_)
  show ‖stateHeatKernel ε s * Real.exp (lam * s)‖ ≤ (2 * Real.pi)⁻¹ * Real.sqrt (Real.pi / ε) *
    Real.exp (2 * ε * lam ^ 2) * Real.exp (-(1 / (8 * ε)) * s ^ 2)
  unfold stateHeatKernel
  have hc : 0 ≤ (2 * Real.pi)⁻¹ * Real.sqrt (Real.pi / ε) := by positivity
  rw [Real.norm_of_nonneg (by positivity), mul_assoc, mul_assoc ((2 * Real.pi)⁻¹ * Real.sqrt (Real.pi / ε)),
    ← Real.exp_add, ← Real.exp_add]
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hc
  have h8 : (0 : ℝ) < 8 * ε := by positivity
  have hsq : 0 ≤ (s - 4 * ε * lam) ^ 2 / (8 * ε) := div_nonneg (sq_nonneg _) h8.le
  have e : -(s ^ 2 / (4 * ε)) + lam * s =
      2 * ε * lam ^ 2 + -(1 / (8 * ε)) * s ^ 2 - (s - 4 * ε * lam) ^ 2 / (8 * ε) := by
    field_simp
    ring
  rw [e]
  linarith

/-- **Approximate identity.** Against a bounded continuous function the tilted heat kernel tends to
the value at the origin as `ε → 0⁺`. -/
theorem tendsto_integral_tiltedHeatKernel_mul {C : ℝ → ℂ} (hC : Continuous C) {M : ℝ}
    (hM : ∀ s, ‖C s‖ ≤ M) (lam : ℝ) :
    Tendsto (fun ε : ℝ => ∫ s : ℝ, ((tiltedHeatKernel ε lam s : ℝ) : ℂ) * C s) (𝓝[>] 0)
      (𝓝 (C 0)) := by
  -- the substitution `s = √ε y` moves the dependence on `ε` into the tilt and the argument of `C`
  have hscale : ∀ ε : ℝ, 0 < ε → (∫ s : ℝ, ((tiltedHeatKernel ε lam s : ℝ) : ℂ) * C s) =
      ∫ y : ℝ, ((stateHeatKernel 1 y * Real.exp (lam * (Real.sqrt ε * y)) : ℝ) : ℂ) *
        C (Real.sqrt ε * y) := by
    intro ε hε
    have hs : 0 < Real.sqrt ε := Real.sqrt_pos.mpr hε
    have hne : Real.sqrt ε ≠ 0 := hs.ne'
    have h := Measure.integral_comp_mul_left
      (fun s : ℝ => ((tiltedHeatKernel ε lam s : ℝ) : ℂ) * C s) (Real.sqrt ε)
    rw [abs_of_pos (inv_pos.mpr hs)] at h
    have h2 : (∫ s : ℝ, ((tiltedHeatKernel ε lam s : ℝ) : ℂ) * C s) =
        Real.sqrt ε • ∫ x : ℝ, ((tiltedHeatKernel ε lam (Real.sqrt ε * x) : ℝ) : ℂ) *
          C (Real.sqrt ε * x) := by
      rw [h, smul_smul, mul_inv_cancel₀ hne, one_smul]
    rw [h2, ← integral_smul]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    show Real.sqrt ε • (((tiltedHeatKernel ε lam (Real.sqrt ε * y) : ℝ) : ℂ) *
        C (Real.sqrt ε * y)) =
      ((stateHeatKernel 1 y * Real.exp (lam * (Real.sqrt ε * y)) : ℝ) : ℂ) * C (Real.sqrt ε * y)
    have hk : Real.sqrt ε * tiltedHeatKernel ε lam (Real.sqrt ε * y) =
        stateHeatKernel 1 y * Real.exp (lam * (Real.sqrt ε * y)) := by
      unfold tiltedHeatKernel stateHeatKernel
      have e1 : (Real.sqrt ε * y) ^ 2 / (4 * ε) = y ^ 2 / (4 * 1) := by
        rw [mul_pow, Real.sq_sqrt hε.le, div_eq_div_iff (by positivity) (by norm_num)]
        ring
      have e2 : Real.sqrt ε * Real.sqrt (Real.pi / ε) = Real.sqrt (Real.pi / 1) := by
        rw [Real.sqrt_div Real.pi_pos.le, div_one, mul_comm, div_mul_cancel₀ _ hne]
      rw [e1]
      linear_combination (2 * Real.pi)⁻¹ * Real.exp (-(y ^ 2 / (4 * 1))) *
        Real.exp (lam * (Real.sqrt ε * y)) * e2
    rw [← hk, Complex.real_smul]
    push_cast
    ring
  have hcontF : ∀ ε : ℝ, Continuous fun y : ℝ =>
      ((stateHeatKernel 1 y * Real.exp (lam * (Real.sqrt ε * y)) : ℝ) : ℂ) *
        C (Real.sqrt ε * y) := by
    intro ε
    have h1 := continuous_stateHeatKernel 1
    fun_prop
  have hlim : Tendsto (fun ε : ℝ => ∫ y : ℝ,
      ((stateHeatKernel 1 y * Real.exp (lam * (Real.sqrt ε * y)) : ℝ) : ℂ) *
        C (Real.sqrt ε * y)) (𝓝[>] 0) (𝓝 (∫ y : ℝ, ((stateHeatKernel 1 y : ℝ) : ℂ) * C 0)) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (fun y : ℝ => (2 * Real.pi)⁻¹ * Real.sqrt (Real.pi / 1) * M * Real.exp (2 * lam ^ 2) *
        Real.exp (-(1 / 8) * y ^ 2)) ?_ ?_ ?_ ?_
    · exact Eventually.of_forall fun ε => (hcontF ε).aestronglyMeasurable
    · have h0 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε := self_mem_nhdsWithin
      have h1 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε < 1 := nhdsWithin_le_nhds (Iio_mem_nhds one_pos)
      filter_upwards [h0, h1] with ε hε0 hε1
      refine Eventually.of_forall fun y => ?_
      have hsq1 : Real.sqrt ε ≤ 1 := Real.sqrt_le_one.mpr hε1.le
      have hsq0 : 0 ≤ Real.sqrt ε := Real.sqrt_nonneg ε
      have hc : 0 ≤ (2 * Real.pi)⁻¹ * Real.sqrt (Real.pi / 1) := by positivity
      have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
      have hexp : -(y ^ 2 / (4 * 1)) + lam * (Real.sqrt ε * y) ≤
          2 * lam ^ 2 + -(1 / 8) * y ^ 2 := by
        have ha : lam * (Real.sqrt ε * y) ≤ |lam| * |y| := by
          calc lam * (Real.sqrt ε * y) ≤ |lam * (Real.sqrt ε * y)| := le_abs_self _
            _ = Real.sqrt ε * (|lam| * |y|) := by
                rw [abs_mul, abs_mul, abs_of_nonneg hsq0]
                ring
            _ ≤ 1 * (|lam| * |y|) :=
                mul_le_mul_of_nonneg_right hsq1 (mul_nonneg (abs_nonneg _) (abs_nonneg _))
            _ = |lam| * |y| := one_mul _
        nlinarith [sq_nonneg (|y| - 4 * |lam|), sq_abs y, sq_abs lam]
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by unfold stateHeatKernel; positivity)]
      unfold stateHeatKernel
      calc (2 * Real.pi)⁻¹ * Real.sqrt (Real.pi / 1) * Real.exp (-(y ^ 2 / (4 * 1))) *
            Real.exp (lam * (Real.sqrt ε * y)) * ‖C (Real.sqrt ε * y)‖
          = (2 * Real.pi)⁻¹ * Real.sqrt (Real.pi / 1) * ‖C (Real.sqrt ε * y)‖ *
              Real.exp (-(y ^ 2 / (4 * 1)) + lam * (Real.sqrt ε * y)) := by
            rw [Real.exp_add]
            ring
        _ ≤ (2 * Real.pi)⁻¹ * Real.sqrt (Real.pi / 1) * M *
              Real.exp (2 * lam ^ 2 + -(1 / 8) * y ^ 2) :=
            mul_le_mul (mul_le_mul_of_nonneg_left (hM _) hc) (Real.exp_le_exp.mpr hexp)
              (Real.exp_pos _).le (mul_nonneg hc hM0)
        _ = (2 * Real.pi)⁻¹ * Real.sqrt (Real.pi / 1) * M * Real.exp (2 * lam ^ 2) *
              Real.exp (-(1 / 8) * y ^ 2) := by
            rw [Real.exp_add]
            ring
    · exact (integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1 / 8)).const_mul _
    · refine Eventually.of_forall fun y => ?_
      have hcont : Continuous fun ε : ℝ =>
          ((stateHeatKernel 1 y * Real.exp (lam * (Real.sqrt ε * y)) : ℝ) : ℂ) *
            C (Real.sqrt ε * y) := by
        fun_prop
      have h := (hcont.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
      simp only [Real.sqrt_zero, zero_mul, mul_zero, Real.exp_zero, mul_one] at h
      exact h
  have hval : (∫ y : ℝ, ((stateHeatKernel 1 y : ℝ) : ℂ) * C 0) = C 0 := by
    rw [integral_mul_const]
    have h1 : (∫ y : ℝ, ((stateHeatKernel 1 y : ℝ) : ℂ)) = ((∫ y : ℝ, stateHeatKernel 1 y : ℝ) : ℂ) :=
      integral_ofReal
    rw [h1, integral_stateHeatKernel_one, Complex.ofReal_one, one_mul]
  rw [hval] at hlim
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (hscale ε hε).symm

/-- **Correlation limit.** For two square-integrable profiles the double integral against the tilted
heat kernel of the difference tends to their pairing. -/
theorem tendsto_integral_mul_integral_tiltedHeatKernel {p q : ℝ → ℂ} (hp : Measurable p)
    (hq : Measurable q) (hp2 : Integrable fun T => ‖p T‖ ^ 2)
    (hq2 : Integrable fun u => ‖q u‖ ^ 2) (lam : ℝ) :
    Tendsto (fun ε : ℝ => ∫ T : ℝ, p T * ∫ u : ℝ, ((tiltedHeatKernel ε lam (u - T) : ℝ) : ℂ) * q u)
      (𝓝[>] 0) (𝓝 (∫ T : ℝ, p T * q T)) := by
  have h := tendsto_integral_tiltedHeatKernel_mul (continuous_profileCorrelation hp hq hp2 hq2)
    (norm_profileCorrelation_le hp hq hp2 hq2) lam
  have h0 : profileCorrelation p q 0 = ∫ T : ℝ, p T * q T := by
    unfold profileCorrelation
    simp only [add_zero]
  rw [h0] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (integral_mul_integral_kernel hp hq hp2 hq2 (continuous_tiltedHeatKernel ε lam)
    (integrable_tiltedHeatKernel hε lam)).symm

/-! ### The profiles of the two pairings -/

/-- A profile in half the weight of the confinement, `e^{−4u} F(u)`. -/
def confinedHalf (F : ℝ → ℝ) (u : ℝ) : ℂ := ((Real.exp (-(4 * u)) * F u : ℝ) : ℂ)

theorem measurable_confinedHalf {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F) :
    Measurable (confinedHalf F) :=
  Complex.measurable_ofReal.comp
    ((by fun_prop : Measurable fun u : ℝ => Real.exp (-(4 * u))).mul hF.meas)

theorem integrable_sq_confinedHalf {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F) :
    Integrable fun u => ‖confinedHalf F u‖ ^ 2 := by
  refine hF.exponential.congr (Eventually.of_forall fun u => ?_)
  show F u ^ 2 * Real.exp (-(8 * u)) = ‖((Real.exp (-(4 * u)) * F u : ℝ) : ℂ)‖ ^ 2
  have he : Real.exp (-(8 * u)) = Real.exp (-(4 * u)) * Real.exp (-(4 * u)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [Complex.norm_real, Real.norm_eq_abs, sq_abs, he]
  ring

/-- The pairing with the heated state, with the weight of the confinement split between the two
profiles. -/
theorem cx_mul_heatedState_eq (F G : ℝ → ℝ) (ε T : ℝ) :
    cx G T * ((heatedState ε F T : ℝ) : ℂ) =
      confinedHalf G T *
        ∫ u : ℝ, ((tiltedHeatKernel ε (-4) (u - T) : ℝ) : ℂ) * confinedHalf F u := by
  have h1 : (∫ u : ℝ, ((tiltedHeatKernel ε (-4) (u - T) * (Real.exp (-(4 * u)) * F u) : ℝ) : ℂ)) =
      ((∫ u : ℝ, tiltedHeatKernel ε (-4) (u - T) * (Real.exp (-(4 * u)) * F u) : ℝ) : ℂ) :=
    integral_ofReal
  have h2 : (∫ u : ℝ, ((tiltedHeatKernel ε (-4) (u - T) : ℝ) : ℂ) * confinedHalf F u) =
      ((∫ u : ℝ, tiltedHeatKernel ε (-4) (u - T) * (Real.exp (-(4 * u)) * F u) : ℝ) : ℂ) := by
    rw [← h1]
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    show ((tiltedHeatKernel ε (-4) (u - T) : ℝ) : ℂ) * ((Real.exp (-(4 * u)) * F u : ℝ) : ℂ) =
      ((tiltedHeatKernel ε (-4) (u - T) * (Real.exp (-(4 * u)) * F u) : ℝ) : ℂ)
    rw [Complex.ofReal_mul (tiltedHeatKernel ε (-4) (u - T))]
  rw [h2]
  show ((G T : ℝ) : ℂ) * ((heatedState ε F T : ℝ) : ℂ) =
    ((Real.exp (-(4 * T)) * G T : ℝ) : ℂ) *
      ((∫ u : ℝ, tiltedHeatKernel ε (-4) (u - T) * (Real.exp (-(4 * u)) * F u) : ℝ) : ℂ)
  rw [← Complex.ofReal_mul, ← Complex.ofReal_mul]
  congr 1
  unfold heatedState
  rw [← integral_const_mul, ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  show G T * (stateHeatKernel ε (u - T) * (Real.exp (-(8 * u)) * F u)) =
    Real.exp (-(4 * T)) * G T *
      (tiltedHeatKernel ε (-4) (u - T) * (Real.exp (-(4 * u)) * F u))
  unfold tiltedHeatKernel
  have he : Real.exp (-(8 * u)) =
      Real.exp (-(4 * T)) * (Real.exp (-4 * (u - T)) * Real.exp (-(4 * u))) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  rw [he]
  ring

/-- A profile damped towards the wall, `e^{T} G(T)`. -/
def dampedProfile (G : ℝ → ℝ) (T : ℝ) : ℂ := ((Real.exp T * G T : ℝ) : ℂ)

theorem measurable_dampedProfile {G : ℝ → ℝ} (hG : CriticalHalfLineEnergyDomain G) :
    Measurable (dampedProfile G) :=
  Complex.measurable_ofReal.comp (Real.measurable_exp.mul hG.meas)

theorem integrable_sq_dampedProfile {G : ℝ → ℝ} (hG : CriticalHalfLineEnergyDomain G) :
    Integrable fun T => ‖dampedProfile G T‖ ^ 2 := by
  refine hG.sq.mono' ((measurable_dampedProfile hG).norm.pow_const 2).aestronglyMeasurable
    (Eventually.of_forall fun T => ?_)
  show ‖‖((Real.exp T * G T : ℝ) : ℂ)‖ ^ 2‖ ≤ G T ^ 2
  rw [Real.norm_of_nonneg (sq_nonneg _), Complex.norm_real, Real.norm_eq_abs, sq_abs, mul_pow]
  rcases le_or_gt 0 T with hT | hT
  · rw [hG.support T hT]
    simp
  · have h1 : Real.exp T ≤ 1 := Real.exp_le_one_iff.mpr hT.le
    have h2 : Real.exp T ^ 2 ≤ 1 := pow_le_one₀ (Real.exp_pos T).le h1
    nlinarith [sq_nonneg (G T)]

/-- The datum of the continuation beyond the wall, extended by zero to the left half-line:
`e^{−x} F⁺(x)` on `x > 0`. -/
def beyondWallDatum (W₀ : ℝ) {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F) : ℝ → ℂ :=
  Set.indicator (Ioi (0 : ℝ)) (unitLeftDatum W₀ hF : ℝ → ℂ)

theorem measurable_beyondWallDatum (W₀ : ℝ) {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F) :
    Measurable (beyondWallDatum W₀ hF) :=
  (Lp.stronglyMeasurable (unitLeftDatum W₀ hF)).measurable.indicator measurableSet_Ioi

theorem integrable_sq_beyondWallDatum (W₀ : ℝ) {F : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) :
    Integrable fun x => ‖beyondWallDatum W₀ hF x‖ ^ 2 := by
  have hD : MemLp (unitLeftDatum W₀ hF : ℝ → ℂ) 2 (volume.restrict (Ioi (0 : ℝ))) :=
    Lp.memLp (unitLeftDatum W₀ hF)
  have h1 : IntegrableOn (fun x : ℝ => ‖(unitLeftDatum W₀ hF : ℝ → ℂ) x‖ ^ 2) (Ioi (0 : ℝ)) :=
    (memLp_two_iff_integrable_sq_norm hD.aestronglyMeasurable).mp hD
  refine ((integrable_indicator_iff measurableSet_Ioi).mpr h1).congr
    (Eventually.of_forall fun x => ?_)
  show Set.indicator (Ioi (0 : ℝ)) (fun x : ℝ => ‖(unitLeftDatum W₀ hF : ℝ → ℂ) x‖ ^ 2) x =
    ‖Set.indicator (Ioi (0 : ℝ)) (unitLeftDatum W₀ hF : ℝ → ℂ) x‖ ^ 2
  by_cases hx : x ∈ Ioi (0 : ℝ)
  · rw [Set.indicator_apply, Set.indicator_apply, if_pos hx, if_pos hx]
  · rw [Set.indicator_apply, Set.indicator_apply, if_neg hx, if_neg hx, norm_zero]
    norm_num

/-- The pairing with the heated profile beyond the wall, with the growth of `F⁺` moved to the
kernel and the test. -/
theorem cx_mul_heatedBeyondWall_eq (W₀ : ℝ) {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F)
    (G : ℝ → ℝ) (ε T : ℝ) :
    cx G T * heatedBeyondWall ε W₀ hF T =
      dampedProfile G T *
        ∫ u : ℝ, ((tiltedHeatKernel ε 1 (u - T) : ℝ) : ℂ) * beyondWallDatum W₀ hF u := by
  have h1 : (∫ u : ℝ, ((tiltedHeatKernel ε 1 (u - T) : ℝ) : ℂ) * beyondWallDatum W₀ hF u) =
      ∫ u : ℝ in Ioi (0 : ℝ), ((tiltedHeatKernel ε 1 (u - T) : ℝ) : ℂ) *
        (unitLeftDatum W₀ hF : ℝ → ℂ) u := by
    rw [← integral_indicator measurableSet_Ioi]
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    show ((tiltedHeatKernel ε 1 (u - T) : ℝ) : ℂ) *
        Set.indicator (Ioi (0 : ℝ)) (unitLeftDatum W₀ hF : ℝ → ℂ) u =
      Set.indicator (Ioi (0 : ℝ)) (fun u : ℝ => ((tiltedHeatKernel ε 1 (u - T) : ℝ) : ℂ) *
        (unitLeftDatum W₀ hF : ℝ → ℂ) u) u
    by_cases hu : u ∈ Ioi (0 : ℝ)
    · rw [Set.indicator_apply, Set.indicator_apply, if_pos hu, if_pos hu]
    · rw [Set.indicator_apply, Set.indicator_apply, if_neg hu, if_neg hu, mul_zero]
  rw [h1]
  unfold heatedBeyondWall
  rw [← integral_const_mul, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
  have he : Real.exp u = Real.exp T * Real.exp (1 * (u - T)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  show ((G T : ℝ) : ℂ) * (((stateHeatKernel ε (u - T) : ℝ) : ℂ) *
      (Complex.exp (u : ℂ) * (unitLeftDatum W₀ hF : ℝ → ℂ) u)) =
    ((Real.exp T * G T : ℝ) : ℂ) *
      (((stateHeatKernel ε (u - T) * Real.exp (1 * (u - T)) : ℝ) : ℂ) *
        (unitLeftDatum W₀ hF : ℝ → ℂ) u)
  rw [← Complex.ofReal_exp, he]
  push_cast
  ring

theorem integrable_cx_mul_heatedState {F G : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F)
    (hG : CriticalHalfLineEnergyDomain G) {ε : ℝ} (hε : 0 < ε) :
    Integrable fun T : ℝ => cx G T * ((heatedState ε F T : ℝ) : ℂ) := by
  refine (integrable_mul_integral_kernel (measurable_confinedHalf hG) (measurable_confinedHalf hF)
    (integrable_sq_confinedHalf hG) (integrable_sq_confinedHalf hF)
    (continuous_tiltedHeatKernel ε (-4)) (integrable_tiltedHeatKernel hε (-4))).congr
    (Eventually.of_forall fun T => ?_)
  exact (cx_mul_heatedState_eq F G ε T).symm

theorem integrable_cx_mul_heatedBeyondWall (W₀ : ℝ) {F G : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) (hG : CriticalHalfLineEnergyDomain G) {ε : ℝ}
    (hε : 0 < ε) :
    Integrable fun T : ℝ => cx G T * heatedBeyondWall ε W₀ hF T := by
  refine (integrable_mul_integral_kernel (measurable_dampedProfile hG)
    (measurable_beyondWallDatum W₀ hF) (integrable_sq_dampedProfile hG)
    (integrable_sq_beyondWallDatum W₀ hF) (continuous_tiltedHeatKernel ε 1)
    (integrable_tiltedHeatKernel hε 1)).congr (Eventually.of_forall fun T => ?_)
  exact (cx_mul_heatedBeyondWall_eq W₀ hF G ε T).symm

/-- As the heat is switched off, the pairing with the heated state is the confinement pairing. -/
theorem tendsto_integral_cx_mul_heatedState {F G : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F)
    (hG : CriticalHalfLineEnergyDomain G) :
    Tendsto (fun ε : ℝ => ∫ T : ℝ, cx G T * ((heatedState ε F T : ℝ) : ℂ)) (𝓝[>] 0)
      (𝓝 (statePairing F (cx G))) := by
  have h := tendsto_integral_mul_integral_tiltedHeatKernel (measurable_confinedHalf hG)
    (measurable_confinedHalf hF) (integrable_sq_confinedHalf hG) (integrable_sq_confinedHalf hF)
    (-4)
  have hlim : (∫ T : ℝ, confinedHalf G T * confinedHalf F T) = statePairing F (cx G) := by
    unfold statePairing
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    show ((Real.exp (-(4 * u)) * G u : ℝ) : ℂ) * ((Real.exp (-(4 * u)) * F u : ℝ) : ℂ) =
      ((G u : ℝ) : ℂ) * ((Real.exp (-(8 * u)) * F u : ℝ) : ℂ)
    have he : Real.exp (-(8 * u)) = Real.exp (-(4 * u)) * Real.exp (-(4 * u)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [he]
    push_cast
    ring
  rw [hlim] at h
  refine h.congr fun ε => ?_
  exact (integral_congr_ae (Eventually.of_forall fun T => cx_mul_heatedState_eq F G ε T)).symm

/-- As the heat is switched off, the profile beyond the wall is not seen from the left of the
wall. -/
theorem tendsto_integral_cx_mul_heatedBeyondWall (W₀ : ℝ) {F G : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) (hG : CriticalHalfLineEnergyDomain G) :
    Tendsto (fun ε : ℝ => ∫ T : ℝ, cx G T * heatedBeyondWall ε W₀ hF T) (𝓝[>] 0) (𝓝 0) := by
  have h := tendsto_integral_mul_integral_tiltedHeatKernel (measurable_dampedProfile hG)
    (measurable_beyondWallDatum W₀ hF) (integrable_sq_dampedProfile hG)
    (integrable_sq_beyondWallDatum W₀ hF) 1
  have hlim : (∫ T : ℝ, dampedProfile G T * beyondWallDatum W₀ hF T) = 0 := by
    have e : (fun T : ℝ => dampedProfile G T * beyondWallDatum W₀ hF T) = fun _ => 0 := by
      funext T
      rcases le_or_gt T 0 with hT | hT
      · have hn : T ∉ Ioi (0 : ℝ) := not_lt.mpr hT
        show dampedProfile G T * Set.indicator (Ioi (0 : ℝ)) (unitLeftDatum W₀ hF : ℝ → ℂ) T = 0
        rw [Set.indicator_apply, if_neg hn, mul_zero]
      · show ((Real.exp T * G T : ℝ) : ℂ) * beyondWallDatum W₀ hF T = 0
        rw [hG.support T hT.le, mul_zero, Complex.ofReal_zero, zero_mul]
    rw [e, integral_zero]
  rw [hlim] at h
  refine h.congr fun ε => ?_
  exact (integral_congr_ae
    (Eventually.of_forall fun T => cx_mul_heatedBeyondWall_eq W₀ hF G ε T)).symm

/-! ### The zero pairing of the state with a profile of the domain -/

theorem integrable_cexp_neg_mul_cx {G : ℝ → ℝ} (hG : CriticalHalfLineEnergyDomain G) {z : ℂ}
    (hz : z.re < 4) : Integrable fun T : ℝ => Complex.exp (-z * (T : ℂ)) * cx G T := by
  have hmaj := integrable_abs_mul_exp_of_domain hG (c := -z.re) (by linarith)
  refine hmaj.mono' ?_ (Eventually.of_forall fun T => ?_)
  · exact ((Complex.continuous_exp.comp
      (continuous_const.mul Complex.continuous_ofReal)).aestronglyMeasurable).mul
      (Complex.measurable_ofReal.comp hG.meas).aestronglyMeasurable
  · show ‖Complex.exp (-z * (T : ℂ)) * ((G T : ℝ) : ℂ)‖ ≤ |G T| * Real.exp (-z.re * T)
    have hre : (-z * (T : ℂ)).re = -z.re * T := by simp
    rw [norm_mul, Complex.norm_exp, hre, Complex.norm_real, Real.norm_eq_abs, mul_comm]

/-- **The weighted zero pairing is the pairing with the heated zero series.** For the critical state,
a profile `G` of the domain and `ε > 0`:
`Σ_z L F(z) L G(−z) e^{εz²} = a ∫ G(T) (k_ε * F⁺ − k_ε * (e^{−8u} F))(T) dT`. -/
theorem criticalState_hasSum_zeroPairing_heated {W₀ : ℝ} (hW : 0 < W₀)
    (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) {G : ℝ → ℝ}
    (hG : CriticalHalfLineEnergyDomain G) {ε : ℝ} (hε : 0 < ε) :
    HasSum (fun q : XiZeroCopy => negativeHalfLineLaplace (cx F) (centredZero q) *
        negativeHalfLineLaplace (cx G) (-centredZero q) *
          Complex.exp ((ε : ℂ) * centredZero q ^ 2))
      (∫ T : ℝ, cx G T * ((criticalAliasCoefficient W₀ : ℂ) *
        (heatedBeyondWall ε W₀ (criticalHalfLineEnergyDomain_of_groundState hF) T -
          ((heatedState ε F T : ℝ) : ℂ)))) := by
  have hsplit : ∀ (T : ℝ) (z : ℂ), stateHeatSymbol ε T z =
      Complex.exp ((ε : ℂ) * z ^ 2) * Complex.exp (-z * (T : ℂ)) := by
    intro T z
    unfold stateHeatSymbol
    rw [sub_eq_add_neg, Complex.exp_add, neg_mul]
  have hzre : ∀ q : XiZeroCopy, (centredZero q).re < 1 / 2 := fun q =>
    (abs_lt.mp (abs_re_centredZero_lt q)).2
  -- each term is an integral over `T`
  have hterm : ∀ q : XiZeroCopy,
      (∫ T : ℝ, cx G T * (negativeHalfLineLaplace (cx F) (centredZero q) *
        stateHeatSymbol ε T (centredZero q))) =
      negativeHalfLineLaplace (cx F) (centredZero q) *
        negativeHalfLineLaplace (cx G) (-centredZero q) *
          Complex.exp ((ε : ℂ) * centredZero q ^ 2) := by
    intro q
    have e : (fun T : ℝ => cx G T * (negativeHalfLineLaplace (cx F) (centredZero q) *
          stateHeatSymbol ε T (centredZero q))) = fun T : ℝ =>
        (negativeHalfLineLaplace (cx F) (centredZero q) *
          Complex.exp ((ε : ℂ) * centredZero q ^ 2)) *
          (Complex.exp (-centredZero q * (T : ℂ)) * cx G T) := by
      funext T
      rw [hsplit]
      ring
    have hL : negativeHalfLineLaplace (cx G) (-centredZero q) =
        ∫ T : ℝ, Complex.exp (-centredZero q * (T : ℂ)) * cx G T := rfl
    rw [e, integral_const_mul, hL]
    ring
  have hint : ∀ q : XiZeroCopy, Integrable fun T : ℝ => cx G T *
      (negativeHalfLineLaplace (cx F) (centredZero q) * stateHeatSymbol ε T (centredZero q)) := by
    intro q
    refine ((integrable_cexp_neg_mul_cx hG (z := centredZero q) (by linarith [hzre q])).const_mul
      (negativeHalfLineLaplace (cx F) (centredZero q) *
        Complex.exp ((ε : ℂ) * centredZero q ^ 2))).congr (Eventually.of_forall fun T => ?_)
    show negativeHalfLineLaplace (cx F) (centredZero q) *
        Complex.exp ((ε : ℂ) * centredZero q ^ 2) *
        (Complex.exp (-centredZero q * (T : ℂ)) * cx G T) =
      cx G T * (negativeHalfLineLaplace (cx F) (centredZero q) *
        stateHeatSymbol ε T (centredZero q))
    rw [hsplit]
    ring
  -- the terms are dominated by the heated zero series at `T = 0` times an exponential moment of `G`
  have hGm := integrable_abs_mul_exp_of_domain hG (c := -(1 / 2)) (by norm_num)
  have hsum0 := (criticalState_hasSum_heated_zeroSeries hW hthreshold hF hε 0).summable.norm
  have key : ∀ a b g x y : ℝ, 0 ≤ a → 0 ≤ b → g * x ≤ g * y →
      g * (a * (b * x)) ≤ a * b * (g * y) := by
    intro a b g x y ha hb h
    calc g * (a * (b * x)) = a * b * (g * x) := by ring
      _ ≤ a * b * (g * y) := mul_le_mul_of_nonneg_left h (mul_nonneg ha hb)
  have hbound : ∀ q : XiZeroCopy,
      (∫ T : ℝ, ‖cx G T * (negativeHalfLineLaplace (cx F) (centredZero q) *
        stateHeatSymbol ε T (centredZero q))‖) ≤
      ‖negativeHalfLineLaplace (cx F) (centredZero q) * stateHeatSymbol ε 0 (centredZero q)‖ *
        ∫ u : ℝ, |G u| * Real.exp (-(1 / 2) * u) := by
    intro q
    rw [← integral_const_mul]
    refine integral_mono (hint q).norm (hGm.const_mul _) fun T => ?_
    have h0 : stateHeatSymbol ε 0 (centredZero q) =
        Complex.exp ((ε : ℂ) * centredZero q ^ 2) := by
      unfold stateHeatSymbol
      rw [Complex.ofReal_zero, mul_zero, sub_zero]
    have hre : (-centredZero q * (T : ℂ)).re = -(centredZero q).re * T := by simp
    have hgx : |G T| * Real.exp (-(centredZero q).re * T) ≤
        |G T| * Real.exp (-(1 / 2) * T) := by
      rcases le_or_gt 0 T with hT | hT
      · rw [hG.support T hT, abs_zero, zero_mul, zero_mul]
      · refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (abs_nonneg _)
        nlinarith [mul_pos (sub_pos.mpr (hzre q)) (neg_pos.mpr hT)]
    show ‖((G T : ℝ) : ℂ) * (negativeHalfLineLaplace (cx F) (centredZero q) *
        stateHeatSymbol ε T (centredZero q))‖ ≤
      ‖negativeHalfLineLaplace (cx F) (centredZero q) * stateHeatSymbol ε 0 (centredZero q)‖ *
        (|G T| * Real.exp (-(1 / 2) * T))
    rw [hsplit, h0, norm_mul, norm_mul, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      Complex.norm_exp (-centredZero q * (T : ℂ)), hre]
    exact key _ _ _ _ _ (norm_nonneg _) (norm_nonneg _) hgx
  have hsum : Summable fun q : XiZeroCopy =>
      ∫ T : ℝ, ‖cx G T * (negativeHalfLineLaplace (cx F) (centredZero q) *
        stateHeatSymbol ε T (centredZero q))‖ :=
    Summable.of_nonneg_of_le (fun q => integral_nonneg fun T => norm_nonneg _) hbound
      (hsum0.mul_right _)
  have h := hasSum_integral_of_summable_integral_norm hint hsum
  have htsum : ∀ T : ℝ, (∑' q : XiZeroCopy, cx G T *
      (negativeHalfLineLaplace (cx F) (centredZero q) * stateHeatSymbol ε T (centredZero q))) =
      cx G T * ((criticalAliasCoefficient W₀ : ℂ) *
        (heatedBeyondWall ε W₀ (criticalHalfLineEnergyDomain_of_groundState hF) T -
          ((heatedState ε F T : ℝ) : ℂ))) := by
    intro T
    rw [tsum_mul_left, (criticalState_hasSum_heated_zeroSeries hW hthreshold hF hε T).tsum_eq]
  simp only [hterm, htsum] at h
  exact h

/-- Weil's bare form of the state and a profile of the domain is minus the confinement pairing:
the weak equation of the state. -/
theorem criticalState_bareMixedEnergy_eq_neg_statePairing {W₀ : ℝ} (hW : 0 < W₀)
    (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) {G : ℝ → ℝ}
    (hG : CriticalHalfLineEnergyDomain G) :
    ((bareMixedEnergy F G : ℝ) : ℂ) =
      -((criticalAliasCoefficient W₀ : ℂ) * statePairing F (cx G)) := by
  have hd := criticalHalfLineEnergyDomain_of_groundState hF
  have hw := criticalHalfLineMixedEnergy_groundState_eq_zero hW hthreshold hF hG
  rw [criticalHalfLineMixedEnergy_eq_bare_add] at hw
  have hb : bareMixedEnergy F G = -(criticalAliasCoefficient W₀ *
      ∫ u in Iio (0 : ℝ), F u * G u * Real.exp (-(8 * u))) := by linarith
  rw [statePairing_cx hd.support G, hb]
  push_cast
  ring

/-- **The explicit formula at the state against the whole domain.** For the critical state `F` and
every profile `G` of the energy domain, with Gaussian summation over the centred zeros:
`lim_{ε→0⁺} Σ_z L F(z) L G(−z) e^{εz²} = W(F, G)`. -/
theorem criticalState_tendsto_zeroPairing {W₀ : ℝ} (hW : 0 < W₀)
    (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) {G : ℝ → ℝ}
    (hG : CriticalHalfLineEnergyDomain G) :
    Tendsto (fun ε : ℝ => ∑' q : XiZeroCopy, negativeHalfLineLaplace (cx F) (centredZero q) *
        negativeHalfLineLaplace (cx G) (-centredZero q) *
          Complex.exp ((ε : ℂ) * centredZero q ^ 2))
      (𝓝[>] 0) (𝓝 ((bareMixedEnergy F G : ℝ) : ℂ)) := by
  have hd := criticalHalfLineEnergyDomain_of_groundState hF
  have h1 := tendsto_integral_cx_mul_heatedState hd hG
  have h2 := tendsto_integral_cx_mul_heatedBeyondWall W₀ hd hG
  have h3 := (h2.sub h1).const_mul (criticalAliasCoefficient W₀ : ℂ)
  have hv : (criticalAliasCoefficient W₀ : ℂ) * (0 - statePairing F (cx G)) =
      ((bareMixedEnergy F G : ℝ) : ℂ) := by
    rw [criticalState_bareMixedEnergy_eq_neg_statePairing hW hthreshold hF hG]
    ring
  rw [hv] at h3
  refine h3.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  rw [(criticalState_hasSum_zeroPairing_heated hW hthreshold hF hG hε).tsum_eq,
    ← integral_sub (integrable_cx_mul_heatedBeyondWall W₀ hd hG hε)
      (integrable_cx_mul_heatedState hd hG hε), ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun T => ?_)
  show (criticalAliasCoefficient W₀ : ℂ) *
      (cx G T * heatedBeyondWall ε W₀ hd T - cx G T * ((heatedState ε F T : ℝ) : ℂ)) =
    cx G T * ((criticalAliasCoefficient W₀ : ℂ) *
      (heatedBeyondWall ε W₀ hd T - ((heatedState ε F T : ℝ) : ℂ)))
  ring

/-! ### The negative vector -/

/-- A zero on the line contributes a nonnegative term: for a real profile and `Re z = 0`,
`L F(z) L F(−z) e^{εz²} = |L F(z)|² e^{−ε (Im z)²}`. -/
theorem laplace_mul_laplace_neg_of_re_eq_zero (F : ℝ → ℝ) {z : ℂ} (hz : z.re = 0) (ε : ℝ) :
    negativeHalfLineLaplace (cx F) z * negativeHalfLineLaplace (cx F) (-z) *
        Complex.exp ((ε : ℂ) * z ^ 2) =
      ((‖negativeHalfLineLaplace (cx F) z‖ ^ 2 * Real.exp (-(ε * z.im ^ 2)) : ℝ) : ℂ) := by
  have hneg : -z = (starRingEnd ℂ) z := by
    apply Complex.ext
    · rw [Complex.neg_re, Complex.conj_re, hz, neg_zero]
    · rw [Complex.neg_im, Complex.conj_im]
  have hsq : (ε : ℂ) * z ^ 2 = ((-(ε * z.im ^ 2) : ℝ) : ℂ) := by
    apply Complex.ext
    · rw [sq, Complex.re_ofReal_mul, Complex.mul_re, hz, Complex.ofReal_re]
      ring
    · rw [sq, Complex.im_ofReal_mul, Complex.mul_im, hz, Complex.ofReal_im]
      ring
  have hconj : negativeHalfLineLaplace (cx F) (-z) =
      (starRingEnd ℂ) (negativeHalfLineLaplace (cx F) z) := by
    rw [hneg]
    exact negativeHalfLineLaplace_real_conj F z
  rw [hconj, hsq, Complex.mul_conj, ← Complex.ofReal_exp, Complex.normSq_eq_norm_sq,
    ← Complex.ofReal_mul]

/-- **The zero values of the state are a negative vector.** With Gaussian summation,
`Σ_z L F(z) L F(−z) e^{εz²} → −a ∫ F² e^{−8u}` as `ε → 0⁺`. -/
theorem criticalState_tendsto_zeroNorm {W₀ : ℝ} (hW : 0 < W₀)
    (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) :
    Tendsto (fun ε : ℝ => ∑' q : XiZeroCopy, negativeHalfLineLaplace (cx F) (centredZero q) *
        negativeHalfLineLaplace (cx F) (-centredZero q) *
          Complex.exp ((ε : ℂ) * centredZero q ^ 2))
      (𝓝[>] 0)
      (𝓝 ((-(criticalAliasCoefficient W₀ * ∫ u : ℝ, F u ^ 2 * Real.exp (-(8 * u))) : ℝ) : ℂ)) := by
  have hd := criticalHalfLineEnergyDomain_of_groundState hF
  have h := criticalState_tendsto_zeroPairing hW hthreshold hF hd
  have hw := criticalHalfLineMixedEnergy_groundState_eq_zero hW hthreshold hF hd
  rw [criticalHalfLineMixedEnergy_eq_bare_add] at hw
  have h2 : (∫ u in Iio (0 : ℝ), F u * F u * Real.exp (-(8 * u))) =
      ∫ u : ℝ, F u ^ 2 * Real.exp (-(8 * u)) := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero fun u hu => by
      have hu' : 0 ≤ u := not_lt.mp fun h => hu (mem_Iio.mpr h)
      rw [hd.support u hu', zero_mul, zero_mul]]
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    show F u * F u * Real.exp (-(8 * u)) = F u ^ 2 * Real.exp (-(8 * u))
    ring
  have hb : bareMixedEnergy F F =
      -(criticalAliasCoefficient W₀ * ∫ u : ℝ, F u ^ 2 * Real.exp (-(8 * u))) := by
    rw [← h2]
    linarith
  rw [hb] at h
  exact h

/-- The limit of the zero norm of the state is negative: the confinement mass is at least one. -/
theorem criticalState_zeroNorm_limit_neg {W₀ : ℝ} (hW : 0 < W₀) {F : ℝ → ℝ}
    (hF : IsCriticalHalfLineGroundState W₀ F) :
    -(criticalAliasCoefficient W₀ * ∫ u : ℝ, F u ^ 2 * Real.exp (-(8 * u))) < 0 := by
  have hd := criticalHalfLineEnergyDomain_of_groundState hF
  have ha := criticalAliasCoefficient_positive hW
  have hone : (1 : ℝ) ≤ ∫ u : ℝ, F u ^ 2 * Real.exp (-(8 * u)) := by
    rw [← hF.2.2.2.1]
    refine integral_mono hd.sq hd.exponential fun u => ?_
    show F u ^ 2 ≤ F u ^ 2 * Real.exp (-(8 * u))
    rcases le_or_gt 0 u with hu | hu
    · rw [hd.support u hu]
      simp
    · have h1 : 1 ≤ Real.exp (-(8 * u)) := Real.one_le_exp (by linarith)
      nlinarith [sq_nonneg (F u)]
  nlinarith

end GaloisForLFunctions.ExclusionOfTheCriticalState
