import GaloisForLFunctions.ExclusionOfTheCriticalState.TheEnergyDomainIsStableUnderLipschitzMultipliers
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.CausalReflection.ConfiningMinimizerExponentialBarriers
import GaloisForLFunctions.ArithmeticIncidencePositivity.ArchimedeanBumpBridgeAndSelfEnergyAsymptotic

/-!
# The state obeys a comparison principle at the wall

Let `F` minimize the confined half-line energy at a ratio `R > 0`, `|F| ≤ C` almost everywhere.
Write `ω` for the Lévy density of the Gamma form and, for a cutoff `δ > 0`,

`𝔏_δ X(u) = ∫_{|t| > δ} ω(|t|) (X(u) − X(u − t)) dt` (`cutoffLevy`).

**Comparison principle** (`IsHalfLineEnergyMinimizer.exists_wall_comparison`). There is a constant
`M`, depending only on `F`, with the following property. Let `0 < k ≤ 1/2` and let `ψ` be a
bounded profile of the energy domain carried by `(−k, 0)` with `ψ ≥ C` on `(−k, −k/2]`. Compare
`F` on `(−k, 0)` with the function equal to `ψ` there and to `F` left of `−k`: if for all small `δ`

`𝔏_δ ψ(u) − ∫_{|t| > δ} ω(|t|) (F 1_{(−∞, −k]})(u − t) dt ≥ M + 1` for `−k/2 < u ≤ −δ`,

then `F ≤ ψ` almost everywhere on `(−k, 0)`.

Mechanism. The positive part `G = (F − ψ)₊`, cut off left of `−k/2`, lies in the energy domain
and is an admissible test. Where `G > 0` one has `F = G + ψ`, and almost everywhere
`F ≤ G + ψ + F 1_{(−∞, −k]}`; the kernel being nonnegative,
`G · 𝔏_δ F ≥ G · 𝔏_δ G + G · (𝔏_δ ψ − ω_δ ⋆ F 1_{(−∞, −k]})`. The integral of `G · 𝔏_δ X` is the
jump form of `(X, G)` over the lags `h > δ`, nonnegative for `X = G`. The weak equation bounds
the full jump form of `(F, G)` by `M ∫ G`: the mass, pole and confinement terms are bounded
multiples of `∫ G`, and of the prime row only the backward shifts meet `(−1/2, 0)`, where the
exponential decay of `F` makes them summable. Letting `δ → 0` (the strip `(−δ, 0)` costs
`O(δ log(1/δ))`) gives `(M + 1) ∫ G ≤ M ∫ G`, so `G = 0`.
-/

noncomputable section
open MeasureTheory Set Filter Topology

namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri
  CriticalArithmeticCorrelationTheory HTGeometry _root_.RHTower

/-! ### Elementary integrability -/

theorem integrable_mul_of_integrable_sq {X G : ℝ → ℝ} (hXm : Measurable X) (hGm : Measurable G)
    (hX2 : Integrable fun u => X u ^ 2) (hG2 : Integrable fun u => G u ^ 2) :
    Integrable fun u => X u * G u := by
  refine Integrable.mono' (hX2.add hG2) (hXm.mul hGm).aestronglyMeasurable
    (Eventually.of_forall fun u => ?_)
  rw [Real.norm_eq_abs, abs_mul]
  show |X u| * |G u| ≤ X u ^ 2 + G u ^ 2
  nlinarith only [sq_nonneg (|X u| - |G u|), sq_abs (X u), sq_abs (G u),
    mul_nonneg (abs_nonneg (X u)) (abs_nonneg (G u))]

theorem integrable_sq_add_of_integrable_sq {X Y : ℝ → ℝ} (hXm : Measurable X)
    (hYm : Measurable Y) (hX2 : Integrable fun u => X u ^ 2) (hY2 : Integrable fun u => Y u ^ 2) :
    Integrable fun u => (X u + Y u) ^ 2 := by
  refine Integrable.mono' ((hX2.const_mul 2).add (hY2.const_mul 2))
    ((hXm.add hYm).pow_const 2).aestronglyMeasurable (Eventually.of_forall fun u => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  show (X u + Y u) ^ 2 ≤ 2 * X u ^ 2 + 2 * Y u ^ 2
  nlinarith only [sq_nonneg (X u - Y u)]

theorem ae_comp_const_sub {p : ℝ → Prop} (h : ∀ᵐ v : ℝ, p v) (u : ℝ) : ∀ᵐ t : ℝ, p (u - t) := by
  have h1 : ∀ᵐ x : ℝ, p (x - -u) :=
    (measurePreserving_sub_right volume (-u)).quasiMeasurePreserving.ae h
  have h2 : ∀ᵐ t : ℝ, p (-t - -u) :=
    (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.ae h1
  filter_upwards [h2] with t ht
  have e : -t - -u = u - t := by ring
  rwa [e] at ht

/-- The integral of an integrable function over `(0, δ]` tends to zero with `δ`. -/
theorem tendsto_setIntegral_Ioc_zero {f : ℝ → ℝ} (hf : IntegrableOn f (Ioi 0)) :
    Tendsto (fun δ : ℝ => ∫ h in Ioc 0 δ, f h) (𝓝[>] 0) (𝓝 0) := by
  have e : ∀ δ : ℝ, (volume.restrict (Ioi (0 : ℝ))) (Ioc 0 δ) = ENNReal.ofReal δ := fun δ => by
    rw [Measure.restrict_apply measurableSet_Ioc, inter_eq_left.mpr Ioc_subset_Ioi_self,
      Real.volume_Ioc, sub_zero]
  have hμ : Tendsto ((volume.restrict (Ioi (0 : ℝ))) ∘ fun δ : ℝ => Ioc 0 δ) (𝓝[>] 0) (𝓝 0) := by
    have e' : ((volume.restrict (Ioi (0 : ℝ))) ∘ fun δ : ℝ => Ioc 0 δ) =
        fun δ => ENNReal.ofReal δ := funext e
    rw [e']
    have h0 : Tendsto (fun δ : ℝ => ENNReal.ofReal δ) (𝓝 0) (𝓝 (ENNReal.ofReal 0)) :=
      ENNReal.continuous_ofReal.tendsto 0
    rw [ENNReal.ofReal_zero] at h0
    exact h0.mono_left nhdsWithin_le_nhds
  have h := Integrable.tendsto_setIntegral_nhds_zero (μ := volume.restrict (Ioi (0 : ℝ))) hf hμ
  refine h.congr fun δ => ?_
  rw [Measure.restrict_restrict measurableSet_Ioc, inter_eq_left.mpr Ioc_subset_Ioi_self]

/-! ### The symmetric cutoff kernel -/

/-- The Lévy density on both sides of the origin with the lags `|t| ≤ δ` removed. -/
def symCutoffKernel (δ t : ℝ) : ℝ :=
  halfLineGammaCutoffKernel δ t + halfLineGammaCutoffKernel δ (-t)

theorem measurable_symCutoffKernel (δ : ℝ) : Measurable (symCutoffKernel δ) :=
  (measurable_halfLineGammaCutoffKernel δ).add
    ((measurable_halfLineGammaCutoffKernel δ).comp measurable_neg)

theorem symCutoffKernel_nonneg {δ : ℝ} (hδ : 0 < δ) (t : ℝ) : 0 ≤ symCutoffKernel δ t :=
  add_nonneg (halfLineGammaCutoffKernel_nonneg hδ t) (halfLineGammaCutoffKernel_nonneg hδ (-t))

theorem integrable_symCutoffKernel {δ : ℝ} (hδ : 0 < δ) : Integrable (symCutoffKernel δ) :=
  (integrable_halfLineGammaCutoffKernel hδ).add (integrable_halfLineGammaCutoffKernel hδ).comp_neg

theorem integrable_sq_symCutoffKernel {δ : ℝ} (hδ : 0 < δ) :
    Integrable fun t => symCutoffKernel δ t ^ 2 :=
  integrable_sq_add_of_integrable_sq (measurable_halfLineGammaCutoffKernel δ)
    ((measurable_halfLineGammaCutoffKernel δ).comp measurable_neg)
    (integrable_sq_halfLineGammaCutoffKernel hδ) (integrable_sq_halfLineGammaCutoffKernel hδ).comp_neg

/-- Integration against the symmetric kernel is integration over the lags `h > δ` on both
sides. -/
theorem integral_symCutoffKernel_mul {δ : ℝ} {f : ℝ → ℝ}
    (hf : Integrable fun t => halfLineGammaCutoffKernel δ t * f t)
    (hf' : Integrable fun t => halfLineGammaCutoffKernel δ t * f (-t)) :
    ∫ t, symCutoffKernel δ t * f t =
      (∫ h in Ioi δ, archLevyDensity h * f h) + ∫ h in Ioi δ, archLevyDensity h * f (-h) := by
  have hneg : Integrable fun t => halfLineGammaCutoffKernel δ (-t) * f t := by
    have h := hf'.comp_neg
    simpa only [neg_neg] using h
  have e : (fun t => symCutoffKernel δ t * f t) = fun t =>
      halfLineGammaCutoffKernel δ t * f t + halfLineGammaCutoffKernel δ (-t) * f t := by
    funext t
    unfold symCutoffKernel
    ring
  have h2 : ∫ t, halfLineGammaCutoffKernel δ (-t) * f t =
      ∫ h in Ioi δ, archLevyDensity h * f (-h) := by
    rw [← integral_halfLineGammaCutoffKernel_mul δ fun t => f (-t)]
    have h := integral_neg_eq_self (fun t => halfLineGammaCutoffKernel δ t * f (-t)) volume
    simpa only [neg_neg] using h
  rw [e, integral_add hf hneg, integral_halfLineGammaCutoffKernel_mul, h2]

theorem integral_symCutoffKernel {δ : ℝ} (hδ : 0 < δ) :
    ∫ t, symCutoffKernel δ t = 2 * ∫ h in Ioi δ, archLevyDensity h := by
  have hK : Integrable fun t => halfLineGammaCutoffKernel δ t * (fun _ : ℝ => (1 : ℝ)) t := by
    simpa only [mul_one] using integrable_halfLineGammaCutoffKernel hδ
  have h := integral_symCutoffKernel_mul (δ := δ) (f := fun _ => (1 : ℝ)) hK hK
  simp only [mul_one] at h
  rw [h]
  ring

/-- `δ ∫_{h>δ} ω → 0` as `δ → 0⁺`: the mass of the cutoff kernel grows only logarithmically. -/
theorem tendsto_mul_integral_archLevyDensity_Ioi :
    Tendsto (fun δ : ℝ => δ * ∫ h in Ioi δ, archLevyDensity h) (𝓝[>] 0) (𝓝 0) := by
  have hcont : Continuous fun δ : ℝ => δ * ((Real.log 2 + 4) / 2) - δ * Real.log δ / 2 :=
    (continuous_id.mul continuous_const).sub (Real.continuous_mul_log.div_const 2)
  have hup : Tendsto (fun δ : ℝ => δ * ((Real.log 2 + 4) / 2) - δ * Real.log δ / 2) (𝓝[>] 0)
      (𝓝 0) := by
    have h := (hcont.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    simpa only [zero_mul, zero_div, sub_zero] using h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with δ hδ
    have hδ0 : (0 : ℝ) < δ := hδ
    exact mul_nonneg hδ0.le (setIntegral_nonneg measurableSet_Ioi fun h hh =>
      (archLevyDensity_pos (lt_trans hδ0 hh)).le)
  · filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Iic_mem_nhds (show (0 : ℝ) < 1 by norm_num))] with δ hδ hδ1
    have hδ0 : (0 : ℝ) < δ := hδ
    have hδ1' : δ ≤ 1 := hδ1
    rw [WeilLevyCoshCrossover.integral_archLevyDensity_Ioi hδ0]
    have h := ArithmeticIncidencePositivity.two_mul_archLevyAntideriv_le_log_one_div_add_four
      (w := δ / 2) (by positivity) (by linarith only [hδ1'])
    rw [show 2 * (δ / 2) = δ by ring, show 1 / (δ / 2) = 2 / δ by field_simp,
      Real.log_div (by norm_num) hδ0.ne'] at h
    have h2 := mul_le_mul_of_nonneg_left h hδ0.le
    linarith only [h2]

/-- A square integrable kernel against a translate of a square integrable profile. -/
theorem integrable_symCutoffKernel_mul_translate {δ : ℝ} (hδ : 0 < δ) {X : ℝ → ℝ}
    (hXm : Measurable X) (hX2 : Integrable fun u => X u ^ 2) (u : ℝ) :
    Integrable fun t => symCutoffKernel δ t * X (u - t) :=
  integrable_mul_of_integrable_sq (measurable_symCutoffKernel δ)
    (hXm.comp (measurable_const.sub measurable_id)) (integrable_sq_symCutoffKernel hδ)
    (hX2.comp_sub_left u)

theorem lineConvolution_symCutoffKernel_add {δ : ℝ} (hδ : 0 < δ) {X Y : ℝ → ℝ}
    (hXm : Measurable X) (hX2 : Integrable fun u => X u ^ 2) (hYm : Measurable Y)
    (hY2 : Integrable fun u => Y u ^ 2) (u : ℝ) :
    lineConvolution (symCutoffKernel δ) (fun v => X v + Y v) u =
      lineConvolution (symCutoffKernel δ) X u + lineConvolution (symCutoffKernel δ) Y u := by
  unfold lineConvolution
  rw [← integral_add (integrable_symCutoffKernel_mul_translate hδ hXm hX2 u)
    (integrable_symCutoffKernel_mul_translate hδ hYm hY2 u)]
  exact integral_congr_ae (Eventually.of_forall fun t => mul_add _ _ _)

theorem lineConvolution_symCutoffKernel_mono {δ : ℝ} (hδ : 0 < δ) {X Y : ℝ → ℝ}
    (hXm : Measurable X) (hX2 : Integrable fun u => X u ^ 2) (hYm : Measurable Y)
    (hY2 : Integrable fun u => Y u ^ 2) (h : ∀ᵐ v : ℝ, X v ≤ Y v) (u : ℝ) :
    lineConvolution (symCutoffKernel δ) X u ≤ lineConvolution (symCutoffKernel δ) Y u := by
  unfold lineConvolution
  refine integral_mono_ae (integrable_symCutoffKernel_mul_translate hδ hXm hX2 u)
    (integrable_symCutoffKernel_mul_translate hδ hYm hY2 u) ?_
  filter_upwards [ae_comp_const_sub h u] with t ht
  exact mul_le_mul_of_nonneg_left ht (symCutoffKernel_nonneg hδ t)

theorem lineConvolution_symCutoffKernel_le_const {δ : ℝ} (hδ : 0 < δ) {X : ℝ → ℝ}
    (hXm : Measurable X) (hX2 : Integrable fun u => X u ^ 2) {c : ℝ} (h : ∀ᵐ v : ℝ, X v ≤ c)
    (u : ℝ) :
    lineConvolution (symCutoffKernel δ) X u ≤ 2 * (∫ h in Ioi δ, archLevyDensity h) * c := by
  unfold lineConvolution
  rw [← integral_symCutoffKernel hδ, ← integral_mul_const]
  refine integral_mono_ae (integrable_symCutoffKernel_mul_translate hδ hXm hX2 u)
    ((integrable_symCutoffKernel hδ).mul_const c) ?_
  filter_upwards [ae_comp_const_sub h u] with t ht
  exact mul_le_mul_of_nonneg_left ht (symCutoffKernel_nonneg hδ t)

theorem stronglyMeasurable_lineConvolution_symCutoffKernel (δ : ℝ) {X : ℝ → ℝ}
    (hXm : Measurable X) : StronglyMeasurable (lineConvolution (symCutoffKernel δ) X) :=
  (((measurable_symCutoffKernel δ).comp measurable_snd).mul
    (hXm.comp (measurable_fst.sub measurable_snd))).stronglyMeasurable.integral_prod_right'

theorem integrable_lineConvolution_symCutoffKernel_mul {δ : ℝ} (hδ : 0 < δ) {X G : ℝ → ℝ}
    (hXm : Measurable X) (hX2 : Integrable fun u => X u ^ 2) (hGm : Measurable G)
    (hG1 : Integrable G) : Integrable fun u => lineConvolution (symCutoffKernel δ) X u * G u := by
  refine (hG1.norm.const_mul
    (Real.sqrt ((∫ t, symCutoffKernel δ t ^ 2) * ∫ v, X v ^ 2))).mono'
    ((stronglyMeasurable_lineConvolution_symCutoffKernel δ hXm).mul
      hGm.stronglyMeasurable).aestronglyMeasurable (Eventually.of_forall fun u => ?_)
  rw [Real.norm_eq_abs, abs_mul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right (abs_lineConvolution_le
    (measurable_symCutoffKernel δ).aestronglyMeasurable (integrable_sq_symCutoffKernel hδ)
    hXm.aestronglyMeasurable hX2 u) (abs_nonneg _)

theorem integrable_kernel_mul_translation_pairing {K X G : ℝ → ℝ} (hK : Integrable K)
    (hKm : Measurable K) (hK0 : ∀ h, 0 ≤ K h) (hXm : Measurable X) (hGm : Measurable G)
    (hX2 : Integrable fun u => X u ^ 2) (hG2 : Integrable fun u => G u ^ 2) :
    Integrable fun t => K t * ∫ u, X (u - t) * G u := by
  have h := (integrable_weighted_translation_pairing hK hKm hK0 hXm hGm hX2 hG2).integral_prod_left
  refine h.congr (Eventually.of_forall fun t => ?_)
  show ∫ u, K t * X (u - t) * G u = K t * ∫ u, X (u - t) * G u
  rw [← integral_const_mul]
  exact integral_congr_ae (Eventually.of_forall fun u => mul_assoc _ _ _)

/-- Against a second profile, the symmetric cutoff convolution is the two rows over `h > δ`. -/
theorem integral_lineConvolution_symCutoffKernel_mul {δ : ℝ} (hδ : 0 < δ) {X G : ℝ → ℝ}
    (hXm : Measurable X) (hGm : Measurable G) (hX2 : Integrable fun u => X u ^ 2)
    (hG2 : Integrable fun u => G u ^ 2) :
    ∫ u, lineConvolution (symCutoffKernel δ) X u * G u =
      (∫ h in Ioi δ, archLevyDensity h * ∫ u, X (u - h) * G u) +
        ∫ h in Ioi δ, archLevyDensity h * ∫ u, X (u + h) * G u := by
  rw [← integral_weighted_translation_pairing (integrable_symCutoffKernel hδ)
    (measurable_symCutoffKernel δ) (symCutoffKernel_nonneg hδ) hXm hGm hX2 hG2]
  have h1 := integrable_kernel_mul_translation_pairing (integrable_halfLineGammaCutoffKernel hδ)
    (measurable_halfLineGammaCutoffKernel δ) (halfLineGammaCutoffKernel_nonneg hδ) hXm hGm hX2 hG2
  have h2 := integrable_kernel_mul_translation_pairing
    (K := fun t => halfLineGammaCutoffKernel δ (-t))
    (integrable_halfLineGammaCutoffKernel hδ).comp_neg
    ((measurable_halfLineGammaCutoffKernel δ).comp measurable_neg)
    (fun t => halfLineGammaCutoffKernel_nonneg hδ (-t)) hXm hGm hX2 hG2
  have h2' : Integrable fun t => halfLineGammaCutoffKernel δ t * ∫ u, X (u - -t) * G u := by
    have h := h2.comp_neg
    simpa only [neg_neg] using h
  have e := integral_symCutoffKernel_mul (f := fun t => ∫ u, X (u - t) * G u) h1 h2'
  simp only [sub_neg_eq_add] at e
  exact e

/-! ### The cutoff Lévy operator -/

/-- The Lévy operator of the Gamma form with the lags `|t| ≤ δ` removed:
`𝔏_δ X(u) = ∫_{|t| > δ} ω(|t|) (X(u) − X(u − t)) dt`. -/
def cutoffLevy (δ : ℝ) (X : ℝ → ℝ) (u : ℝ) : ℝ :=
  2 * (∫ h in Ioi δ, archLevyDensity h) * X u - lineConvolution (symCutoffKernel δ) X u

theorem integrable_cutoffLevy_mul {δ : ℝ} (hδ : 0 < δ) {X G : ℝ → ℝ} (hXm : Measurable X)
    (hX2 : Integrable fun u => X u ^ 2) (hGm : Measurable G) (hG1 : Integrable G)
    (hG2 : Integrable fun u => G u ^ 2) : Integrable fun u => cutoffLevy δ X u * G u := by
  have h1 := (integrable_mul_of_integrable_sq hXm hGm hX2 hG2).const_mul
    (2 * ∫ h in Ioi δ, archLevyDensity h)
  have h2 := integrable_lineConvolution_symCutoffKernel_mul hδ hXm hX2 hGm hG1
  refine (h1.sub h2).congr (Eventually.of_forall fun u => ?_)
  show 2 * (∫ h in Ioi δ, archLevyDensity h) * (X u * G u) -
    lineConvolution (symCutoffKernel δ) X u * G u = cutoffLevy δ X u * G u
  unfold cutoffLevy
  ring

/-- **The cutoff operator represents the large jumps**: for profiles of the domain,
`∫ G · 𝔏_δ F` is the jump form of `(F, G)` over the lags `h > δ`. -/
theorem integral_cutoffLevy_mul {δ : ℝ} (hδ : 0 < δ) {F G : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) (hG : CriticalHalfLineEnergyDomain G) :
    ∫ u, cutoffLevy δ F u * G u = ∫ h in Ioi δ, halfLineGammaMixedJump F G h := by
  have h1 := (integrable_mul_of_integrable_sq hF.meas hG.meas hF.sq hG.sq).const_mul
    (2 * ∫ h in Ioi δ, archLevyDensity h)
  have h2 := integrable_lineConvolution_symCutoffKernel_mul hδ hF.meas hF.sq hG.meas hG.integrable
  have e : (fun u => cutoffLevy δ F u * G u) = fun u =>
      2 * (∫ h in Ioi δ, archLevyDensity h) * (F u * G u) -
        lineConvolution (symCutoffKernel δ) F u * G u := by
    funext u
    unfold cutoffLevy
    ring
  rw [e, integral_sub h1 h2, integral_const_mul,
    integral_lineConvolution_symCutoffKernel_mul hδ hF.meas hG.meas hF.sq hG.sq,
    integral_halfLineGammaMixedJump_cutoff hδ hF hG]
  ring

theorem integral_cutoffLevy_mul_self_nonneg {δ : ℝ} (hδ : 0 < δ) {G : ℝ → ℝ}
    (hG : CriticalHalfLineEnergyDomain G) : 0 ≤ ∫ u, cutoffLevy δ G u * G u := by
  rw [integral_cutoffLevy_mul hδ hG hG]
  refine setIntegral_nonneg measurableSet_Ioi fun h hh => ?_
  show 0 ≤ archLevyDensity h * ∫ u, (G u - G (u + h)) * (G u - G (u + h))
  exact mul_nonneg (archLevyDensity_pos (lt_trans hδ hh)).le
    (integral_nonneg fun u => mul_self_nonneg _)

/-! ### The Lipschitz cutoff of the collar -/

/-- The Lipschitz cutoff of the collar: `0` left of `−k`, `1` right of `−k/2`. -/
def collarCutoff (k u : ℝ) : ℝ := min (max (2 / k * (u + k)) 0) 1

theorem measurable_collarCutoff (k : ℝ) : Measurable (collarCutoff k) :=
  (((measurable_id.add_const k).const_mul (2 / k)).max measurable_const).min measurable_const

theorem collarCutoff_nonneg (k u : ℝ) : 0 ≤ collarCutoff k u :=
  le_min (le_max_right _ _) zero_le_one

theorem collarCutoff_le_one (k u : ℝ) : collarCutoff k u ≤ 1 := min_le_right _ _

theorem abs_collarCutoff_le_one (k u : ℝ) : |collarCutoff k u| ≤ 1 := by
  rw [abs_of_nonneg (collarCutoff_nonneg k u)]
  exact collarCutoff_le_one k u

theorem collarCutoff_of_le {k u : ℝ} (hk : 0 < k) (hu : u ≤ -k) : collarCutoff k u = 0 := by
  have h : 2 / k * (u + k) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith only [hu])
  unfold collarCutoff
  rw [max_eq_right h, min_eq_left zero_le_one]

theorem collarCutoff_of_ge {k u : ℝ} (hk : 0 < k) (hu : -(k / 2) ≤ u) : collarCutoff k u = 1 := by
  have h : 1 ≤ 2 / k * (u + k) := by
    have h1 : 2 / k * (k / 2) ≤ 2 / k * (u + k) :=
      mul_le_mul_of_nonneg_left (by linarith only [hu]) (by positivity)
    have h2 : 2 / k * (k / 2) = 1 := by field_simp
    linarith only [h1, h2]
  unfold collarCutoff
  rw [max_eq_left (le_trans zero_le_one h), min_eq_right h]

theorem collarCutoff_lipschitz {k : ℝ} (hk : 0 < k) (u v : ℝ) :
    |collarCutoff k u - collarCutoff k v| ≤ 2 / k * |u - v| := by
  have h2k : 0 < 2 / k := by positivity
  unfold collarCutoff
  calc |min (max (2 / k * (u + k)) 0) 1 - min (max (2 / k * (v + k)) 0) 1|
      ≤ max |max (2 / k * (u + k)) 0 - max (2 / k * (v + k)) 0| |(1 : ℝ) - 1| :=
        abs_min_sub_min_le_max _ _ _ _
    _ = |max (2 / k * (u + k)) 0 - max (2 / k * (v + k)) 0| := by
        rw [sub_self, abs_zero, max_eq_left (abs_nonneg _)]
    _ ≤ |2 / k * (u + k) - 2 / k * (v + k)| := abs_max_sub_max_le_abs _ _ _
    _ = 2 / k * |u - v| := by
        rw [← mul_sub, abs_mul, abs_of_pos h2k, add_sub_add_right_eq_sub]

/-! ### The weak equation against a nonnegative test at the wall -/

/-- The weak equation bounds the jump form of a minimizer against a nonnegative test carried by
`(−1/2, 0)` by a multiple of the mass of the test. Of the prime row only the backward shifts
meet the support of the test, and there the minimizer decays exponentially. -/
theorem IsHalfLineEnergyMinimizer.integral_mixedJump_le {R : ℝ} (hR : 0 < R) {F : ℝ → ℝ}
    (hF : IsHalfLineEnergyMinimizer R F) {C C₁ : ℝ} (hC : ∀ᵐ u : ℝ, |F u| ≤ C)
    (hC₁0 : 0 ≤ C₁) (hC₁ : ∀ᵐ u : ℝ, |F u| ≤ C₁ * Real.exp (1 * u)) {G : ℝ → ℝ}
    (hG : CriticalHalfLineEnergyDomain G) (hG0 : ∀ u, 0 ≤ G u)
    (hGs : ∀ u, u ≤ -(1 / 2) → G u = 0) :
    ∫ h in Ioi (0 : ℝ), halfLineGammaMixedJump F G h ≤
      ((|criticalHalfLineGroundEnergy R| + 2 * |gammaHardyPhaseRate 0|) * C +
        C₁ * halfLineExponentialPrimeTail 1 + Real.exp (1 / 4) * halfLinePoleReadoutSize F +
        criticalAliasCoefficient R * (C * Real.exp 4)) * ∫ u, G u := by
  have ha := criticalAliasCoefficient_positive hR
  have hI0 : 0 ≤ ∫ u, G u := integral_nonneg hG0
  -- the mass pairing
  have hFG : |∫ u, F u * G u| ≤ C * ∫ u, G u := by
    have h := norm_integral_le_of_norm_le (hG.integrable.const_mul C)
      (f := fun u => F u * G u) (by
        filter_upwards [hC] with u hu
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hG0 u)]
        exact mul_le_mul_of_nonneg_right hu (hG0 u))
    rwa [Real.norm_eq_abs, integral_const_mul] at h
  -- the confinement pairing
  have hconf : |∫ u, F u * G u * Real.exp (-(8 * u))| ≤ C * Real.exp 4 * ∫ u, G u := by
    have h := norm_integral_le_of_norm_le (hG.integrable.const_mul (C * Real.exp 4))
      (f := fun u => F u * G u * Real.exp (-(8 * u))) (by
        filter_upwards [hC] with u hu
        rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (hG0 u),
          abs_of_pos (Real.exp_pos _)]
        rcases le_or_gt u (-(1 / 2)) with h | h
        · simp only [hGs u h, mul_zero, zero_mul, le_refl]
        · have he : Real.exp (-(8 * u)) ≤ Real.exp 4 :=
            Real.exp_le_exp.mpr (by linarith only [h])
          have hC0 : 0 ≤ C := (abs_nonneg _).trans hu
          calc |F u| * G u * Real.exp (-(8 * u)) ≤ C * G u * Real.exp 4 :=
                mul_le_mul (mul_le_mul_of_nonneg_right hu (hG0 u)) he (Real.exp_pos _).le
                  (mul_nonneg hC0 (hG0 u))
            _ = C * Real.exp 4 * G u := by ring)
    rwa [Real.norm_eq_abs, integral_const_mul] at h
  -- the pole pairing
  have hpole := halfLine_polarMixedForm_lower F hG hG0
  have hpe : ∫ u, G u * Real.exp (-(u / 2)) ≤ Real.exp (1 / 4) * ∫ u, G u := by
    rw [← integral_const_mul]
    refine integral_mono hG.integrable_polarExponential (hG.integrable.const_mul _) fun u => ?_
    show G u * Real.exp (-(u / 2)) ≤ Real.exp (1 / 4) * G u
    rcases le_or_gt u (-(1 / 2)) with h | h
    · rw [hGs u h, zero_mul, mul_zero]
    · rw [mul_comm]
      exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by linarith only [h])) (hG0 u)
  -- the prime row
  have hprime : primeMixedForm F G ≤ C₁ * halfLineExponentialPrimeTail 1 * ∫ u, G u := by
    have hterm : ∀ n : ℕ, primePairTerm F G n ≤
        vonMangoldtAtom n * Real.exp (-(1 * Real.log (n : ℝ))) * (C₁ * ∫ u, G u) := by
      intro n
      rcases lt_or_ge n 2 with hn | hn
      · have h0 : vonMangoldtAtom n = 0 := by
          unfold vonMangoldtAtom
          rw [if_neg (not_le.mpr hn)]
        unfold primePairTerm
        rw [h0, zero_mul, zero_mul, zero_mul]
      · have hlog2 : (1 / 2 : ℝ) < Real.log 2 := lt_trans (by norm_num) Real.log_two_gt_d9
        have hlog : 1 / 2 < Real.log (n : ℝ) :=
          lt_of_lt_of_le hlog2 (Real.log_le_log (by norm_num) (by exact_mod_cast hn))
        have ha0 : 0 ≤ vonMangoldtAtom n := by
          unfold vonMangoldtAtom
          rw [if_pos hn]
          exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _)
        have hfirst : ∫ t, F t * G (t - Real.log n) = 0 := by
          refine integral_eq_zero_of_ae (Eventually.of_forall fun t => ?_)
          show F t * G (t - Real.log n) = 0
          rcases le_or_gt 0 t with ht | ht
          · rw [hF.1.support t ht, zero_mul]
          · rw [hGs _ (by linarith only [ht, hlog]), mul_zero]
        have hsecond : ∫ t, F t * G (t + Real.log n) ≤
            C₁ * Real.exp (-(1 * Real.log (n : ℝ))) * ∫ u, G u := by
          have hGt : Integrable fun t => G (t + Real.log n) := hG.integrable.comp_add_right _
          have hGt2 : Integrable fun t => G (t + Real.log n) ^ 2 := hG.sq.comp_add_right _
          have hFGt : Integrable fun t => F t * G (t + Real.log n) :=
            integrable_mul_of_integrable_sq hF.1.meas
              (hG.meas.comp (measurable_id.add_const _)) hF.1.sq hGt2
          have hmono := integral_mono_ae hFGt
            (hGt.const_mul (C₁ * Real.exp (-(1 * Real.log (n : ℝ))))) (by
              filter_upwards [hC₁] with t ht
              show F t * G (t + Real.log n) ≤
                C₁ * Real.exp (-(1 * Real.log (n : ℝ))) * G (t + Real.log n)
              rcases le_or_gt 0 (t + Real.log n) with h | h
              · rw [hG.support _ h, mul_zero, mul_zero]
              · have he : Real.exp (1 * t) ≤ Real.exp (-(1 * Real.log (n : ℝ))) :=
                  Real.exp_le_exp.mpr (by linarith only [h])
                have h1 : F t ≤ C₁ * Real.exp (-(1 * Real.log (n : ℝ))) :=
                  (le_abs_self _).trans (ht.trans (mul_le_mul_of_nonneg_left he hC₁0))
                exact mul_le_mul_of_nonneg_right h1 (hG0 _))
          rw [integral_const_mul, integral_add_right_eq_self G (Real.log n)] at hmono
          exact hmono
        unfold primePairTerm
        rw [hfirst, zero_add]
        calc vonMangoldtAtom n * ∫ t, F t * G (t + Real.log n)
            ≤ vonMangoldtAtom n * (C₁ * Real.exp (-(1 * Real.log (n : ℝ))) * ∫ u, G u) :=
              mul_le_mul_of_nonneg_left hsecond ha0
          _ = _ := by ring
    unfold primeMixedForm
    apply (summable_primePairTerm hF.1.weighted hG.weighted).tsum_le_of_sum_le
    intro s
    calc ∑ n ∈ s, primePairTerm F G n
        ≤ ∑ n ∈ s, vonMangoldtAtom n * Real.exp (-(1 * Real.log (n : ℝ))) * (C₁ * ∫ u, G u) :=
          Finset.sum_le_sum fun n _ => hterm n
      _ = (∑ n ∈ s, vonMangoldtAtom n * Real.exp (-(1 * Real.log (n : ℝ)))) *
            (C₁ * ∫ u, G u) := (Finset.sum_mul s _ _).symm
      _ ≤ halfLineExponentialPrimeTail 1 * (C₁ * ∫ u, G u) :=
          mul_le_mul_of_nonneg_right
            (sum_exponentialBarrier_prime_backward_le (β := 1) (by norm_num) s)
            (mul_nonneg hC₁0 hI0)
      _ = C₁ * halfLineExponentialPrimeTail 1 * ∫ u, G u := by ring
  have heq := hF.weakEquation_rows hR hG
  have hgm := gammaMixedForm_eq_halfLineGammaMixedJump hF.1 hG
  have hP0 := halfLinePoleReadoutSize_nonneg F
  have t1 : criticalHalfLineGroundEnergy R * (∫ u, F u * G u) ≤
      |criticalHalfLineGroundEnergy R| * (C * ∫ u, G u) := by
    calc criticalHalfLineGroundEnergy R * (∫ u, F u * G u)
        ≤ |criticalHalfLineGroundEnergy R * ∫ u, F u * G u| := le_abs_self _
      _ = |criticalHalfLineGroundEnergy R| * |∫ u, F u * G u| := abs_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left hFG (abs_nonneg _)
  have t2 : -(2 * gammaHardyPhaseRate 0 * (∫ u, F u * G u)) ≤
      2 * |gammaHardyPhaseRate 0| * (C * ∫ u, G u) := by
    calc -(2 * gammaHardyPhaseRate 0 * (∫ u, F u * G u))
        ≤ |2 * gammaHardyPhaseRate 0 * ∫ u, F u * G u| := neg_le_abs _
      _ = 2 * |gammaHardyPhaseRate 0| * |∫ u, F u * G u| := by
          rw [abs_mul, abs_mul, abs_of_pos (show (0 : ℝ) < 2 by norm_num)]
      _ ≤ _ := mul_le_mul_of_nonneg_left hFG (by positivity)
  have t3 : -(criticalAliasCoefficient R * (∫ u, F u * G u * Real.exp (-(8 * u)))) ≤
      criticalAliasCoefficient R * (C * Real.exp 4 * ∫ u, G u) := by
    have h := mul_le_mul_of_nonneg_left ((neg_le_abs _).trans hconf) ha.le
    linarith only [h]
  have t4 : -(2 * coshHalfMoment F * coshHalfMoment G - 2 * sinhHalfMoment F * sinhHalfMoment G) ≤
      halfLinePoleReadoutSize F * (Real.exp (1 / 4) * ∫ u, G u) := by
    have h := mul_le_mul_of_nonneg_left hpe hP0
    linarith only [hpole, h]
  linarith only [heq, hgm, t1, t2, t3, t4, hprime]

/-! ### The comparison principle -/

/-- **Comparison principle at the wall.** A minimizer lies below every bounded barrier `ψ` of
the domain, carried by `(−k, 0)` and at least the essential bound of the minimizer on
`(−k, −k/2]`, for which the function equal to `ψ` on `(−k, 0)` and to the minimizer left of
`−k` is a strict supersolution of the cutoff Lévy operators on `(−k/2, −δ]`, with the margin
`M + 1` fixed by the minimizer. -/
theorem IsHalfLineEnergyMinimizer.exists_wall_comparison {R : ℝ} (hR : 0 < R) {F : ℝ → ℝ}
    (hF : IsHalfLineEnergyMinimizer R F) :
    ∃ C M : ℝ, 0 ≤ C ∧ 0 ≤ M ∧ (∀ᵐ u : ℝ, |F u| ≤ C) ∧
      ∀ k : ℝ, 0 < k → k ≤ 1 / 2 → ∀ ψ : ℝ → ℝ, CriticalHalfLineEnergyDomain ψ →
        (∀ u, u ≤ -k → ψ u = 0) → ∀ B : ℝ, (∀ u, |ψ u| ≤ B) →
        (∀ u, -k < u → u ≤ -(k / 2) → C ≤ ψ u) → ∀ δ₀ : ℝ, 0 < δ₀ →
        (∀ δ u : ℝ, 0 < δ → δ ≤ δ₀ → -(k / 2) < u → u ≤ -δ →
          M + 1 ≤ cutoffLevy δ ψ u -
            lineConvolution (symCutoffKernel δ) ((Iic (-k)).indicator F) u) →
        ∀ᵐ u : ℝ, -k < u → u < 0 → F u ≤ ψ u := by
  obtain ⟨C, hC0, hC⟩ := hF.exists_uniform_abs_bound hR
  obtain ⟨C₁, hC₁0, hC₁⟩ := hF.exists_exponential_barrier hR
    (show (1 / 2 : ℝ) < 1 by norm_num) (show (1 : ℝ) < 15 / 2 by norm_num)
  obtain ⟨M, hMdef⟩ : ∃ M : ℝ, M =
      (|criticalHalfLineGroundEnergy R| + 2 * |gammaHardyPhaseRate 0|) * C +
        C₁ * halfLineExponentialPrimeTail 1 + Real.exp (1 / 4) * halfLinePoleReadoutSize F +
        criticalAliasCoefficient R * (C * Real.exp 4) := ⟨_, rfl⟩
  have hM0 : 0 ≤ M := by
    rw [hMdef]
    exact add_nonneg (add_nonneg (add_nonneg
      (mul_nonneg (add_nonneg (abs_nonneg _) (mul_nonneg zero_le_two (abs_nonneg _))) hC0)
      (mul_nonneg hC₁0 (halfLineExponentialPrimeTail_nonneg 1)))
      (mul_nonneg (Real.exp_pos _).le (halfLinePoleReadoutSize_nonneg F)))
      (mul_nonneg (criticalAliasCoefficient_positive hR).le (mul_nonneg hC0 (Real.exp_pos _).le))
  refine ⟨C, M, hC0, hM0, hC, ?_⟩
  intro k hk hk2 ψ hψ hψleft B hψB hψtop δ₀ hδ₀ hsuper
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hψB 0)
  have hCB : 0 ≤ C + B := add_nonneg hC0 hB0
  -- the test function: the positive part of `F − ψ`, cut off left of `−k/2`
  have hcut : CriticalHalfLineEnergyDomain fun u => collarCutoff k u * F u :=
    criticalHalfLineEnergyDomain_lipschitz_mul hF.1 (measurable_collarCutoff k)
      (fun u => abs_collarCutoff_le_one k u) (fun u v => collarCutoff_lipschitz hk u v)
  have hpos : LipschitzWith 1 (fun x : ℝ => max x 0) := by
    apply lipschitzWith_iff_dist_le_mul.mpr
    intro x y
    simpa only [Real.dist_eq, NNReal.coe_one, one_mul] using abs_max_sub_max_le_abs x y 0
  obtain ⟨G, hGdef⟩ : ∃ G : ℝ → ℝ,
      G = fun u => max (collarCutoff k u * F u + (-1) * ψ u) 0 := ⟨_, rfl⟩
  have hGval : ∀ u, G u = max (collarCutoff k u * F u + (-1) * ψ u) 0 := fun u => by rw [hGdef]
  have hG : CriticalHalfLineEnergyDomain G := by
    rw [hGdef]
    exact (hcut.add_const_mul hψ (-1)).comp_contraction hpos (max_self 0)
  have hG0 : ∀ u, 0 ≤ G u := fun u => by
    rw [hGval]
    exact le_max_right _ _
  have hGleft : ∀ u, u ≤ -k → G u = 0 := fun u hu => by
    rw [hGval, collarCutoff_of_le hk hu, hψleft u hu, zero_mul, mul_zero, add_zero, max_self]
  have hGin : ∀ u, -(k / 2) ≤ u → G u = max (F u - ψ u) 0 := fun u hu => by
    rw [hGval, collarCutoff_of_ge hk hu, one_mul, neg_one_mul, ← sub_eq_add_neg]
  have hI0 : 0 ≤ ∫ u, G u := integral_nonneg hG0
  -- almost everywhere: `G` is bounded and vanishes on `(−k, −k/2]`
  have hae : ∀ᵐ u : ℝ, G u ≤ C + B ∧ (-k < u → u ≤ -(k / 2) → G u = 0) := by
    filter_upwards [hC] with u hu
    have hcF : collarCutoff k u * F u ≤ C :=
      calc collarCutoff k u * F u ≤ collarCutoff k u * |F u| :=
            mul_le_mul_of_nonneg_left (le_abs_self _) (collarCutoff_nonneg k u)
        _ ≤ 1 * C := mul_le_mul (collarCutoff_le_one k u) hu (abs_nonneg _) zero_le_one
        _ = C := one_mul C
    constructor
    · rw [hGval]
      refine max_le ?_ hCB
      have h := (abs_le.mp (hψB u)).1
      linarith only [hcF, h]
    · intro h1 h2
      rw [hGval]
      exact max_eq_right (by linarith only [hcF, hψtop u h1 h2])
  -- almost everywhere: `F ≤ G + ψ + F 1_{(−∞, −k]}`
  have hP1 : ∀ᵐ v : ℝ, F v ≤ (G v + ψ v) + (Iic (-k)).indicator F v := by
    filter_upwards [hC] with v hv
    rcases le_or_gt v (-k) with h | h
    · rw [indicator_of_mem (show v ∈ Iic (-k) from h), hGleft v h, hψleft v h, zero_add, zero_add]
    · rw [indicator_of_notMem (show v ∉ Iic (-k) from not_le.mpr h), add_zero]
      rcases le_or_gt v (-(k / 2)) with h2 | h2
      · have h3 := hψtop v h h2
        have h4 := (abs_le.mp hv).2
        linarith only [hG0 v, h3, h4]
      · rw [hGin v h2.le]
        have h3 := le_max_left (F v - ψ v) 0
        linarith only [h3]
  have hXm : Measurable ((Iic (-k)).indicator F) := hF.1.meas.indicator measurableSet_Iic
  have hX2 : Integrable fun v => (Iic (-k)).indicator F v ^ 2 := by
    refine hF.1.sq.mono' (hXm.pow_const 2).aestronglyMeasurable (Eventually.of_forall fun v => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    by_cases hv : v ∈ Iic (-k)
    · rw [indicator_of_mem hv]
    · rw [indicator_of_notMem hv]
      positivity
  have hXC : ∀ᵐ v : ℝ, (Iic (-k)).indicator F v ≤ C := by
    filter_upwards [hC] with v hv
    by_cases hmem : v ∈ Iic (-k)
    · rw [indicator_of_mem hmem]
      exact (le_abs_self _).trans hv
    · rw [indicator_of_notMem hmem]
      exact hC0
  have hGψm : Measurable fun v => G v + ψ v := hG.meas.add hψ.meas
  have hGψ2 : Integrable fun v => (G v + ψ v) ^ 2 :=
    integrable_sq_add_of_integrable_sq hG.meas hψ.meas hG.sq hψ.sq
  have hsum2 : Integrable fun v => ((G v + ψ v) + (Iic (-k)).indicator F v) ^ 2 :=
    integrable_sq_add_of_integrable_sq hGψm hXm hGψ2 hX2
  -- the large jumps of `(F, G)` dominate the barrier term
  have hkey : ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
      (M + 1) * (∫ u, G u) - (M + 1 + 2 * (∫ h in Ioi δ, archLevyDensity h) * (2 * B + C)) *
        ((C + B) * δ) ≤ ∫ h in Ioi δ, halfLineGammaMixedJump F G h := by
    intro δ hδ hδδ₀
    obtain ⟨Ω, hΩdef⟩ : ∃ Ω : ℝ, Ω = ∫ h in Ioi δ, archLevyDensity h := ⟨_, rfl⟩
    have hΩ0 : 0 ≤ Ω := by
      rw [hΩdef]
      exact setIntegral_nonneg measurableSet_Ioi fun h hh =>
        (archLevyDensity_pos (lt_trans hδ hh)).le
    have hcoef : 0 ≤ M + 1 + 2 * Ω * (2 * B + C) :=
      add_nonneg (add_nonneg hM0 zero_le_one)
        (mul_nonneg (mul_nonneg zero_le_two hΩ0) (add_nonneg (mul_nonneg zero_le_two hB0) hC0))
    rw [← hΩdef, ← integral_cutoffLevy_mul hδ hF.1 hG]
    have hpt : ∀ᵐ u : ℝ, cutoffLevy δ G u * G u + ((M + 1) * G u -
        (M + 1 + 2 * Ω * (2 * B + C)) * (Ioo (-δ) (0 : ℝ)).indicator (fun _ => C + B) u) ≤
        cutoffLevy δ F u * G u := by
      filter_upwards [hae] with u hu
      have hind : 0 ≤ (Ioo (-δ) (0 : ℝ)).indicator (fun _ => C + B) u :=
        indicator_nonneg (fun _ _ => hCB) u
      rcases eq_or_ne (G u) 0 with hz | hz
      · simp only [hz, mul_zero, zero_add, zero_sub]
        linarith only [mul_nonneg hcoef hind]
      · have hGpos : 0 < G u := lt_of_le_of_ne (hG0 u) (Ne.symm hz)
        have hu0 : u < 0 := by
          by_contra h
          exact hz (hG.support u (not_lt.mp h))
        have huk : -k < u := by
          by_contra h
          exact hz (hGleft u (not_lt.mp h))
        have huk2 : -(k / 2) < u := by
          by_contra h
          exact hz (hu.2 huk (not_lt.mp h))
        have hFu : F u = G u + ψ u := by
          have h1 := hGin u huk2.le
          have h2 : 0 < F u - ψ u := by
            by_contra h
            rw [max_eq_right (not_lt.mp h)] at h1
            exact hz h1
          rw [max_eq_left h2.le] at h1
          linarith only [h1]
        have hconv : lineConvolution (symCutoffKernel δ) F u ≤
            lineConvolution (symCutoffKernel δ) G u + lineConvolution (symCutoffKernel δ) ψ u +
              lineConvolution (symCutoffKernel δ) ((Iic (-k)).indicator F) u := by
          have h1 := lineConvolution_symCutoffKernel_mono hδ hF.1.meas hF.1.sq (hGψm.add hXm)
            hsum2 hP1 u
          rw [lineConvolution_symCutoffKernel_add hδ hGψm hGψ2 hXm hX2,
            lineConvolution_symCutoffKernel_add hδ hG.meas hG.sq hψ.meas hψ.sq] at h1
          exact h1
        have hlevy : cutoffLevy δ G u + (cutoffLevy δ ψ u -
            lineConvolution (symCutoffKernel δ) ((Iic (-k)).indicator F) u) ≤
            cutoffLevy δ F u := by
          have e : cutoffLevy δ F u =
              2 * Ω * (G u + ψ u) - lineConvolution (symCutoffKernel δ) F u := by
            unfold cutoffLevy
            rw [← hΩdef, ← hFu]
          rw [e]
          unfold cutoffLevy
          rw [← hΩdef]
          linarith only [hconv]
        rcases le_or_gt u (-δ) with hδu | hδu
        · have hs := hsuper δ u hδ hδδ₀ huk2 hδu
          have hout : (Ioo (-δ) (0 : ℝ)).indicator (fun _ => C + B) u = 0 :=
            indicator_of_notMem (fun h => absurd h.1 (not_lt.mpr hδu)) _
          rw [hout, mul_zero, sub_zero]
          have h0 : cutoffLevy δ G u + (M + 1) ≤ cutoffLevy δ F u := by
            linarith only [hlevy, hs]
          have h1 := mul_le_mul_of_nonneg_right h0 hGpos.le
          linarith only [h1]
        · -- on the strip `(−δ, 0)` the barrier term is only bounded below
          have hin : (Ioo (-δ) (0 : ℝ)).indicator (fun _ => C + B) u = C + B :=
            indicator_of_mem (show u ∈ Ioo (-δ) 0 from ⟨hδu, hu0⟩) _
          have hc1 := lineConvolution_symCutoffKernel_le_const hδ hψ.meas hψ.sq
            (c := B) (Eventually.of_forall fun v => (le_abs_self _).trans (hψB v)) u
          have hc2 := lineConvolution_symCutoffKernel_le_const hδ hXm hX2 hXC u
          rw [← hΩdef] at hc1 hc2
          have hψu := (abs_le.mp (hψB u)).1
          have hcrude : -(2 * Ω * (2 * B + C)) ≤ cutoffLevy δ ψ u -
              lineConvolution (symCutoffKernel δ) ((Iic (-k)).indicator F) u := by
            unfold cutoffLevy
            rw [← hΩdef]
            have h1 := mul_le_mul_of_nonneg_left hψu (mul_nonneg zero_le_two hΩ0)
            linarith only [h1, hc1, hc2]
          rw [hin]
          have h0 : cutoffLevy δ G u - 2 * Ω * (2 * B + C) ≤ cutoffLevy δ F u := by
            linarith only [hlevy, hcrude]
          have h1 := mul_le_mul_of_nonneg_right h0 hGpos.le
          have h2 := mul_nonneg hcoef (sub_nonneg.mpr hu.1)
          linarith only [h1, h2]
    have hi1 := integrable_cutoffLevy_mul hδ hG.meas hG.sq hG.meas hG.integrable hG.sq
    have hind : Integrable ((Ioo (-δ) (0 : ℝ)).indicator fun _ : ℝ => C + B) :=
      ((continuousOn_const : ContinuousOn (fun _ : ℝ => C + B) (Icc (-δ) 0)).integrableOn_Icc.mono_set
        Ioo_subset_Icc_self).integrable_indicator measurableSet_Ioo
    have hi2 : Integrable fun u => (M + 1) * G u -
        (M + 1 + 2 * Ω * (2 * B + C)) * (Ioo (-δ) (0 : ℝ)).indicator (fun _ => C + B) u :=
      (hG.integrable.const_mul (M + 1)).sub (hind.const_mul (M + 1 + 2 * Ω * (2 * B + C)))
    have hi12 : Integrable fun u => cutoffLevy δ G u * G u + ((M + 1) * G u -
        (M + 1 + 2 * Ω * (2 * B + C)) * (Ioo (-δ) (0 : ℝ)).indicator (fun _ => C + B) u) :=
      hi1.add hi2
    have hint := integral_mono_ae hi12
      (integrable_cutoffLevy_mul hδ hF.1.meas hF.1.sq hG.meas hG.integrable hG.sq) hpt
    have hvol : ∫ u, (Ioo (-δ) (0 : ℝ)).indicator (fun _ => C + B) u = (C + B) * δ := by
      rw [integral_indicator measurableSet_Ioo, setIntegral_const,
        Real.volume_real_Ioo_of_le (by linarith only [hδ]), smul_eq_mul]
      ring
    rw [integral_add hi1 hi2, integral_sub (hG.integrable.const_mul (M + 1))
      (hind.const_mul (M + 1 + 2 * Ω * (2 * B + C))), integral_const_mul, integral_const_mul,
      hvol] at hint
    have hnn := integral_cutoffLevy_mul_self_nonneg hδ hG
    linarith only [hint, hnn]
  -- the weak equation, and the limit `δ → 0`
  have hJ := hF.integral_mixedJump_le hR hC hC₁0 hC₁ hG hG0
    (fun u hu => hGleft u (by linarith only [hu, hk2]))
  rw [← hMdef] at hJ
  have hle : ∀ᶠ δ : ℝ in 𝓝[>] 0, ∫ u, G u ≤
      (M + 1 + 2 * (∫ h in Ioi δ, archLevyDensity h) * (2 * B + C)) * ((C + B) * δ) -
        ∫ h in Ioc 0 δ, halfLineGammaMixedJump F G h := by
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Iic_mem_nhds hδ₀)] with δ hδ hδ'
    have hδ0 : (0 : ℝ) < δ := hδ
    have h1 := hkey δ hδ0 hδ'
    have h2 := integral_halfLineGammaMixedJump_split hF.1 hG hδ0
    linarith only [h1, h2, hJ]
  have hlim : Tendsto (fun δ : ℝ =>
      (M + 1 + 2 * (∫ h in Ioi δ, archLevyDensity h) * (2 * B + C)) * ((C + B) * δ) -
        ∫ h in Ioc 0 δ, halfLineGammaMixedJump F G h) (𝓝[>] 0) (𝓝 0) := by
    have h1 : Tendsto (fun δ : ℝ => δ) (𝓝[>] 0) (𝓝 0) :=
      tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
    have h2 := tendsto_mul_integral_archLevyDensity_Ioi
    have h3 := tendsto_setIntegral_Ioc_zero (integrableOn_halfLineGammaMixedJump hF.1 hG)
    have h := ((h1.const_mul ((M + 1) * (C + B))).add
      (h2.const_mul (2 * (2 * B + C) * (C + B)))).sub h3
    simp only [mul_zero, add_zero, sub_zero] at h
    refine h.congr fun δ => ?_
    ring
  have hle0 : ∫ u, G u ≤ 0 := ge_of_tendsto hlim hle
  have hGzero : G =ᵐ[volume] 0 :=
    (integral_eq_zero_iff_of_nonneg hG0 hG.integrable).mp (le_antisymm hle0 hI0)
  filter_upwards [hGzero, hC] with u hu hCu huk hu0
  rcases le_or_gt u (-(k / 2)) with h | h
  · exact ((abs_le.mp hCu).2).trans (hψtop u huk h)
  · have h1 := hGin u h.le
    have h2 : G u = 0 := hu
    rw [h2] at h1
    have h3 := le_max_left (F u - ψ u) 0
    linarith only [h1, h3]

end GaloisForLFunctions.ExclusionOfTheCriticalState
