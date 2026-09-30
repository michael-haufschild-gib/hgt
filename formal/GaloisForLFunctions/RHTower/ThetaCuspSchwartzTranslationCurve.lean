import GaloisForLFunctions.RHTower.ThetaCuspStripTaylorRemainder

/-!
Complex differentiation of the literal theta translation orbit in actual
Schwartz topology. Quadratic bounds in each defining seminorm give the TVS
derivative, and every continuous complex-linear scalar observer is analytic.
-/

open MeasureTheory Set Filter Topology
open scoped SchwartzMap ContDiff

noncomputable section

namespace RHTower

/-- Actual continuous complex-linear spatial differentiation of every order. -/
def thetaSchwartzSpatialJetCLM : ℕ → (𝓢(ℝ, ℂ) →L[ℂ] 𝓢(ℝ, ℂ))
  | 0 => ContinuousLinearMap.id ℂ 𝓢(ℝ, ℂ)
  | n + 1 => (thetaSchwartzSpatialJetCLM n).comp (SchwartzMap.derivCLM ℂ ℂ)

theorem thetaSchwartzSpatialJetCLM_apply (n : ℕ) (φ : 𝓢(ℝ, ℂ)) (x : ℝ) :
    thetaSchwartzSpatialJetCLM n φ x = iteratedDeriv n (φ : ℝ → ℂ) x := by
  induction n generalizing φ with
  | zero => rfl
  | succ n ih =>
    rw [thetaSchwartzSpatialJetCLM, ContinuousLinearMap.comp_apply, ih]
    change iteratedDeriv n (deriv (φ : ℝ → ℂ)) x =
      iteratedDeriv (n + 1) (φ : ℝ → ℂ) x
    rw [iteratedDeriv_succ']

theorem thetaSchwartzSpatialJetCLM_deriv_apply (n : ℕ) (φ : 𝓢(ℝ, ℂ)) (x : ℝ) :
    thetaSchwartzSpatialJetCLM n (SchwartzMap.derivCLM ℂ ℂ φ) x =
      iteratedDeriv (n + 1) (φ : ℝ → ℂ) x := by
  rw [thetaSchwartzSpatialJetCLM_apply]
  change iteratedDeriv n (deriv (φ : ℝ → ℂ)) x =
    iteratedDeriv (n + 1) (φ : ℝ → ℂ) x
  rw [iteratedDeriv_succ']

/-- The literal first-order remainder in actual Schwartz space. -/
def thetaCuspTranslationResidual (a h : ℂ) : 𝓢(ℝ, ℂ) :=
  thetaCuspSchwartzTranslationCurve (a + h) - thetaCuspSchwartzTranslationCurve a -
    h • SchwartzMap.derivCLM ℂ ℂ (thetaCuspSchwartzTranslationCurve a)

theorem thetaCuspTranslationResidual_zero (a : ℂ) :
    thetaCuspTranslationResidual a 0 = 0 := by
  simp only [thetaCuspTranslationResidual, add_zero, sub_self, zero_smul]

theorem thetaCuspTranslationResidual_spatialJet
    (a : ℂ) (ha : a ∈ thetaCuspStrip) (h : ℂ) (hah : a + h ∈ thetaCuspStrip)
    (n : ℕ) (x : ℝ) :
    iteratedDeriv n (thetaCuspTranslationResidual a h : ℝ → ℂ) x =
      iteratedDeriv n thetaCuspStripSource ((x : ℂ) + a + h) -
        iteratedDeriv n thetaCuspStripSource ((x : ℂ) + a) -
        h * iteratedDeriv (n + 1) thetaCuspStripSource ((x : ℂ) + a) := by
  rw [← thetaSchwartzSpatialJetCLM_apply, thetaCuspTranslationResidual,
    map_sub, map_sub, map_smul]
  change thetaSchwartzSpatialJetCLM n (thetaCuspSchwartzTranslationCurve (a + h)) x -
      thetaSchwartzSpatialJetCLM n (thetaCuspSchwartzTranslationCurve a) x -
      h • thetaSchwartzSpatialJetCLM n
        (SchwartzMap.derivCLM ℂ ℂ (thetaCuspSchwartzTranslationCurve a)) x = _
  rw [thetaSchwartzSpatialJetCLM_apply, thetaSchwartzSpatialJetCLM_apply,
    thetaSchwartzSpatialJetCLM_deriv_apply,
    thetaCuspSchwartzTranslationCurve_spatialJet (a + h) hah,
    thetaCuspSchwartzTranslationCurve_spatialJet a ha,
    thetaCuspSchwartzTranslationCurve_spatialJet a ha]
  simp only [add_assoc, smul_eq_mul]

/-- Every actual Schwartz seminorm of the literal translation remainder is quadratic. -/
theorem thetaCuspTranslationResidual_seminorm_quadratic
    (a : ℂ) (ha : a ∈ thetaCuspStrip) (k n : ℕ) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ h : ℂ, ‖h‖ ≤ ρ →
      SchwartzMap.seminorm ℂ k n (thetaCuspTranslationResidual a h) ≤ C * ‖h‖ ^ 2 := by
  have ha' : |a.im| < Real.pi / 4 := ha
  have hδ4 : 2 * |a.im| < Real.pi / 2 := by linarith
  obtain ⟨ρ, hρ, C, hC, hTaylor⟩ :=
    thetaCuspStripSource_complexJet_taylor_substrip (abs_nonneg a.im) hδ4 n
  let r := min ρ ((Real.pi / 4 - |a.im|) / 2)
  have hr : 0 < r := by dsimp [r]; apply lt_min hρ; linarith
  refine ⟨r, hr, C * Real.exp |a.re| * (k.factorial : ℝ), by positivity, ?_⟩
  intro h hh
  have hhρ : ‖h‖ ≤ ρ := hh.trans (min_le_left _ _)
  have hgap : ‖h‖ ≤ (Real.pi / 4 - |a.im|) / 2 := hh.trans (min_le_right _ _)
  have hah : a + h ∈ thetaCuspStrip := by
    change |(a + h).im| < Real.pi / 4
    have hi : |(a + h).im| ≤ |a.im| + ‖h‖ := by
      rw [Complex.add_im]
      exact (abs_add_le _ _).trans (by gcongr; exact Complex.abs_im_le_norm h)
    linarith
  apply SchwartzMap.seminorm_le_bound' ℂ k n (thetaCuspTranslationResidual a h)
    (by positivity)
  intro x
  rw [thetaCuspTranslationResidual_spatialJet a ha h hah n x]
  have hjet := hTaylor a le_rfl h hhρ x
  calc
    |x| ^ k * ‖iteratedDeriv n thetaCuspStripSource ((x : ℂ) + a + h) -
        iteratedDeriv n thetaCuspStripSource ((x : ℂ) + a) -
        h * iteratedDeriv (n + 1) thetaCuspStripSource ((x : ℂ) + a)‖ ≤
      |x| ^ k * (C * Real.exp |a.re| * Real.exp (-|x|) * ‖h‖ ^ 2) := by gcongr
    _ = (C * Real.exp |a.re| * ‖h‖ ^ 2) * (|x| ^ k * Real.exp (-|x|)) := by ring
    _ ≤ (C * Real.exp |a.re| * ‖h‖ ^ 2) * (k.factorial : ℝ) :=
      mul_le_mul_of_nonneg_left (pow_mul_exp_neg_le_factorial k (abs_nonneg x))
        (by positivity)
    _ = (C * Real.exp |a.re| * (k.factorial : ℝ)) * ‖h‖ ^ 2 := by ring

/-- The normalized literal remainder converges to zero in the actual Schwartz topology. -/
theorem thetaCuspTranslationResidual_normalized_tendsto
    (a : ℂ) (ha : a ∈ thetaCuspStrip) :
    Tendsto (fun h : ℂ => h⁻¹ • thetaCuspTranslationResidual a h)
      (𝓝 0) (𝓝 (0 : 𝓢(ℝ, ℂ))) := by
  apply ((schwartz_withSeminorms ℂ ℝ ℂ).tendsto_nhds
    (fun h : ℂ => h⁻¹ • thetaCuspTranslationResidual a h) 0).mpr
  rintro ⟨k, n⟩ ε hε
  obtain ⟨ρ, hρ, C, hC, hbound⟩ :=
    thetaCuspTranslationResidual_seminorm_quadratic a ha k n
  have hd : 0 < min ρ (ε / (C + 1)) := by
    apply lt_min hρ
    exact div_pos hε (by positivity)
  have hev : ∀ᶠ h : ℂ in 𝓝 0, ‖h‖ < min ρ (ε / (C + 1)) := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) hd] with h hh
    simpa only [Metric.mem_ball, dist_zero_right] using hh
  filter_upwards [hev] with h hh
  simp only [sub_zero, SchwartzMap.schwartzSeminormFamily_apply]
  have hb := hbound h (hh.le.trans (min_le_left _ _))
  have hscale : SchwartzMap.seminorm ℂ k n (h⁻¹ • thetaCuspTranslationResidual a h) ≤
      C * ‖h‖ := by
    rw [map_smul_eq_mul, norm_inv]
    calc
      ‖h‖⁻¹ * SchwartzMap.seminorm ℂ k n (thetaCuspTranslationResidual a h) ≤
          ‖h‖⁻¹ * (C * ‖h‖ ^ 2) := mul_le_mul_of_nonneg_left hb (by positivity)
      _ = C * ‖h‖ := by
        by_cases h0 : h = 0
        · simp only [h0, norm_zero, inv_zero, zero_mul, mul_zero]
        · have hn : ‖h‖ ≠ 0 := norm_ne_zero_iff.mpr h0
          field_simp
  have hε' : ‖h‖ * (C + 1) < ε :=
    (lt_div_iff₀ (by positivity)).mp (hh.trans_le (min_le_right _ _))
  exact hscale.trans_lt (by nlinarith [norm_nonneg h])

private theorem thetaHasDerivAt_of_tendsto_normalized
    {F : Type*} [AddCommGroup F] [Module ℂ F] [TopologicalSpace F]
    [ContinuousSMul ℂ F] {f : ℂ → F} {v : F} {a : ℂ}
    (hlim : Tendsto (fun z : ℂ => (z - a)⁻¹ • (f z - f a - (z - a) • v))
      (𝓝 a) (𝓝 0)) : HasDerivAt f v a := by
  change HasFDerivAtFilter f (ContinuousLinearMap.toSpanSingleton ℂ v) (𝓝 a ×ˢ pure a)
  apply HasFDerivAtFilter.of_isLittleOTVS
  rw [Filter.prod_pure, Asymptotics.isLittleOTVS_map]
  change Asymptotics.IsLittleOTVS ℂ (𝓝 a)
    (fun z : ℂ => f z - f a - (z - a) • v) (fun z : ℂ => z - a)
  have hzero : ∀ᶠ z : ℂ in 𝓝 a, z - a = 0 → f z - f a - (z - a) • v = 0 := by
    apply Filter.Eventually.of_forall
    intro z hz
    have hza : z = a := sub_eq_zero.mp hz
    simp only [hza, sub_self, zero_smul]
  exact (Asymptotics.isLittleOTVS_iff_tendsto_inv_smul hzero).mpr hlim

/-- Every genuine continuous complex-linear observer differentiates the actual source orbit. -/
theorem thetaCuspSchwartzTranslationCurve_clm_hasDerivAt
    {F : Type*} [AddCommGroup F] [Module ℂ F] [TopologicalSpace F]
    [ContinuousSMul ℂ F] (L : 𝓢(ℝ, ℂ) →L[ℂ] F)
    (a : ℂ) (ha : a ∈ thetaCuspStrip) :
    HasDerivAt (fun z : ℂ => L (thetaCuspSchwartzTranslationCurve z))
      (L (SchwartzMap.derivCLM ℂ ℂ (thetaCuspSchwartzTranslationCurve a))) a := by
  have hL : Tendsto (fun h : ℂ => L (h⁻¹ • thetaCuspTranslationResidual a h))
      (𝓝 0) (𝓝 0) := by
    simpa only [map_zero, Function.comp_def] using (L.continuous.tendsto (0 : 𝓢(ℝ, ℂ))).comp
      (thetaCuspTranslationResidual_normalized_tendsto a ha)
  have hs : Tendsto (fun z : ℂ => z - a) (𝓝 a) (𝓝 0) := by
    have hc : Continuous (fun z : ℂ => z - a) := continuous_id.sub continuous_const
    simpa only [sub_self] using hc.tendsto a
  have haShift (z : ℂ) : a + (z - a) = z := by ring
  apply thetaHasDerivAt_of_tendsto_normalized
  simpa only [Function.comp_def, thetaCuspTranslationResidual, map_smul, map_sub, haShift]
    using hL.comp hs

/-- The original source orbit is genuinely complex differentiable in Schwartz topology. -/
theorem thetaCuspSchwartzTranslationCurve_hasDerivAt
    (a : ℂ) (ha : a ∈ thetaCuspStrip) :
    HasDerivAt thetaCuspSchwartzTranslationCurve
      (SchwartzMap.derivCLM ℂ ℂ (thetaCuspSchwartzTranslationCurve a)) a := by
  simpa only [ContinuousLinearMap.id_apply] using
    thetaCuspSchwartzTranslationCurve_clm_hasDerivAt
      (ContinuousLinearMap.id ℂ 𝓢(ℝ, ℂ)) a ha

/-- Every actual tempered functional has an analytic scalar source orbit on the literal strip. -/
theorem thetaCuspSchwartzTranslationCurve_observer_analyticOnNhd
    (T : 𝓢(ℝ, ℂ) →L[ℂ] ℂ) :
    AnalyticOnNhd ℂ (fun z : ℂ => T (thetaCuspSchwartzTranslationCurve z)) thetaCuspStrip := by
  have hd : DifferentiableOn ℂ (fun z : ℂ => T (thetaCuspSchwartzTranslationCurve z))
      thetaCuspStrip := by
    intro a ha
    exact (thetaCuspSchwartzTranslationCurve_clm_hasDerivAt T a ha).differentiableAt.differentiableWithinAt
  exact hd.analyticOnNhd isOpen_thetaCuspStrip

end RHTower
