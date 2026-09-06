import GaloisForLFunctions.RHTower.WeilLagFunctionOneSided

/-!
# One-sided exponential growth of the lag function and zero-free half-planes

If the real lag function satisfies `Φ(L) ≤ M e^{aL}` for all `L ≥ 0` with `0 ≤ a < ½`, then every
zero copy has real part at most `½ + a`.  The mechanism is the one of the one-sided criterion: the
nonnegative density `M e^{au} − Φ(u)` on `(0,∞)`, augmented by the measure `e^{au} du` whose transform
`1/(s − a)` pins the abscissa at `a`, has a Laplace transform equal to `(M+1)/(s−a) − G(s)` on
`Re s > ½`, where `G` is the lag pole series; Landau's theorem forces the abscissa to be exactly `a`,
so `G` extends analytically to `Re s > a`, which excludes every pole `ρ − ½` with `Re ρ > ½ + a`.
-/

open Complex Filter Topology MeasureTheory Set
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.RHTower

namespace RHTower

noncomputable section

/-! ## The extension theorem for a general half-plane -/

/-- **Analytic extension of the lag pole series to `Re z > a` bounds the real parts of the zeros
by `½ + a`.** -/
theorem re_le_half_add_of_lagPoleSeries_extension {a : ℝ} (ha : 0 ≤ a) {F : ℂ → ℂ}
    (hFd : ∀ z : ℂ, a < z.re → z.re < 2 → DifferentiableAt ℂ F z)
    (hFG : ∀ s : ℂ, 1 / 2 < s.re → F s = lagPoleSeries s) (q₁ : XiZeroCopy) :
    (q₁.1 : ℂ).re ≤ 1 / 2 + a := by
  by_contra hq₁'
  have hq₁ : 1 / 2 + a < (q₁.1 : ℂ).re := not_le.mp hq₁'
  set ρ₁ : ℂ := (q₁.1 : ℂ) with hρ₁
  set K : Set ℂ := Set.Icc ρ₁.re 1 ×ℂ Set.Icc ρ₁.im ρ₁.im with hK
  have hKc : IsCompact K := isCompact_Icc.reProdIm isCompact_Icc
  have hfin : (xiZeroSet ∩ K).Finite := finite_xiZeroSet_inter hKc
  have hmem₁ : ρ₁ ∈ xiZeroSet ∩ K := by
    refine ⟨xi_xiZeroCopy_eq_zero q₁, ?_⟩
    rw [hK, Complex.mem_reProdIm]
    exact ⟨⟨le_rfl, (xiZeroCopy_re_lt_one q₁).le⟩, ⟨le_rfl, le_rfl⟩⟩
  obtain ⟨ρ₀, hρ₀⟩ := hfin.exists_maximalFor Complex.re _ ⟨ρ₁, hmem₁⟩
  have hρ₀mem : ρ₀ ∈ xiZeroSet ∩ K := hρ₀.1
  have hmax : ∀ z ∈ xiZeroSet ∩ K, ρ₀.re ≤ z.re → z.re ≤ ρ₀.re := fun z hz h => hρ₀.2 hz h
  obtain ⟨q₀, hq₀⟩ := exists_xiZeroCopy_of_xi_eq_zero hρ₀mem.1
  have hρ₀K := hρ₀mem.2
  rw [hK, Complex.mem_reProdIm] at hρ₀K
  have hre₀ : 1 / 2 + a < ρ₀.re := lt_of_lt_of_le hq₁ hρ₀K.1.1
  have hre₀' : ρ₀.re < 1 := xiZeroCopy_re_lt_one q₀ |> fun h => by rwa [hq₀] at h
  have him₀ : ρ₀.im = ρ₁.im := le_antisymm hρ₀K.2.2 hρ₀K.2.1
  set p₀ : ℂ := lagPole q₀ with hp₀
  have hp₀re : p₀.re = ρ₀.re - 1 / 2 := by
    rw [hp₀]; unfold lagPole; rw [hq₀]; simp
  have hp₀a : a < p₀.re := by rw [hp₀re]; linarith
  have hp₀pos : 0 < p₀.re := by linarith
  have hp₀half : p₀.re < 1 / 2 := by rw [hp₀re]; linarith
  -- the horizontal ray to the right of `p₀` carries no zero of `ξ(· + ½)`
  have hray : ∀ t : ℝ, 0 < t → xi (p₀ + t + 1 / 2) ≠ 0 := by
    intro t ht hzero
    have hval : p₀ + t + 1 / 2 = ρ₀ + t := by rw [hp₀]; unfold lagPole; rw [hq₀]; ring
    rw [hval] at hzero
    by_cases hle : (ρ₀ + t).re ≤ 1
    · have hmemK : ρ₀ + t ∈ xiZeroSet ∩ K := by
        refine ⟨hzero, ?_⟩
        rw [hK, Complex.mem_reProdIm]
        refine ⟨⟨?_, hle⟩, ?_⟩
        · simp only [Complex.add_re, Complex.ofReal_re]; linarith [hρ₀K.1.1]
        · simp only [Complex.add_im, Complex.ofReal_im, add_zero, him₀]; exact ⟨le_rfl, le_rfl⟩
      have := hmax _ hmemK (by simp only [Complex.add_re, Complex.ofReal_re]; linarith)
      simp only [Complex.add_re, Complex.ofReal_re] at this
      linarith
    · exact xi_ne_zero_of_one_le_re (not_le.mp hle).le hzero
  -- the two analytic functions along the ray
  set ℓ : ℝ → ℂ := fun t => p₀ + t with hℓ
  have hℓan : ∀ t : ℝ, AnalyticAt ℝ ℓ t := fun t =>
    analyticAt_const.add (Complex.ofRealCLM.analyticAt t)
  set V : Set ℂ := {z : ℂ | a < z.re ∧ z.re < 2} with hV
  have hVopen : IsOpen V := (isOpen_lt continuous_const Complex.continuous_re).inter
    (isOpen_lt Complex.continuous_re continuous_const)
  have hFdiff : DifferentiableOn ℂ F V := fun z hz => (hFd z hz.1 hz.2).differentiableWithinAt
  set U : Set ℝ := Ioo (0:ℝ) (2 - p₀.re) with hU
  have hℓV : ∀ t ∈ U, ℓ t ∈ V := by
    intro t ht
    simp only [hℓ, hV, Set.mem_setOf_eq, Complex.add_re, Complex.ofReal_re]
    constructor <;> linarith [ht.1, ht.2]
  have hF : AnalyticOnNhd ℝ (fun t : ℝ => F (ℓ t)) U := by
    intro t ht
    have hFz : AnalyticAt ℂ (F) (ℓ t) :=
      hFdiff.analyticAt (hVopen.mem_nhds (hℓV t ht))
    exact hFz.restrictScalars.comp (hℓan t)
  have hG : AnalyticOnNhd ℝ (fun t : ℝ => lagPoleSeries (ℓ t)) U := by
    intro t ht
    have hGz : AnalyticAt ℂ lagPoleSeries (ℓ t) := by
      have hne : xi (ℓ t + 1 / 2) ≠ 0 := hray t ht.1
      have hopen : IsOpen {z : ℂ | xi (z + 1 / 2) ≠ 0} :=
        isOpen_ne_fun (xi_differentiable.continuous.comp (continuous_id.add continuous_const))
          continuous_const
      refine DifferentiableOn.analyticAt (s := {z : ℂ | xi (z + 1 / 2) ≠ 0}) ?_ (hopen.mem_nhds hne)
      exact fun z hz => (differentiableAt_lagPoleSeries hz).differentiableWithinAt
    exact hGz.restrictScalars.comp (hℓan t)
  have hUconn : IsPreconnected U := isPreconnected_Ioo
  have h1U : (1 : ℝ) ∈ U := ⟨one_pos, by linarith⟩
  have hfg : (fun t : ℝ => F (ℓ t)) =ᶠ[𝓝 (1:ℝ)]
      (fun t : ℝ => lagPoleSeries (ℓ t)) := by
    refine Filter.eventuallyEq_of_mem
      (Ioo_mem_nhds (by norm_num : (1/2 : ℝ) < 1) (by norm_num : (1:ℝ) < 3/2)) fun t ht => ?_
    apply hFG
    simp only [hℓ, Complex.add_re, Complex.ofReal_re]
    linarith [ht.1]
  have heq := hF.eqOn_of_preconnected_of_eventuallyEq hG hUconn h1U hfg
  -- continuity of `F` at `p₀`
  have hFcont : ContinuousAt F p₀ := (hFd p₀ hp₀a (by linarith)).continuousAt
  have hℓ0 : Tendsto ℓ (𝓝 0) (𝓝 p₀) := by
    have : Tendsto (fun t : ℝ => p₀ + (t : ℂ)) (𝓝 0) (𝓝 (p₀ + ((0:ℝ) : ℂ))) :=
      tendsto_const_nhds.add (Complex.continuous_ofReal.tendsto 0)
    simpa using this
  have hcomp : Tendsto (fun t : ℝ => F (ℓ t)) (𝓝 0) (𝓝 (F p₀)) :=
    hFcont.tendsto.comp hℓ0
  obtain ⟨δ, hδ, hδF⟩ := Metric.eventually_nhds_iff.mp
    (Metric.tendsto_nhds.mp hcomp 1 one_pos)
  -- the pole bound
  obtain ⟨ε, hε, C, hC⟩ := norm_lagPoleSeries_ge q₀
  set C' : ℝ := max C 0 with hC'
  have hC0 : 0 ≤ C' := le_max_right _ _
  have hC'' : ∀ t : ℝ, 0 < t → t < ε →
      ‖lagWeight q₀‖ / t - C' ≤ ‖lagPoleSeries (lagPole q₀ + t)‖ :=
    fun t ht htε => le_trans (by linarith [le_max_left C 0]) (hC t ht htε)
  set B : ℝ := ‖F p₀‖ + 1 with hB
  have hw : 0 < ‖lagWeight q₀‖ := by
    rw [norm_pos_iff]
    unfold lagWeight
    exact one_div_ne_zero (mul_ne_zero (xiZeroCopy_ne_zero q₀) (xiZeroCopy_one_sub_ne_zero q₀))
  have hBpos : 0 < B + C' + 1 := by positivity
  have h2p : 0 < 2 - p₀.re := by linarith
  have hw' : 0 < ‖lagWeight q₀‖ / (B + C' + 1) := div_pos hw hBpos
  set m : ℝ := min (min δ ε) (min (2 - p₀.re) (‖lagWeight q₀‖ / (B + C' + 1))) with hm
  have hmpos : 0 < m := lt_min (lt_min hδ hε) (lt_min h2p hw')
  set t₀ : ℝ := m / 2 with ht₀
  have ht₀pos : 0 < t₀ := half_pos hmpos
  have hmδ : m ≤ δ := (min_le_left _ _).trans (min_le_left _ _)
  have hmε : m ≤ ε := (min_le_left _ _).trans (min_le_right _ _)
  have hm2 : m ≤ 2 - p₀.re := (min_le_right _ _).trans (min_le_left _ _)
  have hmw : m ≤ ‖lagWeight q₀‖ / (B + C' + 1) := (min_le_right _ _).trans (min_le_right _ _)
  have ht₀δ : t₀ < δ := by rw [ht₀]; linarith
  have ht₀ε : t₀ < ε := by rw [ht₀]; linarith
  have ht₀U : t₀ ∈ U := ⟨ht₀pos, by rw [ht₀]; linarith⟩
  have hFb : ‖F (ℓ t₀)‖ ≤ B := by
    have hd : dist t₀ 0 < δ := by
      rw [Real.dist_eq, sub_zero, abs_of_pos ht₀pos]; exact ht₀δ
    have := hδF hd
    rw [dist_eq_norm] at this
    calc ‖F (ℓ t₀)‖
        = ‖(F (ℓ t₀) - F p₀) + F p₀‖ := by
          congr 1; ring
      _ ≤ ‖F (ℓ t₀) - F p₀‖ + ‖F p₀‖ :=
          norm_add_le _ _
      _ ≤ 1 + ‖F p₀‖ := by linarith
      _ = B := by rw [hB]; ring
  have hGb : B < ‖lagPoleSeries (ℓ t₀)‖ := by
    have h1 := hC'' t₀ ht₀pos ht₀ε
    have h2 : 2 * (B + C' + 1) ≤ ‖lagWeight q₀‖ / t₀ := by
      rw [le_div_iff₀ ht₀pos]
      calc 2 * (B + C' + 1) * t₀ ≤ 2 * (B + C' + 1) * (‖lagWeight q₀‖ / (B + C' + 1) / 2) := by
            gcongr
            rw [ht₀]; linarith
        _ = ‖lagWeight q₀‖ := by field_simp
    have hℓt : ℓ t₀ = lagPole q₀ + t₀ := rfl
    rw [hℓt]
    linarith
  have hEq : F (ℓ t₀) = lagPoleSeries (ℓ t₀) := heq ht₀U
  rw [hEq] at hFb
  linarith

/-! ## The growth measure -/

/-- The clipped density `max(M e^{au} − Φ(u), 0)`. -/
def growthDensity (a M : ℝ) (u : ℝ) : NNReal :=
  Real.toNNReal (M * Real.exp (a * u) - weilLagFunctionReal u)

theorem measurable_growthDensity (a M : ℝ) : Measurable (growthDensity a M) :=
  ((measurable_const.mul (Real.measurable_exp.comp (measurable_const.mul measurable_id))).sub
    measurable_weilLagFunctionReal).real_toNNReal

/-- The shift density `e^{au}`. -/
def growthShiftDensity (a : ℝ) (u : ℝ) : NNReal := Real.toNNReal (Real.exp (a * u))

theorem measurable_growthShiftDensity (a : ℝ) : Measurable (growthShiftDensity a) :=
  (Real.measurable_exp.comp (measurable_const.mul measurable_id)).real_toNNReal

theorem growthShiftDensity_coe (a u : ℝ) : ((growthShiftDensity a u : ℝ)) = Real.exp (a * u) := by
  unfold growthShiftDensity
  rw [Real.coe_toNNReal _ (Real.exp_pos _).le]

/-- `(M e^{au} − Φ) du + e^{au} du` on `(0,∞)`. -/
def growthMeasure (a M : ℝ) : Measure ℝ :=
  (volume.restrict (Ioi (0:ℝ))).withDensity (fun u => (growthDensity a M u : ENNReal))
    + (volume.restrict (Ioi (0:ℝ))).withDensity (fun u => (growthShiftDensity a u : ENNReal))

/-- The density is at most `(|M| + W) e^{u/2}` for `u > 0`, when `a ≤ ½`. -/
theorem growthDensity_le {a M : ℝ} (ha : a ≤ 1 / 2) {u : ℝ} (hu : 0 < u) :
    ((growthDensity a M u : ℝ)) ≤ (|M| + lagWeightTotal) * Real.exp (u / 2) := by
  unfold growthDensity
  rw [Real.coe_toNNReal']
  have h1 := abs_weilLagFunctionReal_le u
  rw [abs_of_pos hu] at h1
  have h2 : Real.exp (a * u) ≤ Real.exp (u / 2) := Real.exp_le_exp.mpr (by nlinarith)
  have h3 : M * Real.exp (a * u) ≤ |M| * Real.exp (u / 2) := by
    calc M * Real.exp (a * u) ≤ |M| * Real.exp (a * u) :=
          mul_le_mul_of_nonneg_right (le_abs_self M) (Real.exp_pos _).le
      _ ≤ |M| * Real.exp (u / 2) := mul_le_mul_of_nonneg_left h2 (abs_nonneg M)
  have h4 := neg_abs_le (weilLagFunctionReal u)
  have hW := lagWeightTotal_nonneg
  have hE := Real.exp_pos (u / 2)
  rcases le_or_gt (M * Real.exp (a * u) - weilLagFunctionReal u) 0 with h | h
  · rw [max_eq_right h]; positivity
  · rw [max_eq_left h.le]; nlinarith

theorem integrableOn_growth_majorant {σ C : ℝ} (hσ : 1 / 2 < σ) :
    IntegrableOn (fun u : ℝ => C * Real.exp (u / 2) * Real.exp (-σ * u)) (Ioi 0) := by
  have h := (exp_neg_integrableOn_Ioi 0 (by linarith : (0:ℝ) < σ - 1 / 2)).const_mul C
  refine IntegrableOn.congr_fun h (fun u _ => ?_) measurableSet_Ioi
  rw [show Real.exp (-(σ - 1 / 2) * u) = Real.exp (u / 2) * Real.exp (-σ * u) by
    rw [← Real.exp_add]; ring_nf]
  ring

theorem laplaceMass_growth_density_ne_top {a M σ : ℝ} (ha : a ≤ 1 / 2) (hσ : 1 / 2 < σ) :
    laplaceMass ((volume.restrict (Ioi (0:ℝ))).withDensity
      (fun u => (growthDensity a M u : ENNReal))) σ ≠ ⊤ := by
  unfold laplaceMass
  have hg : Measurable (fun u : ℝ => ENNReal.ofReal (Real.exp (-σ * u))) := by measurability
  rw [restrict_withDensity measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi, inter_self,
    lintegral_withDensity_eq_lintegral_mul _ (measurable_growthDensity a M).coe_nnreal_ennreal hg]
  refine ne_top_of_le_ne_top
    (integrableOn_growth_majorant (C := |M| + lagWeightTotal) hσ).lintegral_lt_top.ne ?_
  refine lintegral_mono_ae ?_
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with u hu
  simp only [Pi.mul_apply]
  rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  exact mul_le_mul_of_nonneg_right (growthDensity_le ha hu) (Real.exp_pos _).le

/-- The shift measure has the Laplace mass of Lebesgue measure at `σ − a`. -/
theorem laplaceMass_growthShift (a σ : ℝ) :
    laplaceMass ((volume.restrict (Ioi (0:ℝ))).withDensity
      (fun u => (growthShiftDensity a u : ENNReal))) σ = laplaceMass volume (σ - a) := by
  unfold laplaceMass
  have hg : Measurable (fun u : ℝ => ENNReal.ofReal (Real.exp (-σ * u))) := by measurability
  rw [restrict_withDensity measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi, inter_self,
    lintegral_withDensity_eq_lintegral_mul _ (measurable_growthShiftDensity a).coe_nnreal_ennreal hg]
  refine lintegral_congr fun u => ?_
  simp only [Pi.mul_apply]
  rw [← ENNReal.ofReal_coe_nnreal, growthShiftDensity_coe, ← ENNReal.ofReal_mul (Real.exp_pos _).le,
    ← Real.exp_add]
  congr 2
  ring

theorem laplaceMass_growth_eq (a M σ : ℝ) :
    laplaceMass (growthMeasure a M) σ =
      laplaceMass ((volume.restrict (Ioi (0:ℝ))).withDensity
        (fun u => (growthDensity a M u : ENNReal))) σ + laplaceMass volume (σ - a) := by
  unfold laplaceMass growthMeasure
  rw [Measure.restrict_add, lintegral_add_measure]
  congr 1
  have := laplaceMass_growthShift a σ
  unfold laplaceMass at this
  exact this

/-- The real points of convergence lie in `(a, ∞)`, contain `1`, and form an up-set; their infimum
is the abscissa, which is at least `a`. -/
theorem isAbscissa_growth {a M : ℝ} (ha : a < 1 / 2) :
    IsAbscissa (growthMeasure a M) (sInf {σ : ℝ | laplaceMass (growthMeasure a M) σ ≠ ⊤}) ∧
      a ≤ sInf {σ : ℝ | laplaceMass (growthMeasure a M) σ ≠ ⊤} := by
  set S := {σ : ℝ | laplaceMass (growthMeasure a M) σ ≠ ⊤} with hS
  have hpos : ∀ σ ∈ S, a < σ := by
    intro σ hσ
    by_contra hle
    apply hσ
    rw [laplaceMass_growth_eq]
    rcases lt_or_eq_of_le (not_lt.mp hle) with h | h
    · rw [laplaceMass_volume_eq_top (by linarith), add_top]
    · rw [h, sub_self, laplaceMass_volume_zero_eq_top, add_top]
  have hbdd : BddBelow S := ⟨a, fun σ hσ => (hpos σ hσ).le⟩
  have h1S : (1:ℝ) ∈ S := by
    show laplaceMass (growthMeasure a M) 1 ≠ ⊤
    rw [laplaceMass_growth_eq]
    exact ENNReal.add_ne_top.mpr ⟨laplaceMass_growth_density_ne_top ha.le (by norm_num),
      laplaceMass_volume_ne_top (by linarith)⟩
  have hne : S.Nonempty := ⟨1, h1S⟩
  refine ⟨⟨fun σ hσ => ?_, fun σ hσ => ?_⟩, le_csInf hne fun σ hσ => (hpos σ hσ).le⟩
  · obtain ⟨σ', hσ'S, hlt⟩ := exists_lt_of_csInf_lt hne hσ
    exact ne_top_of_le_ne_top hσ'S (laplaceMass_antitone _ hlt.le)
  · by_contra h
    exact absurd (csInf_le hbdd (show σ ∈ S from h)) (not_le.mpr hσ)

/-! ## The complex transform on `Re s > ½` -/

/-- The candidate analytic continuation `H(z) = (M+1)/(z − a) − G(z)`. -/
def growthContinuation (a M : ℝ) (z : ℂ) : ℂ := (M + 1) / (z - a) - lagPoleSeries z

theorem analyticAt_growthContinuation (a M : ℝ) {z : ℂ} (hza : z ≠ a) (hz : xi (z + 1 / 2) ≠ 0) :
    AnalyticAt ℂ (growthContinuation a M) z := by
  unfold growthContinuation
  exact (analyticAt_const.div (analyticAt_id.sub analyticAt_const) (sub_ne_zero.mpr hza)).sub
    (analyticAt_lagPoleSeries hz)

theorem integrable_cexp_growth_density {a M : ℝ} (ha : a ≤ 1 / 2) {s : ℂ} (hs : 1 / 2 < s.re) :
    Integrable (fun u : ℝ => Complex.exp (-s * (u : ℂ)))
      (((volume.restrict (Ioi (0:ℝ))).withDensity
        (fun u => (growthDensity a M u : ENNReal))).restrict (Ioi 0)) := by
  rw [restrict_withDensity measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi, inter_self,
    integrable_withDensity_iff_integrable_smul (measurable_growthDensity a M)]
  refine (integrableOn_growth_majorant (C := |M| + lagWeightTotal) (by exact hs)).mono' ?_ ?_
  · exact ((measurable_growthDensity a M).coe_nnreal_real.aestronglyMeasurable.smul
      (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)).aestronglyMeasurable)
  · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with u hu
    rw [NNReal.smul_def, norm_smul, Real.norm_eq_abs, abs_of_nonneg (NNReal.coe_nonneg _),
      norm_cexp_neg_mul]
    exact mul_le_mul_of_nonneg_right (growthDensity_le ha hu) (Real.exp_pos _).le

theorem integrable_cexp_growthShift {a : ℝ} {s : ℂ} (hs : a < s.re) :
    Integrable (fun u : ℝ => Complex.exp (-s * (u : ℂ)))
      (((volume.restrict (Ioi (0:ℝ))).withDensity
        (fun u => (growthShiftDensity a u : ENNReal))).restrict (Ioi 0)) := by
  rw [restrict_withDensity measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi, inter_self,
    integrable_withDensity_iff_integrable_smul (measurable_growthShiftDensity a)]
  have hmaj : IntegrableOn (fun u : ℝ => Real.exp (-(s.re - a) * u)) (Ioi 0) :=
    exp_neg_integrableOn_Ioi 0 (by linarith)
  refine hmaj.mono' ?_ ?_
  · exact ((measurable_growthShiftDensity a).coe_nnreal_real.aestronglyMeasurable.smul
      (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)).aestronglyMeasurable)
  · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with u hu
    rw [NNReal.smul_def, norm_smul, Real.norm_eq_abs, abs_of_nonneg (NNReal.coe_nonneg _),
      norm_cexp_neg_mul, growthShiftDensity_coe, ← Real.exp_add]
    apply le_of_eq
    congr 1
    ring

/-- The complex transform of the shift measure is `1/(s − a)`. -/
theorem complexLaplace_growthShift {a : ℝ} {s : ℂ} (hs : a < s.re) :
    ∫ u in Ioi (0:ℝ), Complex.exp (-s * (u : ℂ))
      ∂((volume.restrict (Ioi (0:ℝ))).withDensity (fun u => (growthShiftDensity a u : ENNReal)))
      = 1 / (s - a) := by
  rw [restrict_withDensity measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi, inter_self,
    integral_withDensity_eq_integral_smul (measurable_growthShiftDensity a)]
  have hpt : ∀ u ∈ Ioi (0:ℝ), growthShiftDensity a u • Complex.exp (-s * (u : ℂ))
      = Complex.exp (-(s - a) * (u : ℂ)) := by
    intro u _
    rw [NNReal.smul_def, Complex.real_smul, growthShiftDensity_coe, Complex.ofReal_exp,
      ← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi hpt]
  exact integral_cexp_neg_mul_Ioi (by simp; linarith)

/-- On `Re s > ½` the complex Laplace transform of the growth measure is `H(s)`. -/
theorem complexLaplace_growth_eq {a M : ℝ} (ha : a < 1 / 2)
    (hM : ∀ L, 0 ≤ L → weilLagFunctionReal L ≤ M * Real.exp (a * L)) {s : ℂ} (hs : 1 / 2 < s.re) :
    complexLaplace (growthMeasure a M) s = growthContinuation a M s := by
  have hs0 : 0 < s.re := by linarith
  have hsa : a < s.re := by linarith
  have hsa' : 0 < (s - a).re := by simp; linarith
  have hcexp : Continuous (fun u : ℝ => Complex.exp (-s * (u : ℂ))) :=
    Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)
  have hexpInt : IntegrableOn (fun u : ℝ => Complex.exp (-s * (u : ℂ))) (Ioi 0) :=
    (exp_neg_integrableOn_Ioi 0 hs0).mono' hcexp.aestronglyMeasurable
      (Filter.Eventually.of_forall fun u => le_of_eq (norm_cexp_neg_mul _ u))
  have hexpInt' : IntegrableOn (fun u : ℝ => Complex.exp (-(s - a) * (u : ℂ))) (Ioi 0) := by
    have hc : Continuous (fun u : ℝ => Complex.exp (-(s - a) * (u : ℂ))) :=
      Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)
    exact (exp_neg_integrableOn_Ioi 0 hsa').mono' hc.aestronglyMeasurable
      (Filter.Eventually.of_forall fun u => le_of_eq (norm_cexp_neg_mul _ u))
  unfold complexLaplace growthMeasure growthContinuation
  rw [Measure.restrict_add, integral_add_measure (integrable_cexp_growth_density ha.le hs)
    (integrable_cexp_growthShift hsa), complexLaplace_growthShift hsa]
  rw [restrict_withDensity measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi, inter_self,
    integral_withDensity_eq_integral_smul (measurable_growthDensity a M)]
  have hpt : ∀ u ∈ Ioi (0:ℝ), growthDensity a M u • Complex.exp (-s * (u : ℂ)) =
      (M : ℂ) * Complex.exp (-(s - a) * (u : ℂ)) -
        ((weilLagFunctionReal u : ℂ) * Complex.exp (-s * (u : ℂ))) := by
    intro u hu
    rw [NNReal.smul_def, Complex.real_smul]
    unfold growthDensity
    rw [Real.coe_toNNReal _ (by linarith [hM u (le_of_lt hu)])]
    push_cast
    rw [show Complex.exp (-(s - a) * (u : ℂ)) = Complex.exp (a * u) * Complex.exp (-s * (u : ℂ)) by
      rw [← Complex.exp_add]; congr 1; ring]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi hpt,
    integral_sub (hexpInt'.const_mul _) (integrable_weilLag_mul_cexp hs),
    integral_const_mul, integral_cexp_neg_mul_Ioi hsa']
  have hΦ : ∫ u in Ioi (0:ℝ), (weilLagFunctionReal u : ℂ) * Complex.exp (-s * (u : ℂ)) =
      lagPoleSeries s := by
    rw [← integral_weilLagFunction_mul_cexp hs]
    exact integral_congr_ae (Filter.Eventually.of_forall fun u => by
      beta_reduce; rw [weilLagFunction_eq_ofReal])
  rw [hΦ]
  have hne : (s - a) ≠ 0 := fun h => by
    have := congrArg Complex.re h; simp at this; linarith
  field_simp
  ring

/-! ## Landau: the abscissa is `a` -/

theorem abscissa_growth_eq {a M : ℝ} (ha0 : 0 ≤ a) (ha : a < 1 / 2)
    (hM : ∀ L, 0 ≤ L → weilLagFunctionReal L ≤ M * Real.exp (a * L)) :
    IsAbscissa (growthMeasure a M) a := by
  obtain ⟨hc, hac⟩ := isAbscissa_growth (M := M) ha
  set c : ℝ := sInf {σ : ℝ | laplaceMass (growthMeasure a M) σ ≠ ⊤} with hcdef
  rcases hac.lt_or_eq with hpos | hzero
  · exfalso
    have hc34 : c ≤ 3 / 4 := by
      refine csInf_le ⟨a, fun σ hσ => ?_⟩ ?_
      · by_contra hlt
        apply hσ
        rw [laplaceMass_growth_eq, laplaceMass_volume_eq_top (by linarith [not_le.mp hlt]), add_top]
      · show laplaceMass (growthMeasure a M) (3 / 4) ≠ ⊤
        rw [laplaceMass_growth_eq]
        exact ENNReal.add_ne_top.mpr ⟨laplaceMass_growth_density_ne_top ha.le (by norm_num),
          laplaceMass_volume_ne_top (by linarith)⟩
    have hcpos : 0 < c := lt_of_le_of_lt ha0 hpos
    have hne : xi ((c : ℂ) + 1 / 2) ≠ 0 := xi_ofReal_add_half_ne_zero hcpos
    have hopen : IsOpen {z : ℂ | xi z ≠ 0} := isOpen_ne_fun xi_differentiable.continuous continuous_const
    obtain ⟨d, hd, hball⟩ := Metric.isOpen_iff.mp hopen _ hne
    set δ : ℝ := min (c - a) d / 2 with hδdef
    have hδ : 0 < δ := by rw [hδdef]; exact half_pos (lt_min (by linarith) hd)
    have hδc : δ ≤ (c - a) / 2 := by rw [hδdef]; linarith [min_le_left (c - a) d]
    have hδd : δ ≤ d / 2 := by rw [hδdef]; linarith [min_le_right (c - a) d]
    refine false_of_analyticAt_abscissa hc hδ (Φ := growthContinuation a M) ?_ ?_
    · intro z hz
      rw [Metric.mem_ball, Complex.dist_eq] at hz
      have hzre : (c + a) / 2 < z.re := by
        have := Complex.abs_re_le_norm (z - c)
        rw [Complex.sub_re, Complex.ofReal_re] at this
        have := abs_le.mp this
        linarith
      have hza : z ≠ a := fun h => by rw [h] at hzre; simp at hzre; linarith
      have hzxi : xi (z + 1 / 2) ≠ 0 := by
        apply hball
        rw [Metric.mem_ball, Complex.dist_eq]
        calc ‖z + 1 / 2 - ((c : ℂ) + 1 / 2)‖ = ‖z - c‖ := by congr 1; ring
          _ < δ := hz
          _ ≤ d / 2 := hδd
          _ < d := by linarith
      exact analyticAt_growthContinuation a M hza hzxi
    · intro σ hσc _
      have hV : IsOpen {z : ℂ | c < z.re} := isOpen_lt continuous_const Complex.continuous_re
      have hTdiff : DifferentiableOn ℂ (complexLaplace (growthMeasure a M)) {z : ℂ | c < z.re} :=
        fun z hz => (hasDerivAt_complexLaplace hc hz).differentiableAt.differentiableWithinAt
      have hT : AnalyticOnNhd ℝ (fun t : ℝ => complexLaplace (growthMeasure a M) (t : ℂ)) (Ioi c) := by
        intro t ht
        have h1 : AnalyticAt ℂ (complexLaplace (growthMeasure a M)) (t : ℂ) :=
          hTdiff.analyticAt (hV.mem_nhds (by simpa using ht))
        exact h1.restrictScalars.comp (Complex.ofRealCLM.analyticAt t)
      have hH : AnalyticOnNhd ℝ (fun t : ℝ => growthContinuation a M (t : ℂ)) (Ioi c) := by
        intro t ht
        have hta : a < t := lt_trans hpos ht
        have ht0 : 0 < t := lt_of_le_of_lt ha0 hta
        have h1 : AnalyticAt ℂ (growthContinuation a M) (t : ℂ) :=
          analyticAt_growthContinuation a M (by exact_mod_cast hta.ne')
            (xi_ofReal_add_half_ne_zero ht0)
        exact h1.restrictScalars.comp (Complex.ofRealCLM.analyticAt t)
      have h1mem : (1 : ℝ) ∈ Ioi c := by show c < 1; linarith
      have hfg : (fun t : ℝ => complexLaplace (growthMeasure a M) (t : ℂ)) =ᶠ[𝓝 (1:ℝ)]
          (fun t : ℝ => growthContinuation a M (t : ℂ)) := by
        refine Filter.eventuallyEq_of_mem
          (Ioo_mem_nhds (by norm_num : (1/2 : ℝ) < 1) (by norm_num : (1:ℝ) < 3/2)) fun t ht => ?_
        exact complexLaplace_growth_eq ha hM (by simpa using ht.1)
      have heq := hT.eqOn_of_preconnected_of_eventuallyEq hH isPreconnected_Ioi h1mem hfg
      have hσ : complexLaplace (growthMeasure a M) (σ : ℂ) = growthContinuation a M (σ : ℂ) :=
        heq (show σ ∈ Ioi c from hσc)
      rw [← hσ, complexLaplace_ofReal]
  · rw [← hzero] at hc
    exact hc

/-! ## The growth criterion -/

/-- **One-sided exponential growth of the lag function bounds the real parts of the zeros.**
If `Φ(L) ≤ M e^{aL}` for all `L ≥ 0` with `0 ≤ a < ½`, every zero copy has real part at most
`½ + a`. -/
theorem re_le_half_add_of_weilLagFunctionReal_le_exp {a M : ℝ} (ha0 : 0 ≤ a) (ha : a < 1 / 2)
    (hM : ∀ L, 0 ≤ L → weilLagFunctionReal L ≤ M * Real.exp (a * L)) (q : XiZeroCopy) :
    (q.1 : ℂ).re ≤ 1 / 2 + a := by
  have hc := abscissa_growth_eq ha0 ha hM
  refine re_le_half_add_of_lagPoleSeries_extension ha0
    (F := fun z => ((M : ℂ) + 1) / (z - a) - complexLaplace (growthMeasure a M) z) ?_ ?_ q
  · intro z hza _
    have hz : z - a ≠ 0 := fun h => by
      have := congrArg Complex.re h; simp at this; linarith
    have h1 : DifferentiableAt ℂ (fun z : ℂ => ((M : ℂ) + 1) / (z - a)) z :=
      (differentiableAt_const _).div (differentiableAt_id.sub (differentiableAt_const _)) hz
    have h2 : DifferentiableAt ℂ (complexLaplace (growthMeasure a M)) z :=
      (hasDerivAt_complexLaplace hc hza).differentiableAt
    exact h1.sub h2
  · intro s hs
    rw [complexLaplace_growth_eq ha hM hs]
    unfold growthContinuation
    ring

end

end RHTower
