import GaloisForLFunctions.RHTower.FZZCigarParityReflectedFermiInformationGradientFlow
import GaloisForLFunctions.RHTower.ThetaCuspHawkingPreDivisorOpticalCancellationHolomorphyObstruction
import GaloisForLFunctions.Bottcher.InteriorModulusObstruction

/-!
# FZZ source-global holomorphic Fermi-flow obstruction

The exact reflected-Fermi velocity diverges at the hard Mellin edge. In contrast, a holomorphic
vector field on the open unit strip whose real part depends only on the horizontal coordinate has
an affine horizontal profile. Therefore the exact Fermi velocity cannot be realized by a single
source-global holomorphic, horizontally stratified FZZ/PW generator.

The affine-profile theorem is the positive survivor: any exact realization must introduce ordinate
dependence, an antiholomorphic component, a singular boundary domain, or divisor/source feedback.
-/

open Complex MeasureTheory Set Filter Topology

namespace RHTower

noncomputable section

theorem integral_Ioc_rpow_sigma_sub_one {σ : ℝ} (hσ : 0 < σ) :
    (∫ t in Ioc (0 : ℝ) 1, t ^ (σ - 1)) = 1 / σ := by
  rw [← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  rw [integral_rpow (Or.inl (by linarith : -1 < σ - 1))]
  rw [show σ - 1 + 1 = σ by ring, Real.one_rpow,
    Real.zero_rpow hσ.ne']
  norm_num

theorem fermiMellinNormalizer_reciprocal_lower {σ : ℝ} (hσ : 0 < σ) :
    (Real.exp 1 + 1)⁻¹ / σ ≤ fermiMellinNormalizer σ := by
  have hposC : 0 < (Real.exp 1 + 1)⁻¹ := by positivity
  have hsub : Ioc (0 : ℝ) 1 ⊆ Ioi 0 := by intro t ht; exact ht.1
  have hnonneg : 0 ≤ᵐ[volume.restrict (Ioi 0)] fermiMellinDensity σ := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact (fermiMellinDensity_pos (σ := σ) ht).le
  have hset :
      (∫ t in Ioc (0 : ℝ) 1, fermiMellinDensity σ t) ≤
        ∫ t in Ioi 0, fermiMellinDensity σ t := by
    exact setIntegral_mono_set (integrableOn_fermiMellinDensity hσ) hnonneg
      (Filter.Eventually.of_forall hsub)
  have hpoint : ∀ t ∈ Ioc (0 : ℝ) 1,
      (Real.exp 1 + 1)⁻¹ * t ^ (σ - 1) ≤ fermiMellinDensity σ t := by
    intro t ht
    rw [fermiMellinDensity]
    have hexp : Real.exp t + 1 ≤ Real.exp 1 + 1 := by
      gcongr
      exact ht.2
    have hinv : (Real.exp 1 + 1)⁻¹ ≤ (Real.exp t + 1)⁻¹ := by
      exact inv_anti₀ (by positivity) hexp
    rw [mul_comm (t ^ (σ - 1))]
    exact mul_le_mul_of_nonneg_right hinv (Real.rpow_nonneg ht.1.le _)
  have hintLeft : IntegrableOn (fun t : ℝ => (Real.exp 1 + 1)⁻¹ * t ^ (σ - 1))
      (Ioc 0 1) := by
    exact (intervalIntegral.intervalIntegrable_rpow' (by linarith : -1 < σ - 1)).1.const_mul _
  have hintRight : IntegrableOn (fermiMellinDensity σ) (Ioc 0 1) :=
    (integrableOn_fermiMellinDensity hσ).mono_set hsub
  have hmono :
      (∫ t in Ioc (0 : ℝ) 1, (Real.exp 1 + 1)⁻¹ * t ^ (σ - 1)) ≤
        ∫ t in Ioc (0 : ℝ) 1, fermiMellinDensity σ t :=
    setIntegral_mono_on hintLeft hintRight measurableSet_Ioc hpoint
  rw [integral_const_mul, integral_Ioc_rpow_sigma_sub_one hσ] at hmono
  rw [fermiMellinNormalizer]
  simpa [div_eq_mul_inv, mul_comm] using hmono.trans hset

theorem tendsto_fermiMellinNormalizer_nhdsGT_zero_atTop :
    Tendsto fermiMellinNormalizer (𝓝[>] (0 : ℝ)) atTop := by
  have hbase : Tendsto (fun σ : ℝ => (Real.exp 1 + 1)⁻¹ * σ⁻¹)
      (𝓝[>] (0 : ℝ)) atTop :=
    tendsto_inv_nhdsGT_zero.const_mul_atTop (by positivity)
  rw [Filter.tendsto_atTop] at hbase ⊢
  intro B
  filter_upwards [hbase B, self_mem_nhdsWithin] with σ hB hσ
  exact hB.trans (by
    simpa [div_eq_mul_inv] using fermiMellinNormalizer_reciprocal_lower hσ)

theorem tendsto_fermiLogPartition_nhdsGT_zero_atTop :
    Tendsto fermiLogPartition (𝓝[>] (0 : ℝ)) atTop := by
  exact Real.tendsto_log_atTop.comp tendsto_fermiMellinNormalizer_nhdsGT_zero_atTop

theorem tendsto_fermiLogMean_nhdsGT_zero_atBot :
    Tendsto fermiLogMean (𝓝[>] (0 : ℝ)) atBot := by
  rw [Filter.tendsto_atBot]
  intro B
  have hL := (Filter.tendsto_atTop.1 tendsto_fermiLogPartition_nhdsGT_zero_atTop)
    (fermiLogPartition (1 / 2) + |B| / 2)
  have hsmall : Iio (1 / 2 : ℝ) ∈ 𝓝[>] (0 : ℝ) :=
    mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (show (0 : ℝ) < 1 / 2 by norm_num))
  filter_upwards [hL, self_mem_nhdsWithin, hsmall] with σ hlarge hσ hhalf
  have hσ0 : 0 < σ := hσ
  have hσhalf : σ < 1 / 2 := hhalf
  have hcont : ContinuousOn fermiLogPartition (Icc σ (1 / 2)) := by
    intro x hx
    exact (hasDerivAt_fermiLogPartition (by linarith [hx.1])).continuousAt.continuousWithinAt
  have hderiv : ∀ x ∈ Ioo σ (1 / 2),
      HasDerivAt fermiLogPartition (fermiLogMean x) x := by
    intro x hx
    exact hasDerivAt_fermiLogPartition (by linarith [hx.1])
  obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope
    fermiLogPartition fermiLogMean hhalf hcont hderiv
  have hc0 : 0 < c := lt_trans hσ0 hc.1
  have hmono : fermiLogMean σ < fermiLogMean c :=
    fermiLogMean_strictMonoOn hσ0 hc0 hc.1
  have hden : 0 < (1 / 2 : ℝ) - σ := by linarith [hσhalf]
  have hslope' : fermiLogMean c * ((1 / 2 : ℝ) - σ) =
      fermiLogPartition (1 / 2) - fermiLogPartition σ := by
    exact (eq_div_iff hden.ne').mp hslope
  have htarget :
      fermiLogPartition (1 / 2) - fermiLogPartition σ ≤
        B * ((1 / 2 : ℝ) - σ) := by
    have hwidth : |B| * ((1 / 2 : ℝ) - σ) ≤ |B| / 2 := by
      have hσle : σ ≤ 1 / 2 := hhalf.le
      have hσnonneg : 0 ≤ σ := hσ.le
      nlinarith [abs_nonneg B]
    have hB : B * ((1 / 2 : ℝ) - σ) ≥ -|B| / 2 := by
      have habs : -|B| ≤ B := neg_abs_le B
      have := mul_le_mul_of_nonneg_right habs hden.le
      nlinarith [hwidth]
    linarith
  have hcB : fermiLogMean c ≤ B := by
    rw [← hslope'] at htarget
    nlinarith
  exact hmono.le.trans hcB

theorem tendsto_fzzCigarParityReflectedFermiInformationForce_nhdsGT_zero_atBot :
    Tendsto fzzCigarParityReflectedFermiInformationForce
      (𝓝[>] (0 : ℝ)) atBot := by
  rw [Filter.tendsto_atBot]
  intro B
  have hm := (Filter.tendsto_atBot.1 tendsto_fermiLogMean_nhdsGT_zero_atBot)
    (B / 2 + fermiLogMean (1 / 2))
  have hsmall : Iio (1 / 2 : ℝ) ∈ 𝓝[>] (0 : ℝ) :=
    mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (show (0 : ℝ) < 1 / 2 by norm_num))
  filter_upwards [hm, self_mem_nhdsWithin, hsmall] with σ hmσ hσ hhalf
  have hσ0 : 0 < σ := hσ
  have hσhalf : σ < 1 / 2 := hhalf
  have href0 : 0 < 1 - σ := by linarith
  have hrefhalf : 1 / 2 < 1 - σ := by linarith
  have hmean : fermiLogMean (1 / 2) < fermiLogMean (1 - σ) :=
    fermiLogMean_strictMonoOn (by norm_num) href0 hrefhalf
  have hvσ := fermiLogVariance_pos hσ0
  have hvref := fermiLogVariance_pos href0
  rw [fzzCigarParityReflectedFermiInformationForce]
  nlinarith

theorem tendsto_fzzCigarParityReflectedFermiInformationVelocity_nhdsGT_zero_atTop :
    Tendsto fzzCigarParityReflectedFermiInformationVelocity
      (𝓝[>] (0 : ℝ)) atTop := by
  rw [Filter.tendsto_atTop]
  intro B
  have hf := (Filter.tendsto_atBot.1
    tendsto_fzzCigarParityReflectedFermiInformationForce_nhdsGT_zero_atBot) (-B)
  filter_upwards [hf] with σ hσ
  rw [fzzCigarParityReflectedFermiInformationVelocity]
  linarith

def fzzSourceOpenUnitStrip : Set ℂ := {z : ℂ | 0 < z.re ∧ z.re < 1}

private theorem isOpen_fzzSourceOpenUnitStrip : IsOpen fzzSourceOpenUnitStrip := by
  rw [fzzSourceOpenUnitStrip]
  exact isOpen_criticalOpenStrip

private theorem isPreconnected_fzzSourceOpenUnitStrip : IsPreconnected fzzSourceOpenUnitStrip := by
  rw [fzzSourceOpenUnitStrip]
  exact isPreconnected_criticalStrip

private theorem ofReal_half_mem_fzzSourceOpenUnitStrip : ((1 / 2 : ℝ) : ℂ) ∈ fzzSourceOpenUnitStrip := by
  norm_num [fzzSourceOpenUnitStrip]

theorem analytic_horizontalRealPart_verticalIncrement_exp_constant
    (G : ℂ → ℂ) (hG : AnalyticOnNhd ℂ G fzzSourceOpenUnitStrip)
    (v : ℝ → ℝ)
    (hprofile : ∀ z ∈ fzzSourceOpenUnitStrip, (G z).re = v z.re)
    (t : ℝ) :
    Set.EqOn
      (fun z : ℂ => Complex.exp (G (z + (t : ℂ) * I) - G z))
      (fun _ : ℂ => Complex.exp
        (G (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) - G ((1 / 2 : ℝ) : ℂ)))
      fzzSourceOpenUnitStrip := by
  let T : ℂ → ℂ := fun z => z + (t : ℂ) * I
  have hT : AnalyticOnNhd ℂ T fzzSourceOpenUnitStrip := by
    have h := (analyticOnNhd_id.add analyticOnNhd_const :
      AnalyticOnNhd ℂ ((fun z : ℂ => z) + fun _ : ℂ => (t : ℂ) * I) fzzSourceOpenUnitStrip)
    convert h using 1
    funext z
    simp [T]
  have hTmap : MapsTo T fzzSourceOpenUnitStrip fzzSourceOpenUnitStrip := by
    intro z hz
    simpa [T, fzzSourceOpenUnitStrip] using hz
  have hGT : AnalyticOnNhd ℂ (fun z => G (T z)) fzzSourceOpenUnitStrip := by
    change AnalyticOnNhd ℂ (G ∘ T) fzzSourceOpenUnitStrip
    exact hG.comp hT hTmap
  have hExp : AnalyticOnNhd ℂ
      (fun z => Complex.exp (G (T z) - G z)) fzzSourceOpenUnitStrip := by
    exact (hGT.sub hG).cexp
  have hnorm : ∀ z ∈ fzzSourceOpenUnitStrip,
      ‖Complex.exp (G (T z) - G z)‖ =
        ‖Complex.exp
          (G (T ((1 / 2 : ℝ) : ℂ)) - G ((1 / 2 : ℝ) : ℂ))‖ := by
    intro z hz
    rw [Complex.norm_exp, Complex.norm_exp]
    have hTz : T z ∈ fzzSourceOpenUnitStrip := hTmap hz
    have hh : ((1 / 2 : ℝ) : ℂ) ∈ fzzSourceOpenUnitStrip := ofReal_half_mem_fzzSourceOpenUnitStrip
    have hTh : T ((1 / 2 : ℝ) : ℂ) ∈ fzzSourceOpenUnitStrip := hTmap hh
    change Real.exp ((G (T z)).re - (G z).re) =
      Real.exp ((G (T ((1 / 2 : ℝ) : ℂ))).re - (G ((1 / 2 : ℝ) : ℂ)).re)
    rw [hprofile (T z) hTz, hprofile z hz,
      hprofile (T ((1 / 2 : ℝ) : ℂ)) hTh,
      hprofile ((1 / 2 : ℝ) : ℂ) hh]
    simp [T]
  simpa [T] using Bottcher.eqOn_const_of_norm_const
    isPreconnected_fzzSourceOpenUnitStrip isOpen_fzzSourceOpenUnitStrip hExp.differentiableOn
    ofReal_half_mem_fzzSourceOpenUnitStrip hnorm

theorem deriv_analytic_horizontalRealPart_add_im_eq
    (G : ℂ → ℂ) (hG : AnalyticOnNhd ℂ G fzzSourceOpenUnitStrip)
    (v : ℝ → ℝ)
    (hprofile : ∀ z ∈ fzzSourceOpenUnitStrip, (G z).re = v z.re)
    (z : ℂ) (hz : z ∈ fzzSourceOpenUnitStrip) (t : ℝ) :
    deriv G (z + (t : ℂ) * I) = deriv G z := by
  let T : ℂ → ℂ := fun w => w + (t : ℂ) * I
  let D : ℂ → ℂ := (G ∘ T) - G
  let E : ℂ → ℂ := Complex.exp ∘ D
  have hEq := analytic_horizontalRealPart_verticalIncrement_exp_constant
    G hG v hprofile t
  have hev : E =ᶠ[𝓝 z] fun _ : ℂ => E ((1 / 2 : ℝ) : ℂ) := by
    apply Filter.eventuallyEq_of_mem (isOpen_fzzSourceOpenUnitStrip.mem_nhds hz)
    intro w hw
    simpa [E, D, T, Function.comp_apply] using hEq hw
  have hderivE : deriv E z = 0 := by
    rw [hev.deriv_eq]
    simp
  have hTz : T z ∈ fzzSourceOpenUnitStrip := by
    simpa [T, fzzSourceOpenUnitStrip] using hz
  have hGz : HasDerivAt G (deriv G z) z :=
    (hG.differentiableOn.differentiableAt
      (isOpen_fzzSourceOpenUnitStrip.mem_nhds hz)).hasDerivAt
  have hGTz : HasDerivAt G (deriv G (T z)) (T z) :=
    (hG.differentiableOn.differentiableAt
      (isOpen_fzzSourceOpenUnitStrip.mem_nhds hTz)).hasDerivAt
  have hTderiv : HasDerivAt T 1 z := by
    simpa [T] using (hasDerivAt_id z).add_const ((t : ℂ) * I)
  have hcomp0 := hGTz.comp z hTderiv
  have hsub : HasDerivAt D (deriv G (T z) - deriv G z) z := by
    simpa only [D, Pi.sub_apply, mul_one] using hcomp0.sub hGz
  have hE : HasDerivAt E
      (Complex.exp (D z) * (deriv G (T z) - deriv G z)) z := by
    exact (Complex.hasDerivAt_exp (D z)).comp z hsub
  rw [hE.deriv] at hderivE
  exact sub_eq_zero.mp (mul_eq_zero.mp hderivE |>.resolve_left (Complex.exp_ne_zero _))

theorem deriv_analytic_horizontalRealPart_eq_center
    (G : ℂ → ℂ) (hG : AnalyticOnNhd ℂ G fzzSourceOpenUnitStrip)
    (v : ℝ → ℝ)
    (hprofile : ∀ z ∈ fzzSourceOpenUnitStrip, (G z).re = v z.re) :
    ∀ z ∈ fzzSourceOpenUnitStrip,
      deriv G z = deriv G ((1 / 2 : ℝ) : ℂ) := by
  have hderivProfile : ∀ z ∈ fzzSourceOpenUnitStrip,
      deriv G z = deriv G (z.re : ℂ) := by
    intro z hz
    have hbase : (z.re : ℂ) ∈ fzzSourceOpenUnitStrip := by
      simpa [fzzSourceOpenUnitStrip] using hz
    have h := deriv_analytic_horizontalRealPart_add_im_eq
      G hG v hprofile (z.re : ℂ) hbase z.im
    have hzform : (z.re : ℂ) + (z.im : ℂ) * I = z := by
      apply Complex.ext <;> simp
    rw [hzform] at h
    exact h
  have hconst := analyticOnNhd_openCriticalStrip_constant_of_eq_realProfile
    (deriv G) hG.deriv (fun x : ℝ => deriv G (x : ℂ)) hderivProfile
  intro z hz
  exact hconst z hz ((1 / 2 : ℝ) : ℂ) ofReal_half_mem_fzzSourceOpenUnitStrip

theorem hasDerivAt_realPart_ofReal_analytic_horizontalRealPart
    (G : ℂ → ℂ) (hG : AnalyticOnNhd ℂ G fzzSourceOpenUnitStrip)
    (v : ℝ → ℝ)
    (hprofile : ∀ z ∈ fzzSourceOpenUnitStrip, (G z).re = v z.re)
    {x : ℝ} (h0 : 0 < x) (h1 : x < 1) :
    HasDerivAt (fun y : ℝ => (G (y : ℂ)).re)
      (deriv G ((1 / 2 : ℝ) : ℂ)).re x := by
  have hx : (x : ℂ) ∈ fzzSourceOpenUnitStrip := by
    change 0 < x ∧ x < 1
    exact ⟨h0, h1⟩
  have hGx : HasDerivAt G (deriv G (x : ℂ)) (x : ℂ) :=
    (hG.differentiableOn.differentiableAt
      (isOpen_fzzSourceOpenUnitStrip.mem_nhds hx)).hasDerivAt
  have hconst := deriv_analytic_horizontalRealPart_eq_center G hG v hprofile (x : ℂ) hx
  rw [hconst] at hGx
  exact Complex.reCLM.hasFDerivAt.comp_hasDerivAt x hGx.comp_ofReal

theorem analytic_horizontalRealPart_profile_affine
    (G : ℂ → ℂ) (hG : AnalyticOnNhd ℂ G fzzSourceOpenUnitStrip)
    (v : ℝ → ℝ)
    (hprofile : ∀ z ∈ fzzSourceOpenUnitStrip, (G z).re = v z.re) :
    ∃ a b : ℝ, ∀ x : ℝ, 0 < x → x < 1 → v x = a * x + b := by
  let R : ℝ → ℝ := fun y : ℝ => (G (y : ℂ)).re
  let a : ℝ := (deriv G ((1 / 2 : ℝ) : ℂ)).re
  let b : ℝ := v (1 / 2) - a * (1 / 2)
  refine ⟨a, b, ?_⟩
  intro x hx0 hx1
  have hRx : R x = v x := by
    simpa [R, Function.comp_apply] using hprofile (x : ℂ) (by
      change 0 < x ∧ x < 1
      exact ⟨hx0, hx1⟩)
  have hRh : R (1 / 2) = v (1 / 2) := by
    simpa [R] using hprofile ((1 / 2 : ℝ) : ℂ) ofReal_half_mem_fzzSourceOpenUnitStrip
  rcases lt_trichotomy x (1 / 2) with hlt | heq | hgt
  · have hcont : ContinuousOn R (Icc x (1 / 2)) := by
      intro y hy
      have hy0 : 0 < y := lt_of_lt_of_le hx0 hy.1
      have hy1 : y < 1 := lt_of_le_of_lt hy.2 (by norm_num)
      exact (hasDerivAt_realPart_ofReal_analytic_horizontalRealPart
        G hG v hprofile hy0 hy1).continuousAt.continuousWithinAt
    have hd : ∀ y ∈ Ioo x (1 / 2), HasDerivAt R a y := by
      intro y hy
      have hy0 : 0 < y := lt_trans hx0 hy.1
      have hy1 : y < 1 := lt_trans hy.2 (by norm_num)
      simpa [R, a] using hasDerivAt_realPart_ofReal_analytic_horizontalRealPart
        G hG v hprofile hy0 hy1
    obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope R (fun _ => a) hlt hcont hd
    rw [hRx, hRh] at hslope
    dsimp [b]
    have hden : (1 / 2 : ℝ) - x ≠ 0 := by linarith
    have hslope' := (eq_div_iff hden).mp hslope
    linarith
  · subst x
    simp [b]
  · have hcont : ContinuousOn R (Icc (1 / 2) x) := by
      intro y hy
      have hy0 : 0 < y := lt_of_lt_of_le (by norm_num) hy.1
      have hy1 : y < 1 := lt_of_le_of_lt hy.2 hx1
      exact (hasDerivAt_realPart_ofReal_analytic_horizontalRealPart
        G hG v hprofile hy0 hy1).continuousAt.continuousWithinAt
    have hd : ∀ y ∈ Ioo (1 / 2) x, HasDerivAt R a y := by
      intro y hy
      have hy0 : 0 < y := lt_trans (by norm_num) hy.1
      have hy1 : y < 1 := lt_trans hy.2 hx1
      simpa [R, a] using hasDerivAt_realPart_ofReal_analytic_horizontalRealPart
        G hG v hprofile hy0 hy1
    obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope R (fun _ => a) hgt hcont hd
    rw [hRx, hRh] at hslope
    dsimp [b]
    have hden : x - (1 / 2 : ℝ) ≠ 0 := by linarith
    have hslope' := (eq_div_iff hden).mp hslope
    linarith

/-- No holomorphic vector field on the open unit strip has the exact reflected-Fermi
horizontal velocity as a horizontal-stratified real part. -/
theorem not_exists_analytic_horizontalRealPart_eq_fzzCigarParityReflectedFermiInformationVelocity :
    ¬ ∃ G : ℂ → ℂ,
      AnalyticOnNhd ℂ G fzzSourceOpenUnitStrip ∧
      ∀ z ∈ fzzSourceOpenUnitStrip,
        (G z).re = fzzCigarParityReflectedFermiInformationVelocity z.re := by
  rintro ⟨G, hG, hprofile⟩
  obtain ⟨a, b, haffine⟩ := analytic_horizontalRealPart_profile_affine
    G hG fzzCigarParityReflectedFermiInformationVelocity hprofile
  have hlarge := (Filter.tendsto_atTop.1
    tendsto_fzzCigarParityReflectedFermiInformationVelocity_nhdsGT_zero_atTop)
      (|a| + |b| + 1)
  have hsmall : Iio (1 : ℝ) ∈ 𝓝[>] (0 : ℝ) :=
    mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (by norm_num))
  have hpos : Ioi (0 : ℝ) ∈ 𝓝[>] (0 : ℝ) := self_mem_nhdsWithin
  have hall : ∀ᶠ σ in 𝓝[>] (0 : ℝ),
      |a| + |b| + 1 ≤ fzzCigarParityReflectedFermiInformationVelocity σ ∧
        σ ∈ Ioi 0 ∧ σ ∈ Iio 1 :=
    by
      filter_upwards [hlarge, hpos, hsmall] with σ hσlarge hσ0 hσ1
      exact ⟨hσlarge, hσ0, hσ1⟩
  obtain ⟨σ, hσlarge, hσ0, hσ1⟩ := hall.exists
  have haσ : a * σ ≤ |a| := by
    calc
      a * σ ≤ |a| * σ := mul_le_mul_of_nonneg_right (le_abs_self a) hσ0.le
      _ ≤ |a| := mul_le_of_le_one_right (abs_nonneg a) hσ1.le
  have hb : b ≤ |b| := le_abs_self b
  have heq := haffine σ hσ0 hσ1
  linarith

end
end RHTower
