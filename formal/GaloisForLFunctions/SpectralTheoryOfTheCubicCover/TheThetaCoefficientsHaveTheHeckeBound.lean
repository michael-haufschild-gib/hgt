import GaloisForLFunctions.SpectralTheoryOfTheCubicCover.TheSquareOfTheSourceThetaUnfolds
import GaloisForLFunctions.SpectralTheoryOfTheCubicCover.TheCuspHeightsOfAPointAreSparse

/-!
# The theta coefficients have the Hecke bound

The Fourier coefficients `T_s(h)` of the projected cubic theta function `θ_s` satisfy
`|T_s(h)| ≤ C (1 + |ξ_h|)` for every `h ≠ 0` (`sourceCoefficient_hecke_bound`), with `ξ_h` the cusp
frequency of `h` (`|ξ_h| = |h|/(3√3)`). The bound holds at every frequency, ramified or not, and
comes from the square integrability of `θ_s` on the quotient alone.

* `periodArea_mul_norm_sq_le` (**one Fourier coefficient**): `|P| |a_k|² ≤ ∫_P |Σ_h a_h e(ξ_h z)|² dz`,
  from `|P| |a_k| ≤ ∫_P |S|` and `2|a_k||S| ≤ |S|² + |a_k|²`.
* `cuspStrip_lintegral`: `∫⁻_{strip} G dμ = ∫⁻_0^∞ ∫⁻_P G(z + jv) v^{−3} dz dv` for measurable `G ≥ 0`.
* `sourceTheta_lintegral_sq_lt_top`: `∫_{D_Γ} |θ_s|² dμ < ∞`. `θ_s` represents the rational source
  projection of the residual vector of the cubic Eisenstein series, an element of `L²` of the kernel
  quotient, and the fundamental set of `Γ` lies in the fundamental set of the kernel.
* `tsum_heightWindow_le`: a point has at most `K/Y²` cusp heights in `[Y, 2Y]` (`0 < Y ≤ 1`).
* `lintegral_strip_window_le` (**unfolding bound**):
  `∫_{strip, Y ≤ v ≤ 2Y} |θ_s|² dμ ≤ (K/Y²) ∫_{D_Γ} |θ_s|² dμ`.
* `sourceCoefficient_sq_le`: with `Y = (1 + |ξ_h|)⁻¹` the Bessel factor of
  `b(v, h) = T_s(h) v K_{1/3}(4π|ξ_h| v)` is at least `c e^{−18π}` on `[Y, 2Y]`, and
  `∫_Y^{2Y} dv/v = log 2`; so `|P| c² e^{−36π} log 2 · |T_s(h)|² ≤ K (1 + |ξ_h|)² ‖θ_s‖₂²`.
-/

noncomputable section

open MeasureTheory Function
open scoped BigOperators Classical MatrixGroups ENNReal

namespace GaloisForLFunctions.SpectralTheoryOfTheCubicCover

open MetaplecticMobiusDescent MetaplecticMobiusDescent.Eisenstein MetaplecticMobiusDescent.CubicKubota
  MetaplecticMobiusDescent.CubicEisenstein

/-! ### One Fourier coefficient -/

/-- The area `|P| = 9√3/2` of the period parallelogram, as a real number. -/
abbrev periodAreaReal : ℝ := 9 * Real.sqrt 3 / 2

theorem periodAreaReal_pos : 0 < periodAreaReal := by positivity

theorem integrableOn_periodDomain_real (f : ℂ → ℝ) (hf : Continuous f) :
    IntegrableOn f periodDomain := by
  have hc := hf.continuousOn (s := Metric.closedBall (0 : ℂ) (∑ i : Fin 2, ‖periodBasis i‖))
  refine (hc.integrableOn_compact (isCompact_closedBall _ _)).mono_set fun z hz => ?_
  simpa only [Metric.mem_closedBall, dist_zero_right] using norm_mem_periodDomain z hz

/-- **One Fourier coefficient.** `|P| |a_k|² ≤ ∫_P |Σ_h a_h e(ξ_h z)|² dz`. -/
theorem periodArea_mul_norm_sq_le (a : O → ℂ) (ha : Summable (fun h => ‖a h‖)) (k : O) :
    periodAreaReal * ‖a k‖ ^ 2 ≤ ∫ z in periodDomain, ‖cuspCharacterSeries a z‖ ^ 2 := by
  have hS : Continuous (cuspCharacterSeries a) := cuspCharacterSeries_continuous a ha
  have hfin : volume periodDomain ≠ ⊤ := by
    rw [periodDomain_volume]
    exact ENNReal.ofReal_ne_top
  have hvol : volume.real periodDomain = periodAreaReal := by
    rw [Measure.real, periodDomain_volume, ENNReal.toReal_ofReal periodAreaReal_pos.le]
  have hI1 : IntegrableOn (fun z => ‖cuspCharacterSeries a z‖) periodDomain :=
    integrableOn_periodDomain_real _ (continuous_norm.comp hS)
  have hI2 : IntegrableOn (fun z => ‖cuspCharacterSeries a z‖ ^ 2) periodDomain :=
    integrableOn_periodDomain_real _ ((continuous_norm.comp hS).pow 2)
  -- `|P| |a_k| ≤ ∫_P |S|`: the coefficient is the integral of `S` against a unimodular character
  have h1 : periodAreaReal * ‖a k‖ ≤ ∫ z in periodDomain, ‖cuspCharacterSeries a z‖ := by
    have hk := cuspCharacterSeries_fourier a ha k
    calc periodAreaReal * ‖a k‖
        = ‖∫ z in periodDomain, cuspCharacterSeries a z * tracePhase (-cuspFrequency k * z)‖ := by
          rw [hk, norm_mul, Complex.norm_real, Real.norm_of_nonneg periodAreaReal_pos.le]
      _ ≤ ∫ z in periodDomain, ‖cuspCharacterSeries a z * tracePhase (-cuspFrequency k * z)‖ :=
          norm_integral_le_integral_norm _
      _ = _ := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
          simp only [norm_mul, tracePhase_norm, mul_one]
  -- `2 |a_k| ∫_P |S| ≤ ∫_P |S|² + |a_k|² |P|`
  have h2 : 2 * ‖a k‖ * ∫ z in periodDomain, ‖cuspCharacterSeries a z‖ ≤
      (∫ z in periodDomain, ‖cuspCharacterSeries a z‖ ^ 2) + ‖a k‖ ^ 2 * periodAreaReal := by
    have hc : ∫ _ in periodDomain, ‖a k‖ ^ 2 = ‖a k‖ ^ 2 * periodAreaReal := by
      rw [setIntegral_const, hvol, smul_eq_mul, mul_comm]
    have hcI : IntegrableOn (fun _ : ℂ => ‖a k‖ ^ 2) periodDomain := integrableOn_const hfin
    rw [← hc, ← integral_add hI2 hcI, ← integral_const_mul]
    refine setIntegral_mono_on (hI1.const_mul _) (hI2.add hcI) periodDomain_measurable fun z _ => ?_
    nlinarith [sq_nonneg (‖cuspCharacterSeries a z‖ - ‖a k‖)]
  nlinarith [mul_le_mul_of_nonneg_left h1 (norm_nonneg (a k))]

/-- `ENNReal` form of `periodArea_mul_norm_sq_le`. -/
theorem ofReal_periodArea_mul_norm_sq_le (a : O → ℂ) (ha : Summable (fun h => ‖a h‖)) (k : O) :
    ENNReal.ofReal (periodAreaReal * ‖a k‖ ^ 2) ≤
      ∫⁻ z in periodDomain, ‖cuspCharacterSeries a z‖ₑ ^ 2 := by
  have hS : Continuous (cuspCharacterSeries a) := cuspCharacterSeries_continuous a ha
  calc ENNReal.ofReal (periodAreaReal * ‖a k‖ ^ 2)
      ≤ ENNReal.ofReal (∫ z in periodDomain, ‖cuspCharacterSeries a z‖ ^ 2) :=
        ENNReal.ofReal_le_ofReal (periodArea_mul_norm_sq_le a ha k)
    _ = ∫⁻ z in periodDomain, ENNReal.ofReal (‖cuspCharacterSeries a z‖ ^ 2) :=
        ofReal_integral_eq_lintegral_ofReal
          (integrableOn_periodDomain_real _ ((continuous_norm.comp hS).pow 2))
          (Filter.Eventually.of_forall fun _ => sq_nonneg _)
    _ = _ := lintegral_congr fun z => by rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]

/-! ### The strip in coordinates, for nonnegative functions -/

/-- **The strip in coordinates.** `∫⁻_{strip} G dμ = ∫⁻_0^∞ ∫⁻_P G(z + jv) v^{−3} dz dv`. -/
theorem cuspStrip_lintegral (G : HyperbolicSpace → ℝ≥0∞) (hG : Measurable G) :
    ∫⁻ w in cuspStripSet, G w ∂hyperbolicVolume =
      ∫⁻ v in Set.Ioi (0 : ℝ), ∫⁻ z in periodDomain,
        G (cuspCoordinateLift (v, z)) * ENNReal.ofReal ((v ^ 3)⁻¹) := by
  have hm := euclideanToHyperbolic_measurePreserving_on stripEuclidean stripEuclidean_measurable
  rw [stripEuclidean_preimage] at hm
  have hE : hyperbolicEuclideanVolume.restrict stripEuclidean =
      (volume.restrict stripEuclidean).withDensity hyperbolicDensity := by
    rw [hyperbolicEuclideanVolume, restrict_withDensity stripEuclidean_measurable,
      Measure.restrict_restrict stripEuclidean_measurable,
      Set.inter_eq_left.mpr stripEuclidean_positive]
  have hlift : Measurable cuspCoordinateLift :=
    hm.measurable.comp spatialComplexSplit.symm.measurable
  have hHm : Measurable (fun q : ℝ × ℂ => G (cuspCoordinateLift q) * ENNReal.ofReal ((q.1 ^ 3)⁻¹)) :=
    (hG.comp hlift).mul (ENNReal.measurable_ofReal.comp ((measurable_fst.pow_const 3).inv))
  rw [← hm.lintegral_comp hG, hE, lintegral_withDensity_eq_lintegral_mul _ hyperbolicDensity_measurable
    (g := fun p => G (euclideanToHyperbolic p)) (hG.comp hm.measurable)]
  have hsplit := spatialComplexSplit_preserves_volume.setLIntegral_comp_preimage_emb
    spatialComplexSplit.measurableEmbedding
    (fun q : ℝ × ℂ => G (cuspCoordinateLift q) * ENNReal.ofReal ((q.1 ^ 3)⁻¹))
    (Set.Ioi (0 : ℝ) ×ˢ periodDomain)
  calc _ = ∫⁻ p in stripEuclidean, G (cuspCoordinateLift (spatialComplexSplit p)) *
        ENNReal.ofReal (((spatialComplexSplit p).1 ^ 3)⁻¹) := lintegral_congr fun p => by
          simp only [Pi.mul_apply, cuspCoordinateLift, MeasurableEquiv.symm_apply_apply,
            spatialComplexSplit_fst, hyperbolicDensity]
          rw [mul_comm]
    _ = ∫⁻ q in Set.Ioi (0 : ℝ) ×ˢ periodDomain,
        G (cuspCoordinateLift q) * ENNReal.ofReal ((q.1 ^ 3)⁻¹) := hsplit
    _ = _ := by
        change ∫⁻ q in _, _ ∂((volume : Measure ℝ).prod volume) = _
        rw [setLIntegral_prod _ hHm.aemeasurable]

/-! ### Square integrability of `θ_s` -/

/-- The fundamental set of `Γ` lies in the fundamental set of the kernel `Γ₁ ≤ Γ`. -/
theorem levelSet_subset_kernelSet : levelSet ⊆ hyperbolicFundamentalSet globalKubotaKernel :=
  fun _ hw M => hw ⟨M, globalKubotaKernel_le_levelThree M.2⟩

/-- `|θ_s|²` is integrable on the fundamental set of `Γ`. -/
theorem sourceTheta_integrableOn_sq :
    IntegrableOn (fun w => ‖sourceTheta w‖ ^ 2) levelSet hyperbolicVolume := by
  have hI : Integrable (fun q => ‖kernelRationalSourceProjection cubicEisensteinResidue q‖ ^ 2)
      (integralQuotientVolume globalKubotaKernel) :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable _)).mp (Lp.memLp _)
  have hI2 := ((quotient_projection_measurePreserving globalKubotaKernel).integrable_comp
    hI.aestronglyMeasurable).mpr hI
  have hI3 : IntegrableOn (fun w => ‖sourceTheta w‖ ^ 2)
      (hyperbolicFundamentalSet globalKubotaKernel) hyperbolicVolume := by
    refine hI2.congr ?_
    filter_upwards [ae_restrict_of_ae cubicSourceResidualFunction_represents_projection] with w hw
    simp only [Function.comp_apply] at hw ⊢
    rw [hw]
  exact hI3.mono_set levelSet_subset_kernelSet

/-- **`θ_s` is square integrable on the quotient.** -/
theorem sourceTheta_lintegral_sq_lt_top :
    ∫⁻ w in levelSet, ‖sourceTheta w‖ₑ ^ 2 ∂hyperbolicVolume < ⊤ := by
  refine lt_of_le_of_lt (le_of_eq (lintegral_congr fun w => ?_)) sourceTheta_integrableOn_sq.2
  rw [enorm_pow, enorm_norm]

/-! ### The unfolding bound -/

/-- The height window `1_{[Y, 2Y]}`. -/
def heightWindow (Y : ℝ) : ℝ → ℂ := Set.indicator (Set.Icc Y (2 * Y)) 1

theorem heightWindow_measurable (Y : ℝ) : Measurable (heightWindow Y) :=
  measurable_const.indicator measurableSet_Icc

/-- A point has at most `K/Y²` cusp heights in `[Y, 2Y]`. -/
theorem tsum_heightWindow_le (w : HyperbolicSpace) {Y : ℝ} (hY : 0 < Y) (hY1 : Y ≤ 1) :
    ∑' x : CuspCosets, ‖heightWindow Y (cosetHeight x w)‖ₑ ≤
      ENNReal.ofReal (heightCountConst / Y ^ 2) := by
  refine tsum_le_of_sum_le' zero_le fun s => ?_
  have hsum : ∑ x ∈ s, ‖heightWindow Y (cosetHeight x w)‖ₑ =
      ((s.filter fun x => cosetHeight x w ∈ Set.Icc Y (2 * Y)).card : ℝ≥0∞) := by
    rw [Finset.natCast_card_filter]
    refine Finset.sum_congr rfl fun x _ => ?_
    by_cases hx : cosetHeight x w ∈ Set.Icc Y (2 * Y) <;> simp [heightWindow, hx]
  rw [hsum, ← ENNReal.ofReal_natCast]
  exact ENNReal.ofReal_le_ofReal
    (card_cuspCosets_height_le w hY hY1 _ fun x hx => (Finset.mem_filter.mp hx).2.1)

/-- `θ_s²` has multiplier `κ⁻¹`. -/
theorem sourceThetaSq_automorphy (M : levelThree) (w : HyperbolicSpace) :
    sourceTheta (complexMatrix M • w) ^ 2 = (complexCharacter M)⁻¹ * sourceTheta w ^ 2 := by
  have h3 := complexCharacter_cube M
  have hne : complexCharacter M ≠ 0 := by
    intro h
    rw [h] at h3
    norm_num at h3
  rw [sourceTheta_automorphy, mul_pow]
  field_simp
  linear_combination sourceTheta w ^ 2 * h3

theorem unfolded_window_measurable (Y : ℝ) :
    Measurable (fun w => ‖unfolded (fun w => sourceTheta w ^ 2) (heightWindow Y) w‖ₑ) :=
  ((cubicSourceResidualFunction_continuous.pow 2).measurable.mul
    ((heightWindow_measurable Y).comp hyperbolicHeight_continuous.measurable)).enorm

/-- **The unfolding bound.** `∫_{strip} |θ_s|² 1_{[Y,2Y]}(v) dμ ≤ (K/Y²) ∫_{D_Γ} |θ_s|² dμ`. -/
theorem lintegral_strip_window_le {Y : ℝ} (hY : 0 < Y) (hY1 : Y ≤ 1) :
    ∫⁻ w in cuspStripSet, ‖unfolded (fun w => sourceTheta w ^ 2) (heightWindow Y) w‖ₑ
        ∂hyperbolicVolume ≤
      ENNReal.ofReal (heightCountConst / Y ^ 2) *
        ∫⁻ w in levelSet, ‖sourceTheta w‖ₑ ^ 2 ∂hyperbolicVolume := by
  change ∫⁻ w in CuspDomain.strip.carrier, _ ∂hyperbolicVolume ≤ _
  rw [← lintegral_norm_mul_incompleteEisenstein CuspDomain.strip _ sourceThetaSq_automorphy _
    (unfolded_window_measurable Y).aemeasurable, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono fun w => ?_
  dsimp only
  rw [ENNReal.tsum_mul_left, enorm_pow, mul_comm (ENNReal.ofReal _)]
  gcongr
  exact tsum_heightWindow_le w hY hY1

/-! ### The Hecke bound -/

/-- On `v |ξ_h| ≤ 2` the Bessel factor of `b(v, h)` is at least `c e^{−18π}`. -/
theorem norm_sourceAmplitude_ge (h : O) (hh : h ≠ 0) {c : ℝ} (hc : 0 < c)
    (hK : ∀ x : ℝ, 0 < x → c * Real.exp (-9 * x / 4) ≤ (schlafliBesselK (1 / 3) x).re)
    (v : ℝ) (hv : 0 < v) (hvξ : v * ‖cuspFrequency h‖ ≤ 2) :
    ‖rationalSourceResidualFourierCoefficient h‖ * v * (c * Real.exp (-18 * Real.pi)) ≤
      ‖rationalSourceModeAmplitude v h‖ := by
  have hξ : 0 < ‖cuspFrequency h‖ := norm_pos_iff.mpr (cuspFrequency_ne_zero h hh)
  have hx : 0 < 4 * Real.pi * ‖cuspFrequency h‖ * v := by positivity
  have hexp : Real.exp (-18 * Real.pi) ≤ Real.exp (-9 * (4 * Real.pi * ‖cuspFrequency h‖ * v) / 4) :=
    Real.exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_left hvξ Real.pi_pos.le])
  have hKx : c * Real.exp (-18 * Real.pi) ≤
      ‖schlafliBesselK (1 / 3) (4 * Real.pi * ‖cuspFrequency h‖ * v)‖ :=
    ((mul_le_mul_of_nonneg_left hexp hc.le).trans (hK _ hx)).trans (Complex.re_le_norm _)
  rw [rationalSourceModeAmplitude_bessel v hv h hh, norm_mul, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg hv.le]
  exact mul_le_mul_of_nonneg_left hKx (by positivity)

/-- `∫_Y^{2Y} A dv/v = A log 2`. -/
theorem lintegral_Icc_div (A : ℝ) (hA : 0 ≤ A) {Y : ℝ} (hY : 0 < Y) :
    ∫⁻ v in Set.Icc Y (2 * Y), ENNReal.ofReal (A / v) = ENNReal.ofReal (A * Real.log 2) := by
  have hcont : ContinuousOn (fun v : ℝ => A / v) (Set.Icc Y (2 * Y)) :=
    continuousOn_const.div continuousOn_id fun v hv => (hY.trans_le hv.1).ne'
  rw [← ofReal_integral_eq_lintegral_ofReal hcont.integrableOn_Icc
    (ae_restrict_of_forall_mem measurableSet_Icc fun v hv => div_nonneg hA (hY.trans_le hv.1).le)]
  congr 1
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith)]
  simp_rw [div_eq_mul_inv]
  rw [intervalIntegral.integral_const_mul, integral_inv_of_pos hY (by linarith),
    mul_div_cancel_right₀ _ hY.ne']

/-- **The squared Hecke bound.** There is `C` with `|T_s(h)|² ≤ C (1 + |ξ_h|)²` for every `h ≠ 0`. -/
theorem sourceCoefficient_sq_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ h : O, h ≠ 0 →
      ‖rationalSourceResidualFourierCoefficient h‖ ^ 2 ≤ C * (1 + ‖cuspFrequency h‖) ^ 2 := by
  obtain ⟨c, hc, hK⟩ := schlafliBesselK_one_third_exp_lower
  have hβ0 : 0 < c * Real.exp (-18 * Real.pi) := by positivity
  have hΛt : ∫⁻ w in levelSet, ‖sourceTheta w‖ₑ ^ 2 ∂hyperbolicVolume ≠ ⊤ :=
    sourceTheta_lintegral_sq_lt_top.ne
  have hlog : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hK0 : 0 ≤ heightCountConst := by
    have := latticeConst_nonneg
    positivity
  refine ⟨heightCountConst * (∫⁻ w in levelSet, ‖sourceTheta w‖ₑ ^ 2 ∂hyperbolicVolume).toReal /
    (periodAreaReal * (c * Real.exp (-18 * Real.pi)) ^ 2 * Real.log 2), by positivity, fun h hh => ?_⟩
  have hξ0 : 0 ≤ ‖cuspFrequency h‖ := norm_nonneg _
  have hY : 0 < (1 + ‖cuspFrequency h‖)⁻¹ := by positivity
  have hY1 : (1 + ‖cuspFrequency h‖)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
  have hYξ : (1 + ‖cuspFrequency h‖)⁻¹ * ‖cuspFrequency h‖ ≤ 1 := by
    rw [inv_mul_le_iff₀ (by positivity)]
    linarith
  set Y := (1 + ‖cuspFrequency h‖)⁻¹ with hYdef
  set A := periodAreaReal * (c * Real.exp (-18 * Real.pi)) ^ 2 *
    ‖rationalSourceResidualFourierCoefficient h‖ ^ 2 with hA
  have hA0 : 0 ≤ A := by positivity
  -- the window integral of `|θ_s|²` over the strip is at least `A log 2`
  have hlow : ENNReal.ofReal (A * Real.log 2) ≤
      ∫⁻ w in cuspStripSet, ‖unfolded (fun w => sourceTheta w ^ 2) (heightWindow Y) w‖ₑ
        ∂hyperbolicVolume := by
    rw [cuspStrip_lintegral _ (unfolded_window_measurable Y), ← lintegral_Icc_div A hA0 hY]
    refine le_trans ?_ (lintegral_mono_set fun v (hv : v ∈ Set.Icc Y (2 * Y)) => (hY.trans_le hv.1 : (0 : ℝ) < v))
    refine setLIntegral_mono' measurableSet_Icc fun v hv => ?_
    have hv0 : 0 < v := hY.trans_le hv.1
    have hlift : ∀ z, ‖unfolded (fun w => sourceTheta w ^ 2) (heightWindow Y)
        (cuspCoordinateLift (v, z))‖ₑ * ENNReal.ofReal ((v ^ 3)⁻¹) =
        ‖cuspCharacterSeries (rationalSourceModeAmplitude v) z‖ₑ ^ 2 * ENNReal.ofReal ((v ^ 3)⁻¹) := by
      intro z
      rw [cuspCoordinateLift_positive v z hv0]
      simp only [unfolded, hyperbolicHeight_upperPoint, heightWindow, Set.indicator_of_mem hv,
        Pi.one_apply, mul_one, enorm_pow, sourceTheta, cubicSourceResidualFunction_fourier_expansion]
    rw [lintegral_congr hlift, lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
    have hb := norm_sourceAmplitude_ge h hh hc hK v hv0
      (by nlinarith [mul_le_mul_of_nonneg_right hv.2 hξ0])
    calc ENNReal.ofReal (A / v)
        ≤ ENNReal.ofReal (periodAreaReal * ‖rationalSourceModeAmplitude v h‖ ^ 2) *
            ENNReal.ofReal ((v ^ 3)⁻¹) := by
          rw [← ENNReal.ofReal_mul (by positivity)]
          refine ENNReal.ofReal_le_ofReal ?_
          have hsq := pow_le_pow_left₀ (by positivity) hb 2
          calc A / v = periodAreaReal * (‖rationalSourceResidualFourierCoefficient h‖ * v *
                (c * Real.exp (-18 * Real.pi))) ^ 2 * (v ^ 3)⁻¹ := by
                rw [hA]
                field_simp
              _ ≤ _ := by gcongr
      _ ≤ _ := by
          gcongr
          exact ofReal_periodArea_mul_norm_sq_le _ (rationalSourceModeAmplitude_summable v hv0) h
  have hchain := hlow.trans (lintegral_strip_window_le hY hY1)
  rw [← ENNReal.ofReal_toReal hΛt, ← ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_le_ofReal_iff (by positivity)] at hchain
  have hY2 : heightCountConst / Y ^ 2 = heightCountConst * (1 + ‖cuspFrequency h‖) ^ 2 := by
    rw [hYdef, inv_pow, div_inv_eq_mul]
  rw [hY2] at hchain
  rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
  nlinarith [hchain]

/-- **The Hecke bound.** There is `C` with `|T_s(h)| ≤ C (1 + |ξ_h|)` for every `h ≠ 0`. -/
theorem sourceCoefficient_hecke_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ h : O, h ≠ 0 →
      ‖rationalSourceResidualFourierCoefficient h‖ ≤ C * (1 + ‖cuspFrequency h‖) := by
  obtain ⟨C, hC, hb⟩ := sourceCoefficient_sq_le
  refine ⟨Real.sqrt C, Real.sqrt_nonneg _, fun h hh => ?_⟩
  calc ‖rationalSourceResidualFourierCoefficient h‖
      = Real.sqrt (‖rationalSourceResidualFourierCoefficient h‖ ^ 2) :=
        (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt (C * (1 + ‖cuspFrequency h‖) ^ 2) := Real.sqrt_le_sqrt (hb h hh)
    _ = _ := by rw [Real.sqrt_mul hC, Real.sqrt_sq (by positivity)]

end GaloisForLFunctions.SpectralTheoryOfTheCubicCover
