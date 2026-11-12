import GaloisForLFunctions.SpectralTheoryOfTheCubicCover.TheRotatedThetaProductHasATwoCuspSubtraction
import GaloisForLFunctions.SpectralTheoryOfTheCubicCover.TheRotatedCorrelationsSeeOnlyTheThreeDivisibleLayer

/-!
# The rotated theta product reads the rotated correlation

`R = diag(ω, ω²)` acts by `z + jv ↦ ω²z + jv` (`rotation_smul_upperPoint`), so `θ_s(R·)` and `θ_s(R⁻¹·)`
have the Fourier coefficients `b(v, hω)` and `b(v, hω²)` (`rotatedTheta_fourier`). By Parseval on the
period parallelogram (`integral_cuspCharacterSeries_mul`) the constant term of
`F_R = θ_s(R·) θ_s(R⁻¹·)` is (`cuspConstantTerm_rotatedThetaProduct`)

`a₀(F_R)(v) = |P| (c² v^{4/3} + Σ_{h≠0} T(hω) T(hω²) v² K_{1/3}(4π|ξ_h| v)²)`,

and for any coefficient sequence `P` with `Σ_{h≠0} |P(h)| |ξ_h|^{−Re s} < ∞` the Mellin transform of
`Σ_{h≠0} P(h) v² K_{1/3}(4π|ξ_h|v)²` is `M(s) Σ_{h≠0} P(h)(4π|ξ_h|)^{−s}` (`integral_besselRemainder`).
For `P(h) = T(hω) T(hω²)` the Dirichlet series is the rotated correlation `C_ω(s) = Σ T(ωh) T(h) |…|^{−s}`
(`besselDirichlet_rotatedCoeff`), absolutely convergent for `Re s > 4`.
-/

noncomputable section

open MeasureTheory Filter Function
open scoped BigOperators Classical MatrixGroups ComplexConjugate

namespace GaloisForLFunctions.SpectralTheoryOfTheCubicCover

open MetaplecticMobiusDescent MetaplecticMobiusDescent.Eisenstein MetaplecticMobiusDescent.CubicKubota
  MetaplecticMobiusDescent.CubicEisenstein MetaplecticMobiusDescent.CubicEisenstein.RationalSource

/-! ### The rotation on the upper half-space -/

theorem ringComplex_omega_cube : ringComplex omega ^ 3 = 1 := by rw [← map_pow, omega_cube, map_one]

theorem norm_ringComplex_omega : ‖ringComplex omega‖ = 1 :=
  norm_ringComplex_unit (omega_primitive.isUnit (by decide))

theorem conj_ringComplex_omega : conj (ringComplex omega) = ringComplex omega ^ 2 := by
  rw [← Complex.inv_eq_conj norm_ringComplex_omega]
  exact inv_eq_of_mul_eq_one_right (by rw [← pow_succ']; exact ringComplex_omega_cube)

/-- `R(z + jv) = ω² z + jv`. -/
theorem rotation_smul_upperPoint (z : ℂ) (v : ℝ) (hv : 0 < v) :
    integralComplexMatrix rotation • upperPoint z v hv = upperPoint (ringComplex omega ^ 2 * z) v hv := by
  rw [mobius_upperPoint]
  have h00 : (integralComplexMatrix rotation) 0 0 = ringComplex omega := by simp [integralComplexMatrix]
  have h01 : (integralComplexMatrix rotation) 0 1 = 0 := by simp [integralComplexMatrix]
  have h10 : (integralComplexMatrix rotation) 1 0 = 0 := by simp [integralComplexMatrix]
  have h11 : (integralComplexMatrix rotation) 1 1 = ringComplex omega ^ 2 := by simp [integralComplexMatrix]
  have hn : ‖ringComplex omega ^ 2‖ = 1 := by rw [norm_pow, norm_ringComplex_omega, one_pow]
  simp only [h00, h01, h10, h11, zero_mul, zero_add, add_zero, norm_zero, star_zero, mul_zero, hn]
  congr 1
  · rw [Complex.star_def, map_pow, conj_ringComplex_omega]
    norm_num
    linear_combination (ringComplex omega ^ 2 * z) * ringComplex_omega_cube
  · norm_num

/-- `R⁻¹(z + jv) = ω z + jv`. -/
theorem rotation_inv_smul_upperPoint (z : ℂ) (v : ℝ) (hv : 0 < v) :
    integralComplexMatrix rotation⁻¹ • upperPoint z v hv = upperPoint (ringComplex omega * z) v hv := by
  have h := rotation_smul_upperPoint (ringComplex omega * z) v hv
  have he : ringComplex omega ^ 2 * (ringComplex omega * z) = z := by
    linear_combination z * ringComplex_omega_cube
  rw [he] at h
  rw [← h, map_inv, inv_smul_smul]

/-! ### Parseval for a product -/

/-- **Parseval on `P` for a product.** `∫_P (Σ a_h e(ξ_h z))(Σ b_h e(ξ_h z)) dz = |P| Σ_h a_h b_{−h}`. -/
theorem integral_cuspCharacterSeries_mul (a b : O → ℂ) (ha : Summable (fun h => ‖a h‖))
    (hb : Summable (fun h => ‖b h‖)) :
    ∫ z in periodDomain, cuspCharacterSeries a z * cuspCharacterSeries b z =
      periodArea * ∑' h : O, a h * b (-h) := by
  letI : Countable O := Coordinates.coordinateEquiv.injective.countable
  have hSb : Continuous (cuspCharacterSeries b) := cuspCharacterSeries_continuous b hb
  have hfin : volume periodDomain ≠ ⊤ := by
    rw [periodDomain_volume]
    exact ENNReal.ofReal_ne_top
  have hi : ∀ h : O, Integrable (fun z : ℂ => a h * (cuspCharacterSeries b z *
      tracePhase (cuspFrequency h * z))) (volume.restrict periodDomain) := fun h =>
    integrableOn_periodDomain_of_continuous _
      (continuous_const.mul (hSb.mul (tracePhase_continuous h)))
  have hpt : ∀ (h : O) (z : ℂ), ‖a h * (cuspCharacterSeries b z * tracePhase (cuspFrequency h * z))‖ ≤
      ‖a h‖ * ∑' k : O, ‖b k‖ := by
    intro h z
    rw [norm_mul, norm_mul, tracePhase_norm, mul_one]
    exact mul_le_mul_of_nonneg_left (norm_cuspCharacterSeries_le b hb z) (norm_nonneg _)
  have hint_le : ∀ h : O, ∫ z in periodDomain,
      ‖a h * (cuspCharacterSeries b z * tracePhase (cuspFrequency h * z))‖ ≤
        ‖a h‖ * (∑' k : O, ‖b k‖) * (volume periodDomain).toReal := by
    intro h
    have hc : IntegrableOn (fun _ : ℂ => ‖a h‖ * ∑' k : O, ‖b k‖) periodDomain :=
      integrableOn_const (μ := volume) hfin
    calc _ ≤ ∫ _ in periodDomain, ‖a h‖ * ∑' k : O, ‖b k‖ :=
          setIntegral_mono_on (hi h).norm hc periodDomain_measurable (fun z _ => hpt h z)
      _ = _ := by rw [setIntegral_const, smul_eq_mul, Measure.real, mul_comm]
  have hsum : Summable (fun h : O => ∫ z in periodDomain,
      ‖a h * (cuspCharacterSeries b z * tracePhase (cuspFrequency h * z))‖) :=
    Summable.of_nonneg_of_le (fun h => integral_nonneg fun z => norm_nonneg _) hint_le
      ((ha.mul_right _).mul_right _)
  have hprod : ∀ z : ℂ, cuspCharacterSeries a z * cuspCharacterSeries b z =
      ∑' h : O, a h * (cuspCharacterSeries b z * tracePhase (cuspFrequency h * z)) := by
    intro z
    calc cuspCharacterSeries a z * cuspCharacterSeries b z
        = ∑' h : O, cuspCharacterSeries b z * (a h * tracePhase (cuspFrequency h * z)) := by
          rw [cuspCharacterSeries, ← tsum_mul_right]
          exact tsum_congr fun h => by ring
      _ = _ := tsum_congr fun h => by ring
  simp_rw [hprod]
  rw [← integral_tsum_of_summable_integral_norm hi hsum]
  calc ∑' h : O, ∫ z in periodDomain, a h * (cuspCharacterSeries b z * tracePhase (cuspFrequency h * z))
      = ∑' h : O, periodArea * (a h * b (-h)) := tsum_congr fun h => by
        have hk := cuspCharacterSeries_fourier b hb (-h)
        simp only [cuspFrequency_neg, neg_neg] at hk
        rw [integral_const_mul, hk]
        ring
    _ = _ := tsum_mul_left

/-! ### The rotated Fourier series -/

/-- Rotating the argument rotates the frequencies: `S_a(u z) = S_{a(· w)}(z)` for `w u = 1`. -/
theorem cuspCharacterSeries_rotate (a : O → ℂ) (u w : Oˣ) (hwu : (w : O) * u = 1) (z : ℂ) :
    cuspCharacterSeries a (ringComplex (u : O) * z) = cuspCharacterSeries (fun k => a (k * w)) z := by
  unfold cuspCharacterSeries
  rw [← (Units.mulRight w).tsum_eq]
  refine tsum_congr fun k => ?_
  simp only [Units.mulRight_apply]
  rw [cuspFrequency_mul_right, mul_assoc, ← mul_assoc (ringComplex (w : O)), ← map_mul, hwu, map_one, one_mul]

theorem cuspOmegaUnit_sq_val : ((cuspOmegaUnit ^ 2 : Oˣ) : O) = omega ^ 2 := by
  rw [Units.val_pow_eq_pow_val, cuspOmegaUnit_val]

/-- `θ_s(R(z + jv)) = Σ_k b(v, kω) e(ξ_k z)`. -/
theorem rotatedTheta_fourier (z : ℂ) (v : ℝ) (hv : 0 < v) :
    sourceTheta (integralComplexMatrix rotation • upperPoint z v hv) =
      cuspCharacterSeries (fun k => rationalSourceModeAmplitude v (k * omega)) z := by
  rw [rotation_smul_upperPoint, show sourceTheta = cubicSourceResidualFunction from rfl,
    cubicSourceResidualFunction_fourier_expansion, ← map_pow, ← cuspOmegaUnit_sq_val,
    cuspCharacterSeries_rotate _ _ cuspOmegaUnit (by
      rw [cuspOmegaUnit_sq_val, cuspOmegaUnit_val]; linear_combination omega_cube)]
  simp only [cuspOmegaUnit_val]

/-- `θ_s(R⁻¹(z + jv)) = Σ_k b(v, kω²) e(ξ_k z)`. -/
theorem rotatedInvTheta_fourier (z : ℂ) (v : ℝ) (hv : 0 < v) :
    sourceTheta (integralComplexMatrix rotation⁻¹ • upperPoint z v hv) =
      cuspCharacterSeries (fun k => rationalSourceModeAmplitude v (k * omega ^ 2)) z := by
  rw [rotation_inv_smul_upperPoint, show sourceTheta = cubicSourceResidualFunction from rfl,
    cubicSourceResidualFunction_fourier_expansion, ← cuspOmegaUnit_val,
    cuspCharacterSeries_rotate _ _ (cuspOmegaUnit ^ 2) (by
      rw [cuspOmegaUnit_sq_val, cuspOmegaUnit_val]; linear_combination omega_cube)]
  simp only [Units.val_pow_eq_pow_val, cuspOmegaUnit_val]

theorem summable_amplitude_rotate (v : ℝ) (hv : 0 < v) (x : O) (hx : x ≠ 0) :
    Summable (fun k => ‖rationalSourceModeAmplitude v (k * x)‖) :=
  (rationalSourceModeAmplitude_summable v hv).comp_injective (mul_left_injective₀ hx)

theorem omega_ne_zero' : omega ≠ 0 := omega_primitive.ne_zero (by decide)

/-! ### The constant term -/

/-- The rotated coefficients `T(hω²) T(hω)`. -/
def rotatedCoeff (h : O) : ℂ :=
  rationalSourceResidualFourierCoefficient (h * omega ^ 2) * rationalSourceResidualFourierCoefficient (h * omega)

/-- `Σ_{h≠0} P(h) v² K_{1/3}(4π|ξ_h|v)²`. -/
def besselRemainder (P : O → ℂ) (v : ℝ) : ℂ :=
  ∑' h : O, if h = 0 then 0 else P h * ((v : ℂ) ^ 2 * besselSq (4 * Real.pi * ‖cuspFrequency h‖ * v))

/-- `Σ_{h≠0} P(h) (4π|ξ_h|)^{−s}`. -/
def besselDirichlet (P : O → ℂ) (s : ℂ) : ℂ :=
  ∑' h : O, if h = 0 then 0 else P h * ((4 * Real.pi * ‖cuspFrequency h‖ : ℝ) : ℂ) ^ (-s)

theorem norm_cuspFrequency_mul_omega_pow (h : O) (n : ℕ) :
    ‖cuspFrequency (h * omega ^ n)‖ = ‖cuspFrequency h‖ := by
  rw [cuspFrequency_mul_right, norm_mul, map_pow, norm_pow, norm_ringComplex_omega, one_pow, mul_one]

/-- `b(v, hω) b(v, −hω²) = T(hω²) T(hω) v² K_{1/3}(4π|ξ_h|v)²` for `h ≠ 0`. -/
theorem rotatedAmplitude_mul (v : ℝ) (hv : 0 < v) (h : O) (hh : h ≠ 0) :
    rationalSourceModeAmplitude v (h * omega) * rationalSourceModeAmplitude v (-h * omega ^ 2) =
      rotatedCoeff h * ((v : ℂ) ^ 2 * besselSq (4 * Real.pi * ‖cuspFrequency h‖ * v)) := by
  have h1 : h * omega ≠ 0 := mul_ne_zero hh omega_ne_zero'
  have h2 : -h * omega ^ 2 ≠ 0 := mul_ne_zero (neg_ne_zero.mpr hh) (pow_ne_zero 2 omega_ne_zero')
  rw [rationalSourceModeAmplitude_bessel v hv _ h1, rationalSourceModeAmplitude_bessel v hv _ h2, neg_mul,
    rationalSourceResidualFourierCoefficient_neg, cuspFrequency_neg, norm_neg, norm_cuspFrequency_mul_omega_pow,
    show h * omega = h * omega ^ 1 by rw [pow_one], norm_cuspFrequency_mul_omega_pow, rotatedCoeff, besselSq,
    pow_one]
  ring

/-- **The constant term of `F_R`.** `a₀(F_R)(v) = |P| (c² v^{4/3} + Σ_{h≠0} T(hω²)T(hω) v² K²)`. -/
theorem cuspConstantTerm_rotatedThetaProduct (v : ℝ) (hv : 0 < v) :
    cuspConstantTerm rotatedThetaProduct v =
      periodArea * (thetaCoeff ^ 2 * ((v ^ ((4 : ℝ) / 3) : ℝ) : ℂ) + besselRemainder rotatedCoeff v) := by
  have ha := summable_amplitude_rotate v hv _ omega_ne_zero'
  have hb := summable_amplitude_rotate v hv _ (pow_ne_zero 2 omega_ne_zero')
  have hθ : ∀ z, rotatedThetaProduct (cuspCoordinateLift (v, z)) =
      cuspCharacterSeries (fun k => rationalSourceModeAmplitude v (k * omega)) z *
        cuspCharacterSeries (fun k => rationalSourceModeAmplitude v (k * omega ^ 2)) z := fun z => by
    rw [cuspCoordinateLift_positive v z hv, rotatedThetaProduct, rotatedTheta_fourier, rotatedInvTheta_fourier]
  rw [cuspConstantTerm]
  simp_rw [hθ]
  rw [integral_cuspCharacterSeries_mul _ _ ha hb]
  congr 1
  have hsum : Summable (fun h : O => rationalSourceModeAmplitude v (h * omega) *
      rationalSourceModeAmplitude v (-h * omega ^ 2)) := by
    refine Summable.of_norm_bounded (ha.mul_right (∑' k : O, ‖rationalSourceModeAmplitude v (k * omega ^ 2)‖))
      fun h => ?_
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hb.le_tsum (-h) fun k _ => norm_nonneg _) (norm_nonneg _)
  rw [hsum.tsum_eq_add_tsum_ite 0, zero_mul, neg_zero, zero_mul, ← sq, rationalSourceModeAmplitude_zero,
    mul_pow, cpow_two_thirds_sq v hv, besselRemainder]
  congr 1
  refine tsum_congr fun h => ?_
  split_ifs with hh
  · rfl
  · exact rotatedAmplitude_mul v hv h hh

/-! ### The Mellin link -/

/-- **The Mellin link for a coefficient sequence.** If `Σ_{h≠0} |P(h)| |ξ_h|^{−Re s} < ∞` and
`Re s > 2/3`: `∫_0^∞ v^s (Σ_{h≠0} P(h) v² K²) v^{−3} dv = M(s) Σ_{h≠0} P(h)(4π|ξ_h|)^{−s}`. -/
theorem integral_besselRemainder (P : O → ℂ) (s : ℂ) (hs : 2 / 3 < s.re)
    (hP : Summable (fun h : O => if h = 0 then 0 else ‖P h‖ * ‖cuspFrequency h‖ ^ (-s.re))) :
    ∫ v in Set.Ioi (0 : ℝ), (v : ℂ) ^ s * besselRemainder P v / (v : ℂ) ^ 3 =
      besselSqMellin s * besselDirichlet P s := by
  letI : Countable O := Coordinates.coordinateEquiv.injective.countable
  set a : O → ℝ := fun h => 4 * Real.pi * ‖cuspFrequency h‖ with ha_def
  have ha : ∀ h : O, h ≠ 0 → 0 < a h := fun h hh =>
    by have := norm_pos_iff.mpr (cuspFrequency_ne_zero h hh); positivity
  set F : O → ℝ → ℂ := fun h v => if h = 0 then 0 else P h * ((v : ℂ) ^ (s - 1) • besselSq (a h * v)) with hF
  have hconv := besselSqMellin_convergent s hs
  have hpt : ∀ v ∈ Set.Ioi (0 : ℝ), (v : ℂ) ^ s * besselRemainder P v / (v : ℂ) ^ 3 = ∑' h, F h v := by
    intro v (hv : 0 < v)
    have hv0 : (v : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hv.ne'
    have hcp : (v : ℂ) ^ (s - 1) = (v : ℂ) ^ s / v := by
      rw [Complex.cpow_sub _ _ hv0, Complex.cpow_one]
    rw [besselRemainder, ← tsum_mul_left, ← tsum_div_const]
    refine tsum_congr fun h => ?_
    by_cases hh : h = 0
    · simp [hF, hh]
    · simp only [hF, hh, if_false, smul_eq_mul, hcp, ha_def, mul_comm (4 * Real.pi * ‖cuspFrequency h‖) v,
        ← mul_assoc]
      field_simp
  have hint : ∀ h, Integrable (F h) (volume.restrict (Set.Ioi 0)) := by
    intro h
    by_cases hh : h = 0
    · simp only [hF, hh, if_true]
      exact integrable_zero _ _ _
    · simp only [hF, hh, if_false]
      exact ((MellinConvergent.comp_mul_left (ha h hh)).mpr hconv).const_mul _
  have hval : ∀ h, ∫ v in Set.Ioi (0 : ℝ), F h v = besselSqMellin s *
      (if h = 0 then 0 else P h * ((a h : ℝ) : ℂ) ^ (-s)) := by
    intro h
    by_cases hh : h = 0
    · simp [hF, hh]
    · simp only [hF, hh, if_false]
      rw [integral_const_mul]
      have hm := mellin_comp_mul_left besselSq s (ha h hh)
      simp only [mellin] at hm
      rw [hm, besselSqMellin, mellin, smul_eq_mul]
      ring
  set N : ℝ := ∫ t in Set.Ioi (0 : ℝ), ‖(t : ℂ) ^ (s - 1) • besselSq t‖ with hN
  have hnorm : ∀ h, ∫ v in Set.Ioi (0 : ℝ), ‖F h v‖ = N * (4 * Real.pi) ^ (-s.re) *
      (if h = 0 then 0 else ‖P h‖ * ‖cuspFrequency h‖ ^ (-s.re)) := by
    intro h
    by_cases hh : h = 0
    · simp [hF, hh]
    simp only [hF, hh, if_false]
    have hah := ha h hh
    have hcpow : ∀ v : ℝ, 0 < v → ‖(v : ℂ) ^ (s - 1)‖ = a h ^ (1 - s.re) * ‖((a h * v : ℝ) : ℂ) ^ (s - 1)‖ := by
      intro v hv
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hv, Complex.norm_cpow_eq_rpow_re_of_pos (by positivity),
        Complex.sub_re, Complex.one_re, Real.mul_rpow hah.le hv.le, ← mul_assoc,
        ← Real.rpow_add hah]
      norm_num
    calc ∫ v in Set.Ioi (0 : ℝ), ‖P h * ((v : ℂ) ^ (s - 1) • besselSq (a h * v))‖
        = ∫ v in Set.Ioi (0 : ℝ), ‖P h‖ * a h ^ (1 - s.re) *
            ‖((a h * v : ℝ) : ℂ) ^ (s - 1) • besselSq (a h * v)‖ := by
          refine setIntegral_congr_fun measurableSet_Ioi fun v (hv : 0 < v) => ?_
          rw [norm_mul, norm_smul, norm_smul, hcpow v hv]
          ring
      _ = ‖P h‖ * a h ^ (1 - s.re) * ((a h)⁻¹ * N) := by
          rw [integral_const_mul]
          congr 1
          have hc := integral_comp_mul_left_Ioi
            (fun t : ℝ => ‖(t : ℂ) ^ (s - 1) • besselSq t‖) 0 hah
          rw [mul_zero] at hc
          rw [hc, smul_eq_mul]
      _ = _ := by
          have hsplit : a h ^ (1 - s.re) * (a h)⁻¹ = (4 * Real.pi) ^ (-s.re) * ‖cuspFrequency h‖ ^ (-s.re) := by
            rw [← Real.rpow_neg_one, ← Real.rpow_add hah, ha_def, Real.mul_rpow (by positivity)
              (norm_nonneg _)]
            ring_nf
          calc _ = N * ‖P h‖ * (a h ^ (1 - s.re) * (a h)⁻¹) := by ring
            _ = _ := by rw [hsplit]; ring
  have hsum : Summable (fun h => ∫ v in Set.Ioi (0 : ℝ), ‖F h v‖) := by
    simp_rw [hnorm]
    exact hP.mul_left _
  rw [setIntegral_congr_fun measurableSet_Ioi hpt, ← integral_tsum_of_summable_integral_norm hint hsum]
  simp_rw [hval]
  rw [tsum_mul_left, besselDirichlet]

/-- `Σ_{h≠0} |T(hω²)T(hω)| |ξ_h|^{−σ} < ∞` for `σ > 4` (`2|xy| ≤ |x|² + |y|²`). -/
theorem summable_rotatedCoeff {σ : ℝ} (hσ : 4 < σ) :
    Summable (fun h : O => if h = 0 then 0 else ‖rotatedCoeff h‖ * ‖cuspFrequency h‖ ^ (-σ)) := by
  set A : O → ℝ := fun h => if h = 0 then 0 else
    ‖rationalSourceResidualFourierCoefficient h‖ ^ 2 * ‖cuspFrequency h‖ ^ (-σ) with hA
  have hS : Summable A := summable_sourceCoefficient_sq_rpow hσ
  have h2 : Summable (fun h => A (h * omega ^ 2)) :=
    hS.comp_injective (mul_left_injective₀ (pow_ne_zero 2 omega_ne_zero'))
  have h1 : Summable (fun h => A (h * omega)) := hS.comp_injective (mul_left_injective₀ omega_ne_zero')
  refine Summable.of_nonneg_of_le (fun h => ?_) (fun h => ?_) ((h2.add h1).mul_left (1 / 2))
  · split_ifs
    · exact le_rfl
    · positivity
  · by_cases hh : h = 0
    · simp only [hh, if_true, zero_mul, hA]
      simp
    have hh2 : h * omega ^ 2 ≠ 0 := mul_ne_zero hh (pow_ne_zero 2 omega_ne_zero')
    have hh1 : h * omega ≠ 0 := mul_ne_zero hh omega_ne_zero'
    have hn1 : ‖cuspFrequency (h * omega)‖ = ‖cuspFrequency h‖ := by
      rw [show h * omega = h * omega ^ 1 by rw [pow_one], norm_cuspFrequency_mul_omega_pow]
    simp only [hA, hh, hh2, hh1, if_false, norm_cuspFrequency_mul_omega_pow, hn1, rotatedCoeff, norm_mul]
    have hq : 0 ≤ ‖cuspFrequency h‖ ^ (-σ) := by positivity
    nlinarith [mul_nonneg hq (sq_nonneg (‖rationalSourceResidualFourierCoefficient (h * omega ^ 2)‖ -
      ‖rationalSourceResidualFourierCoefficient (h * omega)‖))]

/-- `Σ_{h≠0} T(hω²)T(hω)(4π|ξ_h|)^{−s} = C_ω(s) = Σ_{h≠0} T(ωh)T(h)(4π|ξ_h|)^{−s}`. -/
theorem besselDirichlet_rotatedCoeff (s : ℂ) :
    besselDirichlet rotatedCoeff s = rotatedCorrelation cuspOmegaUnit s := by
  unfold besselDirichlet rotatedCorrelation
  rw [← (Units.mulRight (cuspOmegaUnit ^ 2)).tsum_eq]
  refine tsum_congr fun h => ?_
  simp only [Units.mulRight_apply, cuspOmegaUnit_sq_val, cuspOmegaUnit_val]
  by_cases hh : h = 0
  · simp [hh]
  · have hz : h * omega ^ 2 ≠ 0 := mul_ne_zero hh (pow_ne_zero 2 omega_ne_zero')
    rw [if_neg hz, if_neg hh, rotatedCoeff, norm_cuspFrequency_mul_omega_pow,
      show h * omega ^ 2 * omega ^ 2 = omega * h by linear_combination (omega * h) * omega_cube,
      show h * omega ^ 2 * omega = h by linear_combination h * omega_cube]

end GaloisForLFunctions.SpectralTheoryOfTheCubicCover
