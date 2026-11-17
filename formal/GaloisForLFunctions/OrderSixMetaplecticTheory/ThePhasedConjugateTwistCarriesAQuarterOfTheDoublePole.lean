import GaloisForLFunctions.OrderSixMetaplecticTheory.TheShiftedFractionalTraceIsAJacobiMultipleOfTheTranslatedProduct
import GaloisForLFunctions.OrderSixMetaplecticTheory.TheConjugateCubicTwistAtEveryOddPrimaryPrimeHasADoublePole
import GaloisForLFunctions.SpectralTheoryOfTheCubicCover.TheTranslatedCorrelationHasADoublePole

/-!
# The phased conjugate twist carries a quarter of the double pole

Insert the shift phase `φ(k) = e(2ωξ_k)` (STCC's `translatedCoeff`) into the coefficients of the fractional-trace
argument. The bounded remainder `R^ω_q = Tr G^ω − (N² + N + (N − 1)J)F_ω` has constant term
`|P|(−NJ R^φ_{cop}(v) + N²χ(−4)χ(9)⁻¹R^φ_g(v/N))` (`cuspConstantTerm_shiftRemainder`), so the phased Gauss-weighted
conjugate twist `D^φ_g` and the phased `q`-coprime squares share their double pole (`phasedTwist_relation`). The phase
is invariant under multiplication by `q ≡ 1` mod `3` (`shiftPhase_mul_of_three_dvd`), so Patterson's relations at `q` give
the same Euler identity `(1 − ρ²t³)C_U = D^φ_{cop} + tD^φ_q` for the translated correlation `C_U`
(`translatedSq_euler`). With STCC's double pole `27π³r³` of `C_U` in place of `108π³r³`
(`phasedConjugateCubicTwist_double_pole`):

**the phased conjugate cubic twist `Σ_k φ(k)χ_q(k)⁻¹T(k)²(4π|ξ_k|)^{−s}` has the double pole of the conjugate twist
with a quarter of its leading coefficient.**
-/

noncomputable section

open MeasureTheory Filter Function Topology
open scoped BigOperators Classical MatrixGroups

namespace GaloisForLFunctions.OrderSixMetaplecticTheory

open MetaplecticMobiusDescent MetaplecticMobiusDescent.Eisenstein MetaplecticMobiusDescent.CubicJacobi
  MetaplecticMobiusDescent.CubicEisenstein MetaplecticMobiusDescent.CubicKubota SpectralTheoryOfTheCubicCover
  MetaplecticMobiusDescent.CubicEisenstein.RationalSource

theorem shiftPhase_zero (b : O) : shiftPhase b 0 = 1 := by
  simp [shiftPhase, cuspFrequency]

/-- The shift phase only sees the frequency modulo `3`. -/
theorem shiftPhase_mul_of_three_dvd (b h c : O) (hc : (3 : O) ∣ c - 1) : shiftPhase b (h * c) = shiftPhase b h := by
  have e1 : cuspFrequency (h * c) * (2 * ringComplex b) = cuspFrequency h * ringComplex (2 * b * c) := by
    rw [cuspFrequency_mul_right, map_mul, map_mul, map_ofNat]
    ring
  have e2 : cuspFrequency h * (2 * ringComplex b) = cuspFrequency h * ringComplex (2 * b) := by
    rw [map_mul, map_ofNat]
  rw [shiftPhase, shiftPhase, e1, e2]
  obtain ⟨m, hm⟩ := hc
  exact tracePhase_congr_three h _ _ ⟨2 * b * m, by linear_combination (2 * b) * hm⟩

/-- STCC's phased coefficient is the theta square times the shift phase. -/
theorem translatedCoeff_eq (h : O) :
    translatedCoeff h = shiftPhase omega h * rationalSourceResidualFourierCoefficient h ^ 2 := by
  rw [translatedCoeff, shiftPhase, mul_comm]
  congr 2
  ring

namespace PrimaryPrime

variable (P : PrimaryPrime)

theorem shiftPhase_mul_p (b h : O) : shiftPhase b (h * P.p) = shiftPhase b h :=
  shiftPhase_mul_of_three_dvd b h P.p P.three_dvd_sub_one

theorem shiftPhase_mul_p_cube (b h : O) : shiftPhase b (h * P.p ^ 3) = shiftPhase b h := by
  rw [pow_succ, pow_two, ← mul_assoc, ← mul_assoc, P.shiftPhase_mul_p, P.shiftPhase_mul_p, P.shiftPhase_mul_p]

/-- `φ(h)T(h)²` on `h` coprime to `q`. -/
def phCoprime (h : O) : ℂ := shiftPhase omega h * P.coprimeCoeff h

/-- `φ(h)g(h)T(h)²`. -/
def phGauss (h : O) : ℂ := shiftPhase omega h * P.gaussCoeff h

/-- `φ(h)T(hq)²` on `h` coprime to `q`. -/
def phP (h : O) : ℂ := shiftPhase omega h * P.pCoeff h

theorem summable_phCoprime {σ : ℝ} (hσ : 4 < σ) :
    Summable (fun h : O => if h = 0 then 0 else ‖P.phCoprime h‖ * ‖cuspFrequency h‖ ^ (-σ)) := by
  simpa only [phCoprime, norm_mul, norm_shiftPhase, one_mul] using P.summable_coprimeCoeff hσ

theorem summable_phGauss {σ : ℝ} (hσ : 4 < σ) :
    Summable (fun h : O => if h = 0 then 0 else ‖P.phGauss h‖ * ‖cuspFrequency h‖ ^ (-σ)) := by
  simpa only [phGauss, norm_mul, norm_shiftPhase, one_mul] using P.summable_gaussCoeff hσ

/-- The constant term of the translated product `F_ω`: `|P| Σ_k φ(k)b(v, k)b(v, −k)`. -/
theorem integral_translatedThetaProduct (v : ℝ) (hv : 0 < v) :
    ∫ z in periodDomain, translatedThetaProduct (upperPoint z v hv) =
      periodArea * ∑' k : O, rationalSourceModeAmplitude v k * rationalSourceModeAmplitude v (-k) *
        shiftPhase omega k := by
  have hb : Summable (fun h => ‖rationalSourceModeAmplitude v h‖) := rationalSourceModeAmplitude_summable v hv
  simp_rw [translatedThetaProduct, sourceTheta_shift]
  rw [integral_translate_mul _ _ hb hb]
  congr 1
  refine tsum_congr fun k => ?_
  rw [shiftPhase, map_neg, sub_neg_eq_add, two_mul]

/-- **The constant term of `R^ω_q`.** -/
theorem cuspConstantTerm_shiftRemainder (h2 : (2 : P.Res) ≠ 0) (v : ℝ) (hv : 0 < v) :
    cuspConstantTerm P.shiftRemainder v = periodArea *
      (-(P.normC * P.fracJacobi) * besselRemainder P.phCoprime v +
        P.normC ^ 2 * (P.chi (-4) * (P.chi 9)⁻¹) *
          besselRemainder P.phGauss (v / ‖ringComplex P.p‖ / ‖ringComplex P.p‖)) := by
  have hn := P.norm_pos
  set b := rationalSourceModeAmplitude v with hbdef
  have hb : Summable (fun h => ‖b h‖) := rationalSourceModeAmplitude_summable v hv
  have hlift : ∀ z, cuspCoordinateLift (v, z) = upperPoint z v hv := fun z => cuspCoordinateLift_positive v z hv
  have hc1 : Continuous (fun z : ℂ => P.sourceShiftTrace omega (upperPoint z v hv)) :=
    P.sourceShiftTrace_continuous.comp (continuous_upperPoint_z v hv)
  have hc2 : Continuous (fun z : ℂ => translatedThetaProduct (upperPoint z v hv)) :=
    translatedThetaProduct_continuous.comp (continuous_upperPoint_z v hv)
  rw [cuspConstantTerm]
  simp_rw [hlift, shiftRemainder]
  rw [integral_sub (integrableOn_periodDomain_of_continuous _ hc1)
    ((integrableOn_periodDomain_of_continuous _ hc2).const_mul _), integral_const_mul,
    P.integral_sourceShiftTrace h2 omega v hv, integral_translatedThetaProduct v hv]
  have hW : ∀ k : O, ‖shiftPhase omega k * P.fracWeight k‖ ≤
      ‖P.normC ^ 2 + P.normC - P.fracJacobi‖ + ‖P.normC * P.fracJacobi‖ := by
    intro k
    rw [norm_mul, norm_shiftPhase, one_mul]
    unfold fracWeight
    refine (norm_add_le _ _).trans (add_le_add le_rfl ?_)
    split_ifs <;> simp
    positivity
  have s1 := summable_mul_neg_bdd hb hb _ _ hW
  have s2 := summable_mul_neg_bdd hb hb (fun k => shiftPhase omega k) 1 (fun k => (norm_shiftPhase _ _).le)
  have hsplit : ∑' k : O, b k * b (-k) * (shiftPhase omega k * P.fracWeight k) -
      P.fracMain * ∑' k : O, b k * b (-k) * shiftPhase omega k =
      -(P.normC * P.fracJacobi) * besselRemainder P.phCoprime v := by
    have e : ∑' k : O, b k * b (-k) * (shiftPhase omega k * P.fracWeight k) -
        P.fracMain * ∑' k : O, b k * b (-k) * shiftPhase omega k =
        ∑' k : O, b k * b (-k) * (shiftPhase omega k * (P.fracWeight k - P.fracMain)) := by
      rw [← tsum_mul_left, ← s1.tsum_sub (s2.mul_left P.fracMain)]
      refine tsum_congr fun k => ?_
      ring
    rw [e]
    simp_rw [P.fracWeight_sub]
    rw [tsum_amplitude_phase _ (by simp) v hv, ← besselRemainder_const_mul]
    congr 1
    funext h
    unfold phCoprime coprimeCoeff
    split_ifs <;> ring
  have hgauss : ∑' k : O, rationalSourceModeAmplitude (v / ‖ringComplex P.p‖ / ‖ringComplex P.p‖) k *
      rationalSourceModeAmplitude (v / ‖ringComplex P.p‖ / ‖ringComplex P.p‖) (-k) *
        (shiftPhase omega k * ∑ u : P.Res, P.chi u * P.traceChar (u * P.res k)) =
      besselRemainder P.phGauss (v / ‖ringComplex P.p‖ / ‖ringComplex P.p‖) := by
    have hga : ∀ k : O, (∑ u : P.Res, P.chi u * P.traceChar (u * P.res k)) = P.gaussAt k := fun k => rfl
    simp_rw [hga]
    rw [tsum_amplitude_phase (fun k => shiftPhase omega k * P.gaussAt k) (by simp [P.gaussAt_zero]) _
      (div_pos (div_pos hv hn) hn)]
    congr 1
    funext h
    simp only [phGauss, gaussCoeff, gaussAt]
    ring
  rw [hgauss]
  linear_combination periodArea * hsplit

/-- **The Mellin identity of `R^ω_q`.** -/
theorem integral_shiftRemainder_mul_eisenstein (h2 : (2 : P.Res) ≠ 0) (s : ℂ) (hs4 : 4 < s.re) (hs : s.re < 13 / 3) :
    ∫ w in levelSet, P.shiftRemainder w * hyperbolicEisenstein s w ∂hyperbolicVolume =
      periodArea * (besselSqMellin s *
        (P.normC ^ 2 * (P.chi (-4) * (P.chi 9)⁻¹) * ((‖ringComplex P.p‖ * ‖ringComplex P.p‖ : ℝ) : ℂ) ^ (s - 2) *
            besselDirichlet P.phGauss s -
          P.normC * P.fracJacobi * besselDirichlet P.phCoprime s)) := by
  have hG := P.shiftRemainder_remainderData h2
  have hn := P.norm_pos
  set ρ := ‖ringComplex P.p‖ with hρ
  have hs23 : 2 / 3 < s.re := by linarith
  have hb : 0 < 1 / (ρ * ρ) := one_div_pos.mpr (mul_pos hn hn)
  rw [hG.integral_mul_eisenstein s (by linarith) hs]
  set RC := besselRemainder P.phCoprime
  set RG := besselRemainder P.phGauss
  set κ : ℂ := P.normC ^ 2 * (P.chi (-4) * (P.chi 9)⁻¹)
  have hpt : ∀ v ∈ Set.Ioi (0 : ℝ),
      (v : ℂ) ^ s * (∫ z in periodDomain, P.shiftRemainder (cuspCoordinateLift (v, z))) / (v : ℂ) ^ 3 =
        periodArea * (κ * ((v : ℂ) ^ s * RG (1 / (ρ * ρ) * v) / (v : ℂ) ^ 3) -
          P.normC * P.fracJacobi * ((v : ℂ) ^ s * RC v / (v : ℂ) ^ 3)) := by
    intro v (hv : 0 < v)
    have hc := P.cuspConstantTerm_shiftRemainder h2 v hv
    rw [cuspConstantTerm] at hc
    rw [hc, show v / ρ / ρ = 1 / (ρ * ρ) * v by field_simp]
    ring
  have hIG := integrableOn_mellin_comp_mul RG s hb
    (integrableOn_besselRemainder P.phGauss s hs23 (P.summable_phGauss hs4))
  have hIC := integrableOn_besselRemainder P.phCoprime s hs23 (P.summable_phCoprime hs4)
  have J1 : IntegrableOn (fun v : ℝ => κ * ((v : ℂ) ^ s * RG (1 / (ρ * ρ) * v) / (v : ℂ) ^ 3)) (Set.Ioi 0) :=
    hIG.const_mul _
  have J2 : IntegrableOn (fun v : ℝ => P.normC * P.fracJacobi * ((v : ℂ) ^ s * RC v / (v : ℂ) ^ 3)) (Set.Ioi 0) :=
    hIC.const_mul _
  rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_const_mul, integral_sub J1 J2, integral_const_mul,
    integral_const_mul, integral_mellin_comp_mul RG s hb,
    integral_besselRemainder P.phGauss s hs23 (P.summable_phGauss hs4),
    integral_besselRemainder P.phCoprime s hs23 (P.summable_phCoprime hs4), real_cpow_sq_inv ρ hn s]
  ring

/-- **The phased relation at `q`**: `(s − 4/3)²M(s)(N²χ(−4)χ(9)⁻¹N^{s−2}D^φ_g − NJ D^φ_{cop}) → 0`. -/
theorem phasedTwist_relation (h2 : (2 : P.Res) ≠ 0) :
    ∃ Λ : ℂ → ℂ,
      (∀ s : ℂ, 4 < s.re → s.re < 13 / 3 → 0 < s.im →
        Λ s = besselSqMellin s *
          (P.normC ^ 2 * (P.chi (-4) * (P.chi 9)⁻¹) * ((‖ringComplex P.p‖ * ‖ringComplex P.p‖ : ℝ) : ℂ) ^ (s - 2) *
              besselDirichlet P.phGauss s -
            P.normC * P.fracJacobi * besselDirichlet P.phCoprime s)) ∧
      (∀ s : ℂ, 1 < s.re → s.re < 13 / 3 → 0 < s.im → DifferentiableAt ℂ Λ s) ∧
      (∀ᶠ s in 𝓝[≠] (4 / 3 : ℂ), DifferentiableAt ℂ Λ s) ∧
      Tendsto (fun s => (s - 4 / 3) ^ 2 * Λ s) (𝓝[≠] (4 / 3 : ℂ)) (𝓝 0) := by
  have hG := P.shiftRemainder_remainderData h2
  have hq : (periodArea : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr periodAreaReal_pos.ne'
  refine ⟨fun s => periodArea⁻¹ * hG.pairing s, fun s hs4 hs hi => ?_, fun s hs1 hs hi => ?_, ?_, ?_⟩
  · show periodArea⁻¹ * hG.pairing s = _
    rw [← hG.pairing_eq s hs4 hs hi, P.integral_shiftRemainder_mul_eisenstein h2 s hs4 hs, inv_mul_cancel_left₀ hq]
  · exact (hG.pairing_differentiableAt s hs1 hs hi).const_mul _
  · filter_upwards [hG.pairing_near_four_thirds.1] with s h
    exact h.const_mul _
  · have h := hG.pairing_near_four_thirds.2.const_mul (periodArea⁻¹ : ℂ)
    rw [mul_zero] at h
    refine h.congr' (Eventually.of_forall fun s => ?_)
    ring


/-! ### The Euler identity for the translated correlation -/

theorem phP_gauss (h : O) : P.gaussAt 1 * P.phP h = P.eulerGauss * P.phGauss h := by
  have e := P.pCoeff_gauss h
  unfold phP phGauss eulerGauss
  linear_combination (shiftPhase omega h) * e

theorem gaussDirichlet_phP (s : ℂ) :
    P.gaussAt 1 * besselDirichlet P.phP s = P.eulerGauss * besselDirichlet P.phGauss s := by
  rw [besselDirichlet, besselDirichlet, ← tsum_mul_left, ← tsum_mul_left]
  refine tsum_congr fun h => ?_
  split_ifs
  · ring
  · rw [← mul_assoc, P.phP_gauss]
    ring

/-- **The Euler identity of the translated correlation at `q`**: `(1 − ρ²t³)C_U(s) = D^φ_{cop}(s) + tD^φ_q(s)`. -/
theorem translatedSq_euler (s : ℂ) (hs : 4 < s.re) :
    (1 - (‖ringComplex P.p‖ : ℂ) ^ 2 * (((‖ringComplex P.p‖ : ℝ) : ℂ) ^ (-s)) ^ 3) *
        besselDirichlet translatedCoeff s =
      besselDirichlet P.phCoprime s + ((‖ringComplex P.p‖ : ℝ) : ℂ) ^ (-s) * besselDirichlet P.phP s := by
  set ρ := ‖ringComplex P.p‖ with hρ
  set t : ℂ := ((ρ : ℝ) : ℂ) ^ (-s) with ht
  set w : O → ℂ := fun h => ((4 * Real.pi * ‖cuspFrequency h‖ : ℝ) : ℂ) ^ (-s) with hw
  set F : O → ℂ := fun h => if h = 0 then 0 else translatedCoeff h * w h with hF
  have hD : besselDirichlet translatedCoeff s = ∑' h, F h := rfl
  have hFs : Summable (fun h => ‖F h‖) := by
    refine ((summable_sq_coeff hs).mul_left ((4 * Real.pi) ^ (-s.re))).congr fun h => ?_
    by_cases h0 : h = 0
    · simp [hF, h0]
    · have hξ : 0 < ‖cuspFrequency h‖ := norm_pos_iff.mpr (cuspFrequency_ne_zero h h0)
      simp only [hF, if_neg h0, norm_mul, hw, translatedCoeff_eq, norm_shiftPhase, one_mul]
      rw [Complex.norm_cpow_eq_rpow_re_of_pos (by positivity), Complex.neg_re, Real.mul_rpow (by positivity) hξ.le]
      ring
  have hw_mul : ∀ h c : O, w (h * c) = w h * ((‖ringComplex c‖ : ℝ) : ℂ) ^ (-s) := by
    intro h c
    simp only [hw, cuspFrequency_mul_right, norm_mul]
    rw [show 4 * Real.pi * (‖cuspFrequency h‖ * ‖ringComplex c‖) =
        (4 * Real.pi * ‖cuspFrequency h‖) * ‖ringComplex c‖ by ring, Complex.ofReal_mul,
      Complex.mul_cpow_ofReal_nonneg (by positivity) (norm_nonneg _)]
  have hp3 : ((‖ringComplex (P.p ^ 3)‖ : ℝ) : ℂ) ^ (-s) = t ^ 3 := by
    rw [map_pow, norm_pow, ofReal_pow_cpow _ (norm_nonneg _)]
  set Fc : O → ℂ := fun h => if h = 0 then 0 else P.phCoprime h * w h with hFc
  set F1 : O → ℂ := fun h => if P.p ∣ h ∧ ¬ P.p ^ 2 ∣ h then F h else 0 with hF1
  set F3 : O → ℂ := fun h => if P.p ^ 3 ∣ h then F h else 0 with hF3
  have hsplit : ∀ h, F h = Fc h + F1 h + F3 h := by
    intro h
    by_cases h0 : h = 0
    · simp [hF, hFc, hF1, hF3, h0]
    · by_cases h1 : P.p ∣ h
      · have hc : Fc h = 0 := by simp [hFc, h0, phCoprime, coprimeCoeff, h1]
        by_cases h2 : P.p ^ 2 ∣ h
        · by_cases h3 : P.p ^ 3 ∣ h
          · simp [hF1, hF3, hc, h2, h3]
          · have hz : F h = 0 := by
              obtain ⟨m, rfl⟩ := h2
              have hm : ¬ P.p ∣ m := fun hm => h3 (by obtain ⟨k, rfl⟩ := hm; exact ⟨k, by ring⟩)
              simp only [hF, h0, if_false, translatedCoeff_eq]
              rw [show P.p ^ 2 * m = m * P.p ^ 2 by ring,
                rationalSourceResidualFourierCoefficient_prime_power_vanish P.p P.prime P.primary m hm 2 (by norm_num)]
              ring
            simp [hF1, hF3, hc, h2, h3, hz]
        · have h3 : ¬ P.p ^ 3 ∣ h := fun h3 => h2 ((pow_dvd_pow P.p (by norm_num : 2 ≤ 3)).trans h3)
          simp [hF1, hF3, hc, h1, h2, h3]
      · have h3 : ¬ P.p ^ 3 ∣ h := fun h3 => h1 ((dvd_pow_self P.p (by norm_num : 3 ≠ 0)).trans h3)
        simp [hF, hFc, hF1, hF3, h0, phCoprime, coprimeCoeff, h1, h3, translatedCoeff_eq]
  have hFc_le : ∀ h, ‖Fc h‖ ≤ ‖F h‖ := by
    intro h
    simp only [hFc, hF, phCoprime, coprimeCoeff, translatedCoeff_eq]
    split_ifs <;> simp
    all_goals positivity
  have hF1_le : ∀ h, ‖F1 h‖ ≤ ‖F h‖ := by
    intro h
    simp only [hF1]
    split_ifs <;> simp
  have hF3_le : ∀ h, ‖F3 h‖ ≤ ‖F h‖ := by
    intro h
    simp only [hF3]
    split_ifs <;> simp
  have sc := Summable.of_norm_bounded hFs hFc_le
  have s1 := Summable.of_norm_bounded hFs hF1_le
  have s3 := Summable.of_norm_bounded hFs hF3_le
  have hsum : ∑' h, F h = ∑' h, Fc h + ∑' h, F1 h + ∑' h, F3 h := by
    rw [← sc.tsum_add s1, ← (sc.add s1).tsum_add s3]
    exact tsum_congr hsplit
  have hinj3 : Injective (fun h : O => h * P.p ^ 3) := fun a b hab =>
    mul_right_cancel₀ (pow_ne_zero 3 P.ne_zero) hab
  have h3 : ∑' h, F3 h = (ρ : ℂ) ^ 2 * t ^ 3 * ∑' h, F h := by
    have hsupp : support F3 ⊆ Set.range (fun h : O => h * P.p ^ 3) := by
      intro h hh
      by_contra hn
      apply hh
      have : ¬ P.p ^ 3 ∣ h := fun ⟨c, hc⟩ => hn ⟨c, by rw [hc]; ring⟩
      simp [hF3, this]
    rw [← hinj3.tsum_eq hsupp, ← tsum_mul_left]
    refine tsum_congr fun h => ?_
    simp only [hF3, dvd_mul_left, if_true, hF]
    by_cases h0 : h = 0
    · simp [h0]
    · have hc3 : rationalSourceResidualFourierCoefficient (h * P.p ^ 3) =
          (ρ : ℂ) * rationalSourceResidualFourierCoefficient h := by
        simpa using P.coeff_mul_cube_pow h h0 1
      rw [if_neg (mul_ne_zero h0 (pow_ne_zero 3 P.ne_zero)), if_neg h0, translatedCoeff_eq, translatedCoeff_eq,
        P.shiftPhase_mul_p_cube, hc3, hw_mul, hp3]
      ring
  have hinj1 : Injective (fun h : O => h * P.p) := fun a b hab => mul_right_cancel₀ P.ne_zero hab
  have h1 : ∑' h, F1 h = t * besselDirichlet P.phP s := by
    have hsupp : support F1 ⊆ Set.range (fun h : O => h * P.p) := by
      intro h hh
      by_contra hn
      apply hh
      have : ¬ P.p ∣ h := fun ⟨c, hc⟩ => hn ⟨c, by rw [hc]; ring⟩
      simp [hF1, this]
    rw [← hinj1.tsum_eq hsupp, besselDirichlet, ← tsum_mul_left]
    refine tsum_congr fun x => ?_
    have hiff : (P.p ∣ x * P.p ∧ ¬ P.p ^ 2 ∣ x * P.p) ↔ ¬ P.p ∣ x := by
      constructor
      · rintro ⟨-, h2⟩ hx
        obtain ⟨c, rfl⟩ := hx
        exact h2 ⟨c, by ring⟩
      · intro hx
        refine ⟨dvd_mul_left _ _, fun h2 => hx ?_⟩
        rw [pow_two] at h2
        exact (mul_dvd_mul_iff_right P.ne_zero).mp h2
    simp only [hF1]
    rw [if_congr hiff rfl rfl]
    by_cases hx : P.p ∣ x
    · rw [if_neg (not_not.mpr hx)]
      simp [phP, pCoeff, hx]
    · have hx0 : x ≠ 0 := fun h0 => hx (by rw [h0]; exact dvd_zero _)
      rw [if_pos hx, if_neg hx0]
      simp only [hF, if_neg (mul_ne_zero hx0 P.ne_zero), phP, pCoeff, if_neg hx, hw_mul, translatedCoeff_eq,
        P.shiftPhase_mul_p]
      ring
  have hDc : besselDirichlet P.phCoprime s = ∑' h, Fc h := rfl
  rw [h3, h1] at hsum
  rw [hD, hDc]
  linear_combination hsum

/-! ### The double pole -/

/-- The leading coefficient `A(4/3)⁻¹NJ(1 − N(q)⁻¹)·27π³r³` of the phased Gauss-weighted conjugate twist. -/
def phConjLimit : ℂ :=
  (P.conjFactor (4 / 3))⁻¹ * (P.normC * P.fracJacobi *
    (1 - (‖ringComplex P.p‖ : ℂ) ^ 2 * (((‖ringComplex P.p‖ : ℝ) : ℂ) ^ (-(4 / 3 : ℂ))) ^ 3) *
      (27 * (Real.pi : ℂ) ^ 3 * constantArithmeticResidue ^ 3))

/-- The phase keeps a quarter of the leading coefficient. -/
theorem phConjLimit_eq : P.phConjLimit = P.conjLimit / 4 := by
  unfold phConjLimit conjLimit
  ring

theorem phConjLimit_ne_zero (h2 : (2 : P.Res) ≠ 0) : P.phConjLimit ≠ 0 := by
  rw [phConjLimit_eq]
  exact div_ne_zero (P.conjLimit_ne_zero h2) (by norm_num)

/-- **The phased Gauss-weighted conjugate twist has the double pole.** -/
theorem phasedTwist_double_pole (h2 : (2 : P.Res) ≠ 0) :
    ∃ Λ : ℂ → ℂ,
      (∀ s : ℂ, 4 < s.re → s.re < 13 / 3 → 0 < s.im → Λ s = besselSqMellin s * besselDirichlet P.phGauss s) ∧
      (∀ s : ℂ, 1 < s.re → s.re < 13 / 3 → 0 < s.im → DifferentiableAt ℂ Λ s) ∧
      (∀ᶠ s in 𝓝[≠] (4 / 3 : ℂ), DifferentiableAt ℂ Λ s) ∧
      Tendsto (fun s => (s - 4 / 3) ^ 2 * Λ s) (𝓝[≠] (4 / 3 : ℂ)) (𝓝 P.phConjLimit) ∧ P.phConjLimit ≠ 0 := by
  obtain ⟨Λr, hr_eq, hr_d, hr_n, hr_l⟩ := P.phasedTwist_relation h2
  obtain ⟨Λ₀, h0_eq, h0_d, h0_n, h0_l, -⟩ := translatedCorrelation_double_pole
  set E : ℂ → ℂ := fun s => 1 - (‖ringComplex P.p‖ : ℂ) ^ 2 * (((‖ringComplex P.p‖ : ℝ) : ℂ) ^ (-s)) ^ 3 with hE
  have hρ := P.rho_ne_zero
  have hEd : ∀ s, DifferentiableAt ℂ E s := fun s =>
    (differentiableAt_const _).sub ((differentiableAt_const _).mul
      ((DifferentiableAt.const_cpow (f := fun s : ℂ => -s) differentiableAt_id.neg (Or.inl hρ)).pow 3))
  have hAd := P.conjFactor_differentiableAt
  refine ⟨fun s => (P.conjFactor s)⁻¹ * (Λr s + P.normC * P.fracJacobi * E s * Λ₀ s), fun s hs4 hs hi => ?_,
    fun s hs1 hs hi => ?_, ?_, ?_, P.phConjLimit_ne_zero h2⟩
  · have hA := P.conjFactor_ne_zero h2 s (by linarith)
    have heuler := P.translatedSq_euler s hs4
    have hgp := P.gaussDirichlet_phP s
    have hg1 := P.gaussAt_one_ne_zero
    have hDp : besselDirichlet P.phP s = P.eulerGauss * (P.gaussAt 1)⁻¹ * besselDirichlet P.phGauss s := by
      rw [← inv_mul_cancel_left₀ hg1 (besselDirichlet P.phP s), hgp]
      ring
    show (P.conjFactor s)⁻¹ * (Λr s + P.normC * P.fracJacobi * E s * Λ₀ s) = _
    rw [hr_eq s hs4 hs hi, h0_eq s hs4 hs hi, inv_mul_eq_iff_eq_mul₀ hA, conjFactor]
    simp only [hE]
    linear_combination (besselSqMellin s * (P.normC * P.fracJacobi)) * heuler +
      (besselSqMellin s * (P.normC * P.fracJacobi) * ((‖ringComplex P.p‖ : ℝ) : ℂ) ^ (-s)) * hDp
  · exact ((hAd s).inv (P.conjFactor_ne_zero h2 s (by linarith))).mul
      ((hr_d s hs1 hs hi).add (((differentiableAt_const _).mul (hEd s)).mul (h0_d s hs1 hs hi)))
  · filter_upwards [hr_n, h0_n, eventually_re_gt] with s h1 h2' h3
    exact ((hAd s).inv (P.conjFactor_ne_zero h2 s h3)).mul (h1.add (((differentiableAt_const _).mul (hEd s)).mul h2'))
  · have hA0 := P.conjFactor_ne_zero h2 (4 / 3) (by norm_num)
    have hAt : Tendsto (fun s => (P.conjFactor s)⁻¹) (𝓝[≠] (4 / 3 : ℂ)) (𝓝 (P.conjFactor (4 / 3))⁻¹) :=
      ((hAd (4 / 3)).continuousAt.tendsto.inv₀ hA0).mono_left nhdsWithin_le_nhds
    have hEt : Tendsto E (𝓝[≠] (4 / 3 : ℂ)) (𝓝 (E (4 / 3))) :=
      (hEd (4 / 3)).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    have hsum := hr_l.add ((hEt.const_mul (P.normC * P.fracJacobi)).mul h0_l)
    have hlim := hAt.mul hsum
    rw [zero_add] at hlim
    have hval : P.phConjLimit = (P.conjFactor (4 / 3))⁻¹ * (P.normC * P.fracJacobi * E (4 / 3) *
        (27 * (Real.pi : ℂ) ^ 3 * constantArithmeticResidue ^ 3)) := rfl
    rw [hval]
    exact hlim.congr' (Eventually.of_forall fun s => by ring)

/-! ### The phased conjugate cubic twist -/

/-- `φ(k)χ_q(k)⁻¹T(k)²`. -/
def phConjTwistCoeff (h : O) : ℂ := shiftPhase omega h * P.conjTwistCoeff h

theorem gaussDirichlet_eq_phConjTwist (s : ℂ) :
    besselDirichlet P.phGauss s = P.gaussAt 1 * besselDirichlet P.phConjTwistCoeff s := by
  rw [besselDirichlet, besselDirichlet, ← tsum_mul_left]
  refine tsum_congr fun h => ?_
  split_ifs
  · ring
  · rw [phGauss, gaussCoeff, P.gaussAt_eq h, phConjTwistCoeff, conjTwistCoeff]
    ring

/-- **The phased conjugate cubic twist has a quarter of the double pole of the conjugate twist.**
`(s − 4/3)²M(s)Σ_k φ(k)χ_q(k)⁻¹T(k)²(4π|ξ_k|)^{−s} → g₁⁻¹A(4/3)⁻¹NJ(1 − N(q)⁻¹)·27π³r³ ≠ 0`. -/
theorem phasedConjugateCubicTwist_double_pole (h2 : (2 : P.Res) ≠ 0) :
    ∃ Λ : ℂ → ℂ,
      (∀ s : ℂ, 4 < s.re → s.re < 13 / 3 → 0 < s.im →
        Λ s = besselSqMellin s * besselDirichlet P.phConjTwistCoeff s) ∧
      (∀ s : ℂ, 1 < s.re → s.re < 13 / 3 → 0 < s.im → DifferentiableAt ℂ Λ s) ∧
      (∀ᶠ s in 𝓝[≠] (4 / 3 : ℂ), DifferentiableAt ℂ Λ s) ∧
      Tendsto (fun s => (s - 4 / 3) ^ 2 * Λ s) (𝓝[≠] (4 / 3 : ℂ)) (𝓝 ((P.gaussAt 1)⁻¹ * P.phConjLimit)) ∧
      (P.gaussAt 1)⁻¹ * P.phConjLimit ≠ 0 := by
  obtain ⟨Λ, hΛ, hΛd, hΛn, hΛl, hne⟩ := P.phasedTwist_double_pole h2
  have hg1 := P.gaussAt_one_ne_zero
  refine ⟨fun s => (P.gaussAt 1)⁻¹ * Λ s, fun s hs4 hs hi => ?_, fun s hs1 hs hi => (hΛd s hs1 hs hi).const_mul _,
    ?_, ?_, mul_ne_zero (inv_ne_zero hg1) hne⟩
  · show (P.gaussAt 1)⁻¹ * Λ s = _
    rw [hΛ s hs4 hs hi, P.gaussDirichlet_eq_phConjTwist]
    field_simp
  · filter_upwards [hΛn] with s h
    exact h.const_mul _
  · refine (hΛl.const_mul (P.gaussAt 1)⁻¹).congr' (Eventually.of_forall fun s => ?_)
    ring

end PrimaryPrime

end GaloisForLFunctions.OrderSixMetaplecticTheory
