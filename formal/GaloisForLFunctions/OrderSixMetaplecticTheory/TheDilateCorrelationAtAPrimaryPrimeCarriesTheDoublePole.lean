import GaloisForLFunctions.OrderSixMetaplecticTheory.TheHeckeTraceAtAPrimaryPrimeIsTwiceNormThetaSquaresUpToABoundedRemainder

/-!
# The dilate correlation at a primary prime carries the double pole

With `ρ = |p|`, `D(s) = Σ_{h≠0} T(h)²(4π|ξ_h|)^{−s}` the squared theta series, and

* `D_{p²}(s) = Σ_{h≠0} T(h)T(−p²h)(4π|ξ_h|)^{−s}` (`shiftSqCoeff`),
* `D_{dil}(s) = Σ_{p∤k} T(k)T(kp)(4π|ξ_k|)^{−s}` (`dilateCoeff`),

the bounded remainder `G'_p = Tr_pθ_s − 2N(p)θ_s²` has constant term
`N(p)|P|(2ρ^{−2}R_{p²}(ρv) + ρR_{dil}(v/ρ) − 2R(v))` (`cuspConstantTerm_remainder`), hence Mellin transform
`N(p)|P|M(s)(2ρ^{−s}D_{p²}(s) + ρ^{s−1}D_{dil}(s) − 2D(s))` (`integral_remainder_mul_eisenstein`). Since `G'_p` has at
most a simple pole at `4/3` (`RemainderData.pairing_near_four_thirds`), the combination
`M(s)(2ρ^{−s}D_{p²} + ρ^{s−1}D_{dil})` carries the double pole of `2M(s)D(s)` (`dilateCombination_double_pole`):
`(s − 4/3)² M(s)(2ρ^{−s}D_{p²}(s) + ρ^{s−1}D_{dil}(s)) → 216π³r³`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped BigOperators Classical MatrixGroups

namespace GaloisForLFunctions.OrderSixMetaplecticTheory

open MetaplecticMobiusDescent MetaplecticMobiusDescent.Eisenstein MetaplecticMobiusDescent.CubicJacobi
  MetaplecticMobiusDescent.CubicEisenstein MetaplecticMobiusDescent.CubicKubota SpectralTheoryOfTheCubicCover
  MetaplecticMobiusDescent.CubicEisenstein.RationalSource

namespace PrimaryPrime

variable (P : PrimaryPrime)

/-! ### Summability -/

theorem summable_shiftSqCoeff {σ : ℝ} (hσ : 4 < σ) :
    Summable (fun h : O => if h = 0 then 0 else ‖P.shiftSqCoeff h‖ * ‖cuspFrequency h‖ ^ (-σ)) := by
  have hn := P.norm_pos
  set ρ := ‖ringComplex P.p‖ with hρ
  set A : O → ℝ := fun h => if h = 0 then 0 else
    ‖rationalSourceResidualFourierCoefficient h‖ ^ 2 * ‖cuspFrequency h‖ ^ (-σ) with hAdef
  have hA : Summable A := summable_sourceCoefficient_sq_rpow hσ
  have hinj : Function.Injective (fun h : O => -(h * P.p) * P.p) := fun x y hxy => by
    have h1 := mul_right_cancel₀ P.ne_zero hxy
    exact mul_right_cancel₀ P.ne_zero (neg_injective h1)
  have hA4 : Summable (fun h => A (-(h * P.p) * P.p)) := hA.comp_injective hinj
  refine Summable.of_nonneg_of_le (fun h => ?_) (fun h => ?_)
    ((hA.add (hA4.mul_left ((ρ ^ 2) ^ σ))).mul_left (1 / 2))
  · split_ifs <;> positivity
  · split_ifs with hh
    · simp [hAdef, hh]
    · have h4 : -(h * P.p) * P.p ≠ 0 :=
        mul_ne_zero (neg_ne_zero.mpr (mul_ne_zero hh P.ne_zero)) P.ne_zero
      simp only [hAdef, hh, h4, if_false, shiftSqCoeff, norm_mul, P.norm_cuspFrequency_dilate]
      have hξ : 0 < ‖cuspFrequency h‖ := norm_pos_iff.mpr (cuspFrequency_ne_zero h hh)
      have hrp : (‖cuspFrequency h‖ * ρ ^ 2) ^ (-σ) = (ρ ^ 2) ^ (-σ) * ‖cuspFrequency h‖ ^ (-σ) := by
        rw [Real.mul_rpow hξ.le (by positivity), mul_comm]
      have h44 : (ρ ^ 2) ^ σ * (ρ ^ 2) ^ (-σ) = 1 := by
        rw [← Real.rpow_add (by positivity), add_neg_cancel, Real.rpow_zero]
      rw [hrp]
      set x := ‖rationalSourceResidualFourierCoefficient h‖
      set y := ‖rationalSourceResidualFourierCoefficient (-(h * P.p) * P.p)‖
      set w := ‖cuspFrequency h‖ ^ (-σ)
      have hw : 0 ≤ w := Real.rpow_nonneg hξ.le _
      have key : x * y * w ≤ 1 / 2 * (x ^ 2 * w + (ρ ^ 2) ^ σ * (y ^ 2 * ((ρ ^ 2) ^ (-σ) * w))) := by
        rw [show (ρ ^ 2) ^ σ * (y ^ 2 * ((ρ ^ 2) ^ (-σ) * w)) = y ^ 2 * w * ((ρ ^ 2) ^ σ * (ρ ^ 2) ^ (-σ)) by ring,
          h44]
        nlinarith [sq_nonneg (x - y), mul_nonneg (sq_nonneg (x - y)) hw]
      exact key

theorem summable_dilateCoeff {σ : ℝ} (hσ : 4 < σ) :
    Summable (fun h : O => if h = 0 then 0 else ‖P.dilateCoeff h‖ * ‖cuspFrequency h‖ ^ (-σ)) := by
  have hn := P.norm_pos
  set ρ := ‖ringComplex P.p‖ with hρ
  set A : O → ℝ := fun h => if h = 0 then 0 else
    ‖rationalSourceResidualFourierCoefficient h‖ ^ 2 * ‖cuspFrequency h‖ ^ (-σ) with hAdef
  have hA : Summable A := summable_sourceCoefficient_sq_rpow hσ
  have hinj : Function.Injective (fun h : O => h * P.p) := fun x y hxy => mul_right_cancel₀ P.ne_zero hxy
  have hAp : Summable (fun h => A (h * P.p)) := hA.comp_injective hinj
  refine Summable.of_nonneg_of_le (fun h => ?_) (fun h => ?_) ((hA.add (hAp.mul_left (ρ ^ σ))).mul_left (1 / 2))
  · split_ifs <;> positivity
  · split_ifs with hh
    · simp [hAdef, hh]
    · have hp0 : h * P.p ≠ 0 := mul_ne_zero hh P.ne_zero
      have hξ : 0 < ‖cuspFrequency h‖ := norm_pos_iff.mpr (cuspFrequency_ne_zero h hh)
      have hw : 0 ≤ ‖cuspFrequency h‖ ^ (-σ) := Real.rpow_nonneg hξ.le _
      by_cases hd : P.p ∣ h
      · simp only [dilateCoeff, if_pos hd, norm_zero, zero_mul, hAdef, hh, hp0, if_false]
        positivity
      · simp only [dilateCoeff, if_neg hd, hAdef, hh, hp0, if_false, norm_mul]
        have hnorm : ‖cuspFrequency (h * P.p)‖ = ‖cuspFrequency h‖ * ρ := by
          rw [cuspFrequency_mul_right, norm_mul]
        rw [hnorm, Real.mul_rpow hξ.le hn.le]
        have h44 : ρ ^ σ * ρ ^ (-σ) = 1 := by rw [← Real.rpow_add hn, add_neg_cancel, Real.rpow_zero]
        set x := ‖rationalSourceResidualFourierCoefficient h‖
        set y := ‖rationalSourceResidualFourierCoefficient (h * P.p)‖
        set w := ‖cuspFrequency h‖ ^ (-σ)
        rw [show ρ ^ σ * (y ^ 2 * (w * ρ ^ (-σ))) = y ^ 2 * w * (ρ ^ σ * ρ ^ (-σ)) by ring, h44]
        nlinarith [sq_nonneg (x - y), mul_nonneg (sq_nonneg (x - y)) hw]

/-! ### The constant term and the Mellin identity -/

theorem sourceHeckeTrace_continuous_z (v : ℝ) (hv : 0 < v) :
    Continuous (fun z : ℂ => P.sourceHeckeTrace (upperPoint z v hv)) := by
  have hb : Summable (fun h => ‖rationalSourceModeAmplitude (v / ‖ringComplex P.p‖) h‖) :=
    rationalSourceModeAmplitude_summable _ (div_pos hv P.norm_pos)
  have hinj : Function.Injective (fun m : O => m * P.p) := fun x y h => mul_right_cancel₀ P.ne_zero h
  rw [funext (P.sourceHeckeTrace_upperPoint v hv)]
  refine (continuous_const.mul (((cuspCharacterSeries_continuous _
    (rationalSourceModeAmplitude_summable _ (mul_pos P.norm_pos hv))).comp
      (continuous_const.mul continuous_id)).mul
        (continuous_const.mul (cuspCharacterSeries_continuous _ (hb.comp_injective hinj))))).add
    (continuous_finsetSum _ fun y _ => continuous_const.mul (continuous_const.mul
      (cuspCharacterSeries_continuous _
        ((summable_cuspConv (P.summable_shiftedLow v hv _) hb).comp_injective hinj))))

/-- **The constant term of `G'_p`.** -/
theorem cuspConstantTerm_remainder (v : ℝ) (hv : 0 < v) :
    cuspConstantTerm P.remainder v = (Fintype.card P.Res : ℂ) * periodArea *
      (2 * ((‖ringComplex P.p‖ : ℂ) ^ 2)⁻¹ * besselRemainder P.shiftSqCoeff (‖ringComplex P.p‖ * v) +
        (‖ringComplex P.p‖ : ℂ) * besselRemainder P.dilateCoeff (v / ‖ringComplex P.p‖) -
          2 * besselRemainder (fun h => rationalSourceResidualFourierCoefficient h ^ 2) v) := by
  have hlift : ∀ z, cuspCoordinateLift (v, z) = upperPoint z v hv := fun z => cuspCoordinateLift_positive v z hv
  have hc1 := P.sourceHeckeTrace_continuous_z v hv
  have hc2 : Continuous (fun z : ℂ => sourceTheta (upperPoint z v hv) ^ 2) := by
    have h := cuspCharacterSeries_continuous _ (rationalSourceModeAmplitude_summable v hv)
    simp_rw [sourceTheta, cubicSourceResidualFunction_fourier_expansion]
    exact h.pow 2
  rw [cuspConstantTerm]
  simp_rw [hlift, remainder]
  rw [integral_sub (integrableOn_periodDomain_of_continuous _ hc1)
    ((integrableOn_periodDomain_of_continuous _ hc2).const_mul _), integral_const_mul,
    P.integral_sourceHeckeTrace_bessel v hv, integral_sourceThetaSq_periodDomain v hv, thetaSqRemainder_eq v hv]
  ring

theorem real_cpow_identities (ρ : ℝ) (hρ : 0 < ρ) (s : ℂ) :
    ((ρ : ℂ) ^ 2)⁻¹ * (ρ : ℂ) ^ (2 - s) = (ρ : ℂ) ^ (-s) ∧
      (ρ : ℂ) * (((1 / ρ : ℝ) : ℂ)) ^ (2 - s) = (ρ : ℂ) ^ (s - 1) := by
  have hρ0 : (ρ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hρ.ne'
  have harg : (ρ : ℂ).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg hρ.le]
    exact Real.pi_ne_zero.symm
  have h2 : (ρ : ℂ) ^ (2 : ℂ) = (ρ : ℂ) ^ (2 : ℕ) := by exact_mod_cast Complex.cpow_natCast (ρ : ℂ) 2
  constructor
  · rw [Complex.cpow_sub _ _ hρ0, Complex.cpow_neg, h2]
    field_simp
  · rw [show (((1 / ρ : ℝ) : ℂ)) = (ρ : ℂ)⁻¹ by push_cast; ring, Complex.inv_cpow _ _ harg, ← Complex.cpow_neg,
      show (s - 1 : ℂ) = 1 + -(2 - s) by ring, Complex.cpow_add _ _ hρ0, Complex.cpow_one]

/-- **The Mellin identity at `p`.** For `4 < Re s < 13/3`:
`∫ G'_p E(s) = N(p)|P| M(s)(2ρ^{−s}D_{p²}(s) + ρ^{s−1}D_{dil}(s) − 2D(s))`. -/
theorem integral_remainder_mul_eisenstein (s : ℂ) (hs4 : 4 < s.re) (hs : s.re < 13 / 3) :
    ∫ w in levelSet, P.remainder w * hyperbolicEisenstein s w ∂hyperbolicVolume =
      (Fintype.card P.Res : ℂ) * periodArea * (besselSqMellin s *
        (2 * ((‖ringComplex P.p‖ : ℝ) : ℂ) ^ (-s) * besselDirichlet P.shiftSqCoeff s +
          ((‖ringComplex P.p‖ : ℝ) : ℂ) ^ (s - 1) * besselDirichlet P.dilateCoeff s - 2 * thetaSqDirichlet s)) := by
  have hG := P.remainder_remainderData
  have hn := P.norm_pos
  set ρ := ‖ringComplex P.p‖ with hρ
  have hs23 : 2 / 3 < s.re := by linarith
  rw [hG.integral_mul_eisenstein s (by linarith) hs]
  set RA := besselRemainder P.shiftSqCoeff
  set RD := besselRemainder P.dilateCoeff
  set R := besselRemainder (fun h => rationalSourceResidualFourierCoefficient h ^ 2)
  have hpt : ∀ v ∈ Set.Ioi (0 : ℝ),
      (v : ℂ) ^ s * (∫ z in periodDomain, P.remainder (cuspCoordinateLift (v, z))) / (v : ℂ) ^ 3 =
        (Fintype.card P.Res : ℂ) * periodArea * (2 * ((ρ : ℂ) ^ 2)⁻¹ * ((v : ℂ) ^ s * RA (ρ * v) / (v : ℂ) ^ 3) +
          (ρ : ℂ) * ((v : ℂ) ^ s * RD (1 / ρ * v) / (v : ℂ) ^ 3) - 2 * ((v : ℂ) ^ s * R v / (v : ℂ) ^ 3)) := by
    intro v (hv : 0 < v)
    have hc := P.cuspConstantTerm_remainder v hv
    rw [cuspConstantTerm] at hc
    rw [hc, show v / ρ = 1 / ρ * v by ring]
    ring
  have hIA := integrableOn_mellin_comp_mul RA s hn
    (integrableOn_besselRemainder P.shiftSqCoeff s hs23 (P.summable_shiftSqCoeff hs4))
  have hID := integrableOn_mellin_comp_mul RD s (one_div_pos.mpr hn)
    (integrableOn_besselRemainder P.dilateCoeff s hs23 (P.summable_dilateCoeff hs4))
  have hI := integrableOn_besselRemainder _ s hs23 (summable_sq_coeff hs4)
  have J1 : IntegrableOn (fun v : ℝ => 2 * ((ρ : ℂ) ^ 2)⁻¹ * ((v : ℂ) ^ s * RA (ρ * v) / (v : ℂ) ^ 3))
      (Set.Ioi 0) := hIA.const_mul _
  have J2 : IntegrableOn (fun v : ℝ => (ρ : ℂ) * ((v : ℂ) ^ s * RD (1 / ρ * v) / (v : ℂ) ^ 3)) (Set.Ioi 0) :=
    hID.const_mul _
  have J3 : IntegrableOn (fun v : ℝ => 2 * ((v : ℂ) ^ s * R v / (v : ℂ) ^ 3)) (Set.Ioi 0) := hI.const_mul _
  have J12 : IntegrableOn (fun v : ℝ => 2 * ((ρ : ℂ) ^ 2)⁻¹ * ((v : ℂ) ^ s * RA (ρ * v) / (v : ℂ) ^ 3) +
      (ρ : ℂ) * ((v : ℂ) ^ s * RD (1 / ρ * v) / (v : ℂ) ^ 3)) (Set.Ioi 0) := J1.add J2
  rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_const_mul, integral_sub J12 J3,
    integral_add J1 J2, integral_const_mul, integral_const_mul, integral_const_mul,
    integral_mellin_comp_mul RA s hn, integral_mellin_comp_mul RD s (one_div_pos.mpr hn),
    integral_besselRemainder P.shiftSqCoeff s hs23 (P.summable_shiftSqCoeff hs4),
    integral_besselRemainder P.dilateCoeff s hs23 (P.summable_dilateCoeff hs4),
    integral_besselRemainder _ s hs23 (summable_sq_coeff hs4)]
  obtain ⟨h1, h2⟩ := real_cpow_identities ρ hn s
  have hD : besselDirichlet (fun h => rationalSourceResidualFourierCoefficient h ^ 2) s = thetaSqDirichlet s := rfl
  rw [hD]
  linear_combination (Fintype.card P.Res : ℂ) * periodArea * besselSqMellin s *
    (2 * besselDirichlet P.shiftSqCoeff s * h1 + besselDirichlet P.dilateCoeff s * h2)

/-- **The dilate combination at `p` carries the double pole of `2M(s)D(s)`.** -/
theorem dilateCombination_double_pole :
    ∃ Λ : ℂ → ℂ,
      (∀ s : ℂ, 4 < s.re → s.re < 13 / 3 → 0 < s.im →
        Λ s = besselSqMellin s * (2 * ((‖ringComplex P.p‖ : ℝ) : ℂ) ^ (-s) * besselDirichlet P.shiftSqCoeff s +
          ((‖ringComplex P.p‖ : ℝ) : ℂ) ^ (s - 1) * besselDirichlet P.dilateCoeff s)) ∧
      (∀ s : ℂ, 1 < s.re → s.re < 13 / 3 → 0 < s.im → DifferentiableAt ℂ Λ s) ∧
      (∀ᶠ s in 𝓝[≠] (4 / 3 : ℂ), DifferentiableAt ℂ Λ s) ∧
      Tendsto (fun s => (s - 4 / 3) ^ 2 * Λ s) (𝓝[≠] (4 / 3 : ℂ))
        (𝓝 (2 * (108 * (Real.pi : ℂ) ^ 3 * constantArithmeticResidue ^ 3))) := by
  obtain ⟨Λ, hΛ, hΛd, hΛn, hΛl, -⟩ := thetaSqDirichlet_double_pole
  have hG := P.remainder_remainderData
  have hq : ((Fintype.card P.Res : ℂ) * periodArea : ℂ) ≠ 0 :=
    mul_ne_zero (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
      (Complex.ofReal_ne_zero.mpr periodAreaReal_pos.ne')
  refine ⟨fun s => 2 * Λ s + ((Fintype.card P.Res : ℂ) * periodArea)⁻¹ * hG.pairing s, fun s hs4 hs hi => ?_,
    fun s hs1 hs hi => ?_, ?_, ?_⟩
  · show 2 * Λ s + ((Fintype.card P.Res : ℂ) * periodArea)⁻¹ * hG.pairing s = _
    rw [hΛ s hs4 hs hi, ← hG.pairing_eq s hs4 hs hi, P.integral_remainder_mul_eisenstein s hs4 hs,
      inv_mul_cancel_left₀ hq]
    ring
  · exact ((hΛd s hs1 hs hi).const_mul _).add ((hG.pairing_differentiableAt s hs1 hs hi).const_mul _)
  · filter_upwards [hΛn, hG.pairing_near_four_thirds.1] with s h1 h2
    exact (h1.const_mul _).add (h2.const_mul _)
  · have h2 := hG.pairing_near_four_thirds.2
    have hsum := (hΛl.const_mul 2).add (h2.const_mul ((Fintype.card P.Res : ℂ) * periodArea)⁻¹)
    rw [mul_zero, add_zero] at hsum
    refine hsum.congr' (Eventually.of_forall fun s => ?_)
    ring

end PrimaryPrime

end GaloisForLFunctions.OrderSixMetaplecticTheory
