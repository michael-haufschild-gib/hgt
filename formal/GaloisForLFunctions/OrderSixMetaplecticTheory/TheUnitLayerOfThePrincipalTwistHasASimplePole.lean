import GaloisForLFunctions.OrderSixMetaplecticTheory.TheTwistedUnitLayersAreGaussSumMultiplesOfTheUntwistedResidue

/-!
# The unit layer of the principal twist has a simple pole

Let `q` be an odd primary prime, `ρ = |q|`, `t(s) = ρ^{−s}`, `E(s) = 1 − ρ²t(s)³`. Patterson's relations at `q` split the
theta square and the translated correlation over the `q`-adic valuation (`thetaSq_euler`, `translatedSq_euler`), and
the `q`-divisible part is the (phased) conjugate cubic twist (`coprime_euler`, `phCoprime_euler`):

`D_{cop} = E·D − t c₂ L_{χ̄}`,   `D^φ_{cop} = E·C − t c₂ L^φ_{χ̄}`,

`D_{cop}(s) = Σ_{q∤k}T(k)²(4π|ξ_k|)^{−s}`, `c₂ = χ(9)⁻¹g₂²ρ⁻²`. STCC's selector (`coprime_sub_phased`) leaves the part prime to
`3`, the unramified principal twist modulo `q`, with the double pole (`unramCoprime_double_pole`)

`(s − 4/3)²M(s)D₀^{1_q}(s) → 54π³r³E(4/3) − ½t(4/3)c₂g(χ)⁻¹L = 54π³r³E(4/3)N²χ(−4)χ(9)⁻¹N^{−2/3}/A(4/3) ≠ 0`

(`principalLimit_eq`). As for the cubic twists, the principal character's cube factor is `Z₀` without its Euler factor at
`q`, so (`principalUnitLayer_simple_pole`) **the unit layer `S^{1_q}_1(w) = Σ_{q ∤ A}σ(A)N(A)^{−w}` has a simple pole at
`w = 2/3` with an explicit nonzero residue**.
-/

noncomputable section

open MeasureTheory Filter Function Topology
open scoped BigOperators Classical MatrixGroups

namespace GaloisForLFunctions.OrderSixMetaplecticTheory

open MetaplecticMobiusDescent MetaplecticMobiusDescent.Eisenstein MetaplecticMobiusDescent.CubicJacobi
  MetaplecticMobiusDescent.CubicEisenstein MetaplecticMobiusDescent.CubicKubota SpectralTheoryOfTheCubicCover
  MetaplecticMobiusDescent.CubicEisenstein.RationalSource

namespace PrimaryPrime

variable (P : PrimaryPrime)

/-! ### The coprime squares through the conjugate twist -/

/-- **`D_{cop} = E·D − t c₂ L_{χ̄}`.** -/
theorem coprime_euler (s : ℂ) (hs : 4 < s.re) :
    besselDirichlet P.coprimeCoeff s =
      (1 - (‖ringComplex P.p‖ : ℂ) ^ 2 * (((‖ringComplex P.p‖ : ℝ) : ℂ) ^ (-s)) ^ 3) * thetaSqDirichlet s -
        ((‖ringComplex P.p‖ : ℝ) : ℂ) ^ (-s) * P.eulerGauss * besselDirichlet P.conjTwistCoeff s := by
  have h1 := P.thetaSq_euler s hs
  have hg := P.gaussAt_one_ne_zero
  have hp : besselDirichlet P.pCoeff s = P.eulerGauss * besselDirichlet P.conjTwistCoeff s := by
    apply mul_left_cancel₀ hg
    rw [P.gaussDirichlet_pCoeff, P.gaussDirichlet_eq_conjTwist, eulerGauss]
    ring
  rw [hp] at h1
  linear_combination -h1

/-- **`D^φ_{cop} = E·C − t c₂ L^φ_{χ̄}`.** -/
theorem phCoprime_euler (s : ℂ) (hs : 4 < s.re) :
    besselDirichlet P.phCoprime s =
      (1 - (‖ringComplex P.p‖ : ℂ) ^ 2 * (((‖ringComplex P.p‖ : ℝ) : ℂ) ^ (-s)) ^ 3) * besselDirichlet translatedCoeff s -
        ((‖ringComplex P.p‖ : ℝ) : ℂ) ^ (-s) * P.eulerGauss * besselDirichlet P.phConjTwistCoeff s := by
  have h1 := P.translatedSq_euler s hs
  have hg := P.gaussAt_one_ne_zero
  have hp : besselDirichlet P.phP s = P.eulerGauss * besselDirichlet P.phConjTwistCoeff s := by
    apply mul_left_cancel₀ hg
    rw [P.gaussDirichlet_phP, P.gaussDirichlet_eq_phConjTwist]
    ring
  rw [hp] at h1
  linear_combination -h1

/-! ### The selector on the coprime squares -/

/-- `T(k)²` on `k` prime to `3q`. -/
def unramCoprimeCoeff (h : O) : ℂ := if (3 : O) ∣ h then 0 else P.coprimeCoeff h

theorem coprimeCoeff_neg (h : O) : P.coprimeCoeff (-h) = P.coprimeCoeff h := by
  simp only [coprimeCoeff, dvd_neg, rationalSourceResidualFourierCoefficient_neg]

theorem norm_coprimeCoeff_le (h : O) :
    ‖P.coprimeCoeff h‖ ≤ ‖rationalSourceResidualFourierCoefficient h ^ 2‖ := by
  unfold coprimeCoeff
  split_ifs
  · rw [norm_zero]
    exact norm_nonneg _
  · exact le_rfl

theorem coprime_selector (h : O) :
    P.coprimeCoeff h * (1 - (tracePhase (2 * (cuspFrequency h * ringComplex omega)) +
        tracePhase (-(2 * (cuspFrequency h * ringComplex omega)))) / 2) = (3 / 2 : ℂ) * P.unramCoprimeCoeff h := by
  have hs := thetaSquare_translation_selector h
  unfold unramCoprimeCoeff coprimeCoeff
  by_cases hq : P.p ∣ h
  · simp [hq]
  · simp only [hq, if_false]
    rw [hs]

/-- **The selector on the coprime squares.** `D_{cop} − D^φ_{cop} = (3/2)D₀^{1_q}`. -/
theorem coprime_sub_phased (s : ℂ) (hs : 4 < s.re) :
    besselDirichlet P.coprimeCoeff s - besselDirichlet P.phCoprime s =
      (3 / 2 : ℂ) * besselDirichlet P.unramCoprimeCoeff s := by
  let F : O → ℂ := fun h => if h = 0 then 0 else P.coprimeCoeff h *
    ((4 * Real.pi * ‖cuspFrequency h‖ : ℝ) : ℂ) ^ (-s)
  let C : O → ℂ := fun h => if h = 0 then 0 else P.phCoprime h *
    ((4 * Real.pi * ‖cuspFrequency h‖ : ℝ) : ℂ) ^ (-s)
  have hT := summable_thetaSqDirichlet_term s hs
  have hF : Summable F := by
    refine Summable.of_norm_bounded hT.norm fun h => ?_
    simp only [F]
    split_ifs with hh
    · simp
    · rw [norm_mul, norm_mul]
      exact mul_le_mul_of_nonneg_right (P.norm_coprimeCoeff_le h) (norm_nonneg _)
  have hC : Summable C := by
    refine Summable.of_norm_bounded hT.norm fun h => ?_
    simp only [C]
    split_ifs with hh
    · simp
    · rw [phCoprime, norm_mul, norm_mul, norm_mul, norm_shiftPhase, one_mul]
      exact mul_le_mul_of_nonneg_right (P.norm_coprimeCoeff_le h) (norm_nonneg _)
  have hneg : Summable (fun h => C (-h)) := hC.comp_injective neg_injective
  have he : (∑' h, C (-h)) = ∑' h, C h := (Equiv.neg O).tsum_eq C
  change (∑' h, F h) - (∑' h, C h) = _
  calc
    _ = (∑' h, F h) - ((∑' h, C h) + ∑' h, C (-h)) / 2 := by rw [he]; ring
    _ = ∑' h, (F h - (C h + C (-h)) / 2) := by
      rw [← hC.tsum_add hneg, ← tsum_div_const, hF.tsum_sub ((hC.add hneg).div_const 2)]
    _ = ∑' h : O, (3 / 2 : ℂ) * (if h = 0 then 0 else P.unramCoprimeCoeff h *
        ((4 * Real.pi * ‖cuspFrequency h‖ : ℝ) : ℂ) ^ (-s)) := by
      refine tsum_congr fun h => ?_
      by_cases hh : h = 0
      · simp [F, C, hh]
      · simp only [F, C, hh, neg_ne_zero.mpr hh, if_false, cuspFrequency_neg, norm_neg, phCoprime,
          P.coprimeCoeff_neg]
        rw [shiftPhase_omega_neg, shiftPhase_omega_eq]
        have hp := P.coprime_selector h
        linear_combination (((4 * Real.pi * ‖cuspFrequency h‖ : ℝ) : ℂ) ^ (-s)) * hp
    _ = _ := by rw [tsum_mul_left]; rfl

/-! ### The double pole of the unramified principal twist -/

/-- The leading coefficient `54π³r³E(4/3) − ½t(4/3)c₂g(χ)⁻¹L` of the unramified principal twist. -/
def principalLimit : ℂ :=
  (1 - (‖ringComplex P.p‖ : ℂ) ^ 2 * (((‖ringComplex P.p‖ : ℝ) : ℂ) ^ (-(4 / 3 : ℂ))) ^ 3) *
      (54 * (Real.pi : ℂ) ^ 3 * constantArithmeticResidue ^ 3) -
    1 / 2 * (((‖ringComplex P.p‖ : ℝ) : ℂ) ^ (-(4 / 3 : ℂ)) * P.eulerGauss * ((P.gaussAt 1)⁻¹ * P.conjLimit))

/-- **The unramified principal twist has a double pole.** For every odd primary prime `q`,
`(s − 4/3)²M(s)Σ_{3∤k, q∤k}T(k)²(4π|ξ_k|)^{−s} → principalLimit`. -/
theorem unramCoprime_double_pole (h2 : (2 : P.Res) ≠ 0) :
    ∃ Λ : ℂ → ℂ,
      (∀ s : ℂ, 4 < s.re → s.re < 13 / 3 → 0 < s.im →
        Λ s = besselSqMellin s * besselDirichlet P.unramCoprimeCoeff s) ∧
      (∀ s : ℂ, 1 < s.re → s.re < 13 / 3 → 0 < s.im → DifferentiableAt ℂ Λ s) ∧
      (∀ᶠ s in 𝓝[≠] (4 / 3 : ℂ), DifferentiableAt ℂ Λ s) ∧
      Tendsto (fun s => (s - 4 / 3) ^ 2 * Λ s) (𝓝[≠] (4 / 3 : ℂ)) (𝓝 P.principalLimit) := by
  obtain ⟨ΛD, hD_eq, hD_d, hD_n, hD_l, -⟩ := thetaSqDirichlet_double_pole
  obtain ⟨ΛC, hC_eq, hC_d, hC_n, hC_l, -⟩ := translatedCorrelation_double_pole
  obtain ⟨Λc, hc_eq, hc_d, hc_n, hc_l, -⟩ := P.conjugateCubicTwist_double_pole h2
  obtain ⟨Λφ, hφ_eq, hφ_d, hφ_n, hφ_l, -⟩ := P.phasedConjugateCubicTwist_double_pole h2
  have hρ := P.rho_ne_zero
  set t : ℂ → ℂ := fun s => ((‖ringComplex P.p‖ : ℝ) : ℂ) ^ (-s) with ht
  set E : ℂ → ℂ := fun s => 1 - (‖ringComplex P.p‖ : ℂ) ^ 2 * (t s) ^ 3 with hE
  have htd : ∀ s, DifferentiableAt ℂ t s := fun s =>
    DifferentiableAt.const_cpow (f := fun s : ℂ => -s) differentiableAt_id.neg (Or.inl hρ)
  have hEd : ∀ s, DifferentiableAt ℂ E s := fun s =>
    (differentiableAt_const _).sub ((differentiableAt_const _).mul ((htd s).pow 3))
  refine ⟨fun s => (2 / 3 : ℂ) * ((E s * ΛD s - t s * P.eulerGauss * Λc s) - (E s * ΛC s - t s * P.eulerGauss * Λφ s)),
    fun s hs4 hs hi => ?_, fun s hs1 hs hi => ?_, ?_, ?_⟩
  · have hsel := P.coprime_sub_phased s hs4
    have h1 := P.coprime_euler s hs4
    have h2' := P.phCoprime_euler s hs4
    show (2 / 3 : ℂ) * ((E s * ΛD s - t s * P.eulerGauss * Λc s) - (E s * ΛC s - t s * P.eulerGauss * Λφ s)) = _
    rw [hD_eq s hs4 hs hi, hC_eq s hs4 hs hi, hc_eq s hs4 hs hi, hφ_eq s hs4 hs hi]
    simp only [hE, ht]
    linear_combination (2 / 3 : ℂ) * besselSqMellin s * hsel - (2 / 3 : ℂ) * besselSqMellin s * (h1 - h2')
  · exact (((((hEd s).mul (hD_d s hs1 hs hi)).sub (((htd s).mul_const _).mul (hc_d s hs1 hs hi))).sub
      (((hEd s).mul (hC_d s hs1 hs hi)).sub (((htd s).mul_const _).mul (hφ_d s hs1 hs hi))))).const_mul _
  · filter_upwards [hD_n, hC_n, hc_n, hφ_n] with s h1 h2' h3 h4
    exact (((((hEd s).mul h1).sub (((htd s).mul_const _).mul h3)).sub
      (((hEd s).mul h2').sub (((htd s).mul_const _).mul h4)))).const_mul _
  · have hEt : Tendsto E (𝓝[≠] (4 / 3 : ℂ)) (𝓝 (E (4 / 3))) :=
      (hEd _).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    have htt : Tendsto (fun s => t s * P.eulerGauss) (𝓝[≠] (4 / 3 : ℂ)) (𝓝 (t (4 / 3) * P.eulerGauss)) :=
      ((htd _).continuousAt.tendsto.mono_left nhdsWithin_le_nhds).mul_const _
    have hlim := (((hEt.mul hD_l).sub (htt.mul hc_l)).sub ((hEt.mul hC_l).sub (htt.mul hφ_l))).const_mul (2 / 3 : ℂ)
    have hval : P.principalLimit = (2 / 3 : ℂ) * ((E (4 / 3) * (108 * (Real.pi : ℂ) ^ 3 * constantArithmeticResidue ^ 3) -
        t (4 / 3) * P.eulerGauss * ((P.gaussAt 1)⁻¹ * P.conjLimit)) -
        (E (4 / 3) * (27 * (Real.pi : ℂ) ^ 3 * constantArithmeticResidue ^ 3) -
          t (4 / 3) * P.eulerGauss * ((P.gaussAt 1)⁻¹ * P.phConjLimit))) := by
      rw [P.phConjLimit_eq]
      simp only [principalLimit, hE, ht]
      ring
    rw [hval]
    exact hlim.congr fun s => by ring

/-- **The leading coefficient is `54π³r³E(4/3)N²χ(−4)χ(9)⁻¹N^{−2/3}/A(4/3)`.** -/
theorem principalLimit_eq (h2 : (2 : P.Res) ≠ 0) :
    P.principalLimit = (1 - (‖ringComplex P.p‖ : ℂ) ^ 2 * (((‖ringComplex P.p‖ : ℝ) : ℂ) ^ (-(4 / 3 : ℂ))) ^ 3) *
      (54 * (Real.pi : ℂ) ^ 3 * constantArithmeticResidue ^ 3) *
        (P.normC ^ 2 * (P.chi (-4) * (P.chi 9)⁻¹) * ((‖ringComplex P.p‖ * ‖ringComplex P.p‖ : ℝ) : ℂ) ^ ((4 / 3 : ℂ) - 2)) /
          P.conjFactor (4 / 3) := by
  have hA := P.conjFactor_ne_zero h2 (4 / 3) (by norm_num)
  have hAd : P.conjFactor (4 / 3) =
      P.normC ^ 2 * (P.chi (-4) * (P.chi 9)⁻¹) * ((‖ringComplex P.p‖ * ‖ringComplex P.p‖ : ℝ) : ℂ) ^ ((4 / 3 : ℂ) - 2) +
        P.normC * P.fracJacobi * ((‖ringComplex P.p‖ : ℝ) : ℂ) ^ (-(4 / 3 : ℂ)) * P.eulerGauss * (P.gaussAt 1)⁻¹ := rfl
  rw [eq_div_iff hA, principalLimit, conjLimit]
  linear_combination ((1 - (‖ringComplex P.p‖ : ℂ) ^ 2 * (((‖ringComplex P.p‖ : ℝ) : ℂ) ^ (-(4 / 3 : ℂ))) ^ 3) *
      (54 * (Real.pi : ℂ) ^ 3 * constantArithmeticResidue ^ 3)) * hAd -
    (54 * (((‖ringComplex P.p‖ : ℝ) : ℂ) ^ (-(4 / 3 : ℂ)) * P.eulerGauss * (P.gaussAt 1)⁻¹ * P.normC * P.fracJacobi *
      (1 - (‖ringComplex P.p‖ : ℂ) ^ 2 * (((‖ringComplex P.p‖ : ℝ) : ℂ) ^ (-(4 / 3 : ℂ))) ^ 3) *
        ((Real.pi : ℂ) ^ 3 * constantArithmeticResidue ^ 3))) * inv_mul_cancel₀ hA

theorem principalLimit_ne_zero (h2 : (2 : P.Res) ≠ 0) : P.principalLimit ≠ 0 := by
  rw [P.principalLimit_eq h2]
  have hA := P.conjFactor_ne_zero h2 (4 / 3) (by norm_num)
  have hE := P.one_sub_ne_zero (4 / 3) (by norm_num)
  have hr : (54 * (Real.pi : ℂ) ^ 3 * constantArithmeticResidue ^ 3) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 3 (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)))
      (pow_ne_zero 3 constantArithmeticResidue_ne_zero)
  have hN : P.normC ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have h4 : (-4 : P.Res) ≠ 0 := neg_ne_zero.mpr (P.four_ne_zero' h2)
  have hc4 : P.chi (-4) ≠ 0 := by
    intro h0
    have := P.norm_chi_eq_one _ h4
    rw [h0, norm_zero] at this
    exact zero_ne_one this
  have hc9 : P.chi 9 ≠ 0 := by
    intro h0
    have := P.norm_chi_eq_one _ P.nine_ne_zero'
    rw [h0, norm_zero] at this
    exact zero_ne_one this
  have hρρ : ((‖ringComplex P.p‖ * ‖ringComplex P.p‖ : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (mul_pos P.norm_pos P.norm_pos).ne'
  have hcp : ((‖ringComplex P.p‖ * ‖ringComplex P.p‖ : ℝ) : ℂ) ^ ((4 / 3 : ℂ) - 2) ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl hρρ)
  exact div_ne_zero (mul_ne_zero (mul_ne_zero hE hr)
    (mul_ne_zero (mul_ne_zero (pow_ne_zero 2 hN) (mul_ne_zero hc4 (inv_ne_zero hc9))) hcp)) hA

/-! ### The unit layer -/

theorem resTwist_one_apply (h : O) :
    P.resTwist (1 : MulChar P.Res ℂ) h = if P.p ∣ h then 0 else 1 := by
  show (1 : MulChar P.Res ℂ) (P.res h) = _
  by_cases hd : P.p ∣ h
  · rw [if_pos hd, (P.res_eq_zero_iff h).mpr hd, MulChar.map_zero]
  · rw [if_neg hd]
    exact MulChar.one_apply (isUnit_iff_ne_zero.mpr fun h0 => hd ((P.res_eq_zero_iff h).mp h0))

theorem unramCoprimeCoeff_eq_twist (h : O) :
    P.unramCoprimeCoeff h =
      (P.resTwist (1 : MulChar P.Res ℂ) * unramifiedChar) h * rationalSourceResidualFourierCoefficient h ^ 2 := by
  have hu : unramifiedChar h = if lambda ∣ h then 0 else 1 := rfl
  rw [MonoidHom.mul_apply, hu, P.resTwist_one_apply]
  by_cases hT : rationalSourceResidualFourierCoefficient h = 0
  · simp [unramCoprimeCoeff, coprimeCoeff, hT]
  · have hiff := three_dvd_iff_lambda_dvd_of_coeff h hT
    unfold unramCoprimeCoeff coprimeCoeff
    by_cases h3 : (3 : O) ∣ h
    · rw [if_pos h3, if_pos (hiff.mp h3)]
      ring
    · rw [if_neg h3, if_neg (fun hl => h3 (hiff.mpr hl))]
      split_ifs <;> ring

theorem besselDirichlet_unramCoprime (s : ℂ) :
    besselDirichlet P.unramCoprimeCoeff s =
      twistDirichletG (P.resTwist (1 : MulChar P.Res ℂ) * unramifiedChar) s := by
  unfold twistDirichletG
  congr 1
  funext h
  exact P.unramCoprimeCoeff_eq_twist h

theorem resTwist_one_sign : P.resTwist (1 : MulChar P.Res ℂ) 1 + P.resTwist (1 : MulChar P.Res ℂ) (-1) = 2 := by
  rw [P.resTwist_one_apply, P.resTwist_one_apply, if_neg (fun hd => P.prime.not_unit (isUnit_of_dvd_one hd)),
    if_neg (fun hd => P.prime.not_unit (isUnit_of_dvd_one (dvd_neg.mp hd)))]
  norm_num

/-- **The unit layer of the principal twist.** `(s − 4/3)D₀^{1_q}(s) = C̄²(2/3)Z̃(s)E_q(s)·2(4π|ξ₁|)^{−s}S^{1_q}_1(s/2)`. -/
theorem sub_mul_unramCoprime (s : ℂ) (hs : 4 < s.re) :
    (s - 4 / 3) * besselDirichlet P.unramCoprimeCoeff s =
      P.combinationDenom s * (2 * unitFrequencyWeight s *
        P.twistedSquarefreeSeriesW (1 : MulChar P.Res ℂ) 1 (s / 2)) := by
  have hz : 1 < (3 * (s / 2) - 1).re := by rw [cubeZeta_re]; linarith
  have hZ := sub_mul_cubeZeta (s := s) (by linarith)
  have hU := unramifiedTwist_eq (P.resTwist (1 : MulChar P.Res ℂ)) (P.norm_resTwist_le _) s hs
  have hcz : cubeZetaG (P.resTwist (1 : MulChar P.Res ℂ)) (3 * (s / 2) - 1) =
      P.cubeZetaW (1 : MulChar P.Res ℂ) (3 * (s / 2) - 1) := rfl
  have hsq : twistedSquarefreeSeriesG (P.resTwist (1 : MulChar P.Res ℂ)) 1 (s / 2) =
      P.twistedSquarefreeSeriesW (1 : MulChar P.Res ℂ) 1 (s / 2) := rfl
  rw [P.besselDirichlet_unramCoprime, hU, hcz, hsq, P.resTwist_one_sign,
    P.cubeZetaW_cubic _ (one_pow 3) _ hz]
  unfold combinationDenom eulerFactorQ unitFrequencyWeight
  linear_combination (star rationalSourceThetaScalar ^ 2 *
    (1 - unramifiedNormWeight (3 * (s / 2) - 1) (Ideal.span {P.p})) *
      (2 * ((4 * Real.pi * ‖cuspFrequency 1‖ : ℝ) : ℂ) ^ (-s) *
        P.twistedSquarefreeSeriesW (1 : MulChar P.Res ℂ) 1 (s / 2))) * hZ

/-- The residue of `M(s)S^{1_q}_1(s/2)` at `4/3`. -/
def principalUnitResidue : ℂ :=
  P.principalLimit / (2 * unitFrequencyWeight (4 / 3) * P.combinationDenom (4 / 3))

theorem principalUnitResidue_ne_zero (h2 : (2 : P.Res) ≠ 0) : P.principalUnitResidue ≠ 0 :=
  div_ne_zero (P.principalLimit_ne_zero h2)
    (mul_ne_zero (mul_ne_zero (by norm_num) (unitFrequencyWeight_ne_zero _)) P.combinationDenom_four_thirds_ne_zero)

/-- **The unit layer of the principal twist has a simple pole.** For every odd primary prime `q`,
`M(s)S^{1_q}_1(s/2)`, `S^{1_q}_1(w) = Σ_{q ∤ gen A}σ(A)N(A)^{−w}`, continues to `{4/3 < Re s < 13/3, Im s > 0}` and to
a punctured neighbourhood of `4/3`, and `(s − 4/3)M(s)S^{1_q}_1(s/2) → principalUnitResidue ≠ 0`. -/
theorem principalUnitLayer_simple_pole (h2 : (2 : P.Res) ≠ 0) :
    ∃ Λ : ℂ → ℂ,
      (∀ s : ℂ, 4 < s.re → s.re < 13 / 3 → 0 < s.im →
        Λ s = besselSqMellin s * P.twistedSquarefreeSeriesW (1 : MulChar P.Res ℂ) 1 (s / 2)) ∧
      (∀ s : ℂ, 4 / 3 < s.re → s.re < 13 / 3 → 0 < s.im → DifferentiableAt ℂ Λ s) ∧
      (∀ᶠ s in 𝓝[≠] (4 / 3 : ℂ), DifferentiableAt ℂ Λ s) ∧
      Tendsto (fun s => (s - 4 / 3) * Λ s) (𝓝[≠] (4 / 3 : ℂ)) (𝓝 P.principalUnitResidue) ∧
      P.principalUnitResidue ≠ 0 := by
  obtain ⟨Λu, hu_eq, hu_d, hu_n, hu_l⟩ := P.unramCoprime_double_pole h2
  set D : ℂ → ℂ := fun s => 2 * unitFrequencyWeight s * P.combinationDenom s with hD
  have hDd : Differentiable ℂ D := fun s =>
    ((unitFrequencyWeight_differentiable s).const_mul 2).mul (P.combinationDenom_differentiable s)
  have hD0 : D (4 / 3) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) (unitFrequencyWeight_ne_zero _)) P.combinationDenom_four_thirds_ne_zero
  have hDne : ∀ s : ℂ, 4 / 3 < s.re → D s ≠ 0 := fun s hs =>
    mul_ne_zero (mul_ne_zero (by norm_num) (unitFrequencyWeight_ne_zero _)) (P.combinationDenom_ne_zero hs)
  have hD_ev : ∀ᶠ s in 𝓝 (4 / 3 : ℂ), D s ≠ 0 := (hDd _).continuousAt.eventually_ne hD0
  refine ⟨fun s => (s - 4 / 3) * Λu s / D s, fun s hs4 hs hi => ?_, fun s hs1 hs hi => ?_, ?_, ?_,
    P.principalUnitResidue_ne_zero h2⟩
  · have hd := hDne s (by linarith)
    have hL := P.sub_mul_unramCoprime s hs4
    show (s - 4 / 3) * Λu s / D s = _
    rw [hu_eq s hs4 hs hi, div_eq_iff hd]
    simp only [hD]
    linear_combination besselSqMellin s * hL
  · exact ((differentiableAt_id.sub_const _).mul (hu_d s (by linarith) hs hi)).div (hDd s) (hDne s hs1)
  · filter_upwards [hu_n, nhdsWithin_le_nhds hD_ev] with s h1 h2'
    exact ((differentiableAt_id.sub_const _).mul h1).div (hDd s) h2'
  · have hDt : Tendsto D (𝓝[≠] (4 / 3 : ℂ)) (𝓝 (D (4 / 3))) :=
      ((hDd _).continuousAt.tendsto).mono_left nhdsWithin_le_nhds
    have hval : P.principalUnitResidue = P.principalLimit / D (4 / 3) := by
      simp only [principalUnitResidue, hD]
    rw [hval]
    refine (hu_l.div hDt hD0).congr fun s => ?_
    simp only [Pi.div_apply]
    ring

end PrimaryPrime

end GaloisForLFunctions.OrderSixMetaplecticTheory
