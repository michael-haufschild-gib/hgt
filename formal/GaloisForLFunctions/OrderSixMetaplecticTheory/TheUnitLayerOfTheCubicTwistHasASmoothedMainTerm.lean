import GaloisForLFunctions.OrderSixMetaplecticTheory.TheTwistedUnitLayersAreGaussSumMultiplesOfTheUntwistedResidue
import GaloisForLFunctions.OrderSixMetaplecticTheory.GaussianSmoothedIdealSumsReadTheResidueOfTheirContinuation
import GaloisForLFunctions.OrderSixMetaplecticTheory.TheRegularizedRemainderPairingIsBoundedOnVerticalStrips
import GaloisForLFunctions.OrderSixMetaplecticTheory.TheLongColumnsAreLayersOfTwistedThetaSquares

/-!
# The unit layer of the cubic twist has a smoothed main term

For every primary prime `p` the unit layer `S^{χ_p}_1(w) = Σ_A χ_p(gen A)σ(A)N(A)^{−w}` is, on `1 < Re w < 13/6`,

`S^{χ_p}_1(w) = A_p(2w)S₁(w) + B_p(2w)(Λ̃_h − Λ̃_s)(2w)`   (`cubicUnitLayerCont_eq_series`),

`A_p(s) = 2/(c_p(s)κ_pE_p(s))`, `κ_p = (9/p)₃\overline{G̃(p)}`, `B_p(s)` the factor `s − 4/3` times an explicit
function holomorphic for `Re s > 5/4`, and `Λ̃_h`, `Λ̃_s` the regularized pairings of the Hecke and the shifted
Hecke remainders at `p`. The right side is holomorphic on `5/8 < Re w < 13/6` except a simple pole at `2/3` of
residue `A_p(4/3)Res S₁`: the remainder part is regular there, its pairings having at most simple poles
(`cubicUnitLayerCont_simple_pole`). Times `e^{w²}` it is `O((1 + Im² w)^{−1})` on closed strips
(`cubicUnitLayerCont_gaussian_bound`). Hence for every `5/8 < a < 2/3` (`cubicUnitLayer_smoothed_main_term`)

`Σ_A χ_p(gen A)σ(A)g(log(N(A)/X)) = e^{4/9}A_p(4/3)Res S₁·X^{2/3} + O_{p,a}(X^a)`,
`A_p(4/3) = 2N(p)^{5/6}/(N(p) + 1)·\overline{(9/p)₃}G̃(p)`   (`unitWeight_four_thirds`).

The exponent `5/8` is the zero-free half-plane `Re z > 7/8` of `ζ_K` read at `z = 3w − 1`, as for `S₁`.
-/

noncomputable section

open MeasureTheory Filter Function Topology Complex
open scoped BigOperators Classical

namespace GaloisForLFunctions.OrderSixMetaplecticTheory

open MetaplecticMobiusDescent MetaplecticMobiusDescent.Eisenstein MetaplecticMobiusDescent.CubicJacobi
  MetaplecticMobiusDescent.CubicEisenstein MetaplecticMobiusDescent.CubicKubota SpectralTheoryOfTheCubicCover
  MetaplecticMobiusDescent.CubicEisenstein.RationalSource

/-- `(4π|ξ₁|)^{s}` is bounded on `0 ≤ Re s ≤ B`. -/
theorem unitFrequencyWeight_inv_le (B : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, 0 ≤ s.re → s.re ≤ B → ‖(unitFrequencyWeight s)⁻¹‖ ≤ C := by
  let A : ℝ := 4 * Real.pi * ‖cuspFrequency 1‖
  have hA : 0 < A := by
    have hξ := norm_pos_iff.mpr (cuspFrequency_ne_zero 1 one_ne_zero)
    dsimp only [A]
    positivity
  refine ⟨Real.exp (|Real.log A| * B), (Real.exp_pos _).le, ?_⟩
  intro s hs hB
  change ‖(((A : ℂ) ^ (-s))⁻¹)‖ ≤ _
  rw [Complex.cpow_neg, inv_inv, Complex.norm_cpow_eq_rpow_re_of_pos hA, Real.rpow_def_of_pos hA]
  apply Real.exp_le_exp.mpr
  exact mul_le_mul (le_abs_self _) hB hs (abs_nonneg _)

theorem two_mul_tendsto_punctured :
    Tendsto (fun w : ℂ => 2 * w) (𝓝[≠] (2 / 3 : ℂ)) (𝓝[≠] (4 / 3 : ℂ)) := by
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
  · have ht : Tendsto (fun w : ℂ => 2 * w) (𝓝 (2 / 3 : ℂ)) (𝓝 (2 * (2 / 3 : ℂ))) :=
      (continuous_const.mul continuous_id).tendsto (2 / 3 : ℂ)
    rw [show (2 : ℂ) * (2 / 3) = 4 / 3 by norm_num] at ht
    exact ht.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with w hw he
    apply hw
    change w = 2 / 3
    change 2 * w = 4 / 3 at he
    linear_combination he / 2

namespace PrimaryPrime

variable (P : PrimaryPrime)

/-! ### The coefficient -/

/-- `χ_p(gen A)σ(A)` on the squarefree ideals with a primary generator. -/
def cubicUnitCoeff (A : Ideal O) : ℂ :=
  if Squarefree A ∧ primaryIdealGenerator A ≠ 0 then
    P.chi (P.res (primaryIdealGenerator A)) *
      (ringComplex (symbol 1 (primaryIdealGenerator A)) ^ 2 * thetaSquareWeight A) else 0

theorem cubicUnitCoeff_bounded : BoundedIdealCoefficient P.cubicUnitCoeff where
  norm_le A := by
    unfold cubicUnitCoeff
    split_ifs with h
    · have hp := (primaryIdealGenerator_spec A h.2).2
      rw [norm_mul, norm_mul, norm_pow, norm_thetaSquareWeight A h.2 h.1, mul_one]
      exact mul_le_one₀ (P.norm_mulChar_le _ _) (pow_nonneg (norm_nonneg _) _)
        (pow_le_one₀ (norm_nonneg _) (GaloisForLFunctions.OrderSixMetaplecticTheory.norm_symbol_le _ _ hp))
    · simp only [norm_zero, zero_le_one]
  of_bad A hA := by simp [cubicUnitCoeff, hA]

theorem idealSeries_cubicUnitCoeff (w : ℂ) :
    idealSeries P.cubicUnitCoeff w = P.twistedSquarefreeSeriesW P.chi 1 w := by
  unfold idealSeries twistedSquarefreeSeriesW cubicUnitCoeff
  refine tsum_congr fun A => ?_
  by_cases hA : primaryIdealGenerator A = 0
  · simp [unramifiedNormWeight_of_bad _ A hA]
  · by_cases hs : Squarefree A
    · simp [hs, hA]
    · simp [hs]

/-! ### The continuation -/

/-- `A_p(s) = 2/(c_p(s)κ_pE_p(s))`, the weight of the untwisted layer. -/
def unitWeight (s : ℂ) : ℂ :=
  2 / (P.dilateFactor s * (ringComplex (symbol 9 P.p) * star (normalizedCubicUnitGauss P.p)) *
    P.eulerFactorQ s)

/-- `B_p(s) = (s − 4/3)(2/3)(N vol)⁻¹/(c_p(s)κ_p·2W(s)Den_p(s)·M(s))`, the weight of the remainders. -/
def remainderWeight (s : ℂ) : ℂ :=
  (s - 4 / 3) * (2 / 3) * ((Fintype.card P.Res : ℂ) * periodArea)⁻¹ /
    (P.dilateFactor s * (ringComplex (symbol 9 P.p) * star (normalizedCubicUnitGauss P.p)) *
      (2 * unitFrequencyWeight s * P.combinationDenom s) * besselSqMellin s)

/-- `Λ̃_h(s) − Λ̃_s(s)`: the regularized pairings of the Hecke and the shifted Hecke remainders. -/
def remainderComb (s : ℂ) : ℂ :=
  P.remainder_remainderData.regPairing s - P.heckeShiftRemainder_remainderData.regPairing s

/-- The continuation `A_p(2w)S₁(w) + B_p(2w)(Λ̃_h − Λ̃_s)(2w)` of `S^{χ_p}_1(w)`. -/
def cubicUnitLayerCont (w : ℂ) : ℂ :=
  P.unitWeight (2 * w) * regularizedUntwistedTheta w + P.remainderWeight (2 * w) * P.remainderComb (2 * w)

theorem combinationDenom_ne_zero_of_five_fourths {s : ℂ} (hs : 5 / 4 < s.re) :
    P.combinationDenom s ≠ 0 :=
  mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero 2 scalar_star_ne_zero) (by norm_num))
    (clearedCubeZeta_ne_zero_right_of_five_fourths s hs)) (P.eulerFactorQ_ne_zero (by linarith))

/-- **The identity** on `4 < Re s < 13/3`, `Im s > 0`. -/
theorem cubicUnitLayerCont_eq_upper (s : ℂ) (hs4 : 4 < s.re) (hs : s.re < 13 / 3) (hi : 0 < s.im) :
    P.cubicUnitLayerCont (s / 2) = P.twistedSquarefreeSeriesW P.chi 1 (s / 2) := by
  have hs2 : 2 * (s / 2) = s := by ring
  have hre : 5 / 8 < (s / 2).re := by
    rw [show (s / 2).re = s.re / 2 by simp]
    linarith
  have him : (s / 2).im ≠ 0 := by
    rw [show (s / 2).im = s.im / 2 by simp]
    exact div_ne_zero hi.ne' two_ne_zero
  have hUT : regularizedUntwistedTheta (s / 2) =
      (s - 4 / 3) * ((2 / 3) * (completedThetaSq s - completedTranslated s)) /
        (2 * unitFrequencyWeight s * star rationalSourceThetaScalar ^ 2 * (2 / 3) * clearedCubeZeta s) /
          besselSqMellin s := by
    rw [regularizedUntwistedTheta_eq_nonreal _ hre him, continuedUntwistedTheta, hs2, completedUntwistedS,
      completedUnramified]
  have hPh := P.remainder_remainderData.regPairing_eq_of_im_ne s (by linarith) hi.ne'
  have hPs := P.heckeShiftRemainder_remainderData.regPairing_eq_of_im_ne s (by linarith) hi.ne'
  have e₃ : P.remainder_remainderData.pairing s = (Fintype.card P.Res : ℂ) * periodArea *
      (besselSqMellin s * (2 * ((‖ringComplex P.p‖ : ℝ) : ℂ) ^ (-s) * besselDirichlet P.shiftSqCoeff s +
        ((‖ringComplex P.p‖ : ℝ) : ℂ) ^ (s - 1) * besselDirichlet P.dilateCoeff s - 2 * thetaSqDirichlet s)) := by
    rw [← P.remainder_remainderData.pairing_eq s hs4 hs hi, P.integral_remainder_mul_eisenstein s hs4 hs]
  have e₄ : P.heckeShiftRemainder_remainderData.pairing s = (Fintype.card P.Res : ℂ) * periodArea *
      (besselSqMellin s * (2 * ((‖ringComplex P.p‖ : ℝ) : ℂ) ^ (-s) * besselDirichlet (P.phShiftSq omega) s +
        ((‖ringComplex P.p‖ : ℝ) : ℂ) ^ (s - 1) * besselDirichlet (P.phDilate omega) s -
          2 * besselDirichlet translatedCoeff s)) := by
    rw [← P.heckeShiftRemainder_remainderData.pairing_eq s hs4 hs hi,
      P.integral_heckeShiftRemainder_mul_eisenstein s hs4 hs]
  have e₁ := completedThetaSq_eq s hs4 hs hi
  have e₂ := completedTranslated_eq s hs4 hs hi
  have e₅ := P.combination_eq s hs4
  have e₆ := P.phasedCombination_eq s hs4
  set κ := ringComplex (symbol 9 P.p) * star (normalizedCubicUnitGauss P.p) with hκ
  have e₇ : besselDirichlet P.dilateCoeff s = κ * besselDirichlet P.twistCoeff s := by
    rw [besselDirichlet, besselDirichlet, ← tsum_mul_left]
    refine tsum_congr fun h => ?_
    split_ifs
    · ring
    · rw [P.dilateCoeff_eq_twist]
      ring
  have e₈ : besselDirichlet (P.phDilate omega) s = κ * besselDirichlet P.phTwistCoeff s := by
    rw [besselDirichlet, besselDirichlet, ← tsum_mul_left]
    refine tsum_congr fun h => ?_
    split_ifs
    · ring
    · rw [phDilate, phTwistCoeff, P.dilateCoeff_eq_twist]
      ring
  have e₉ := P.twist_sub_phased s hs4
  have hL := P.sub_mul_unramTwist s hs4
  set N : ℂ := (Fintype.card P.Res : ℂ) * periodArea with hN
  have hN0 : N ≠ 0 := mul_ne_zero (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
    (Complex.ofReal_ne_zero.mpr periodAreaReal_pos.ne')
  have e₀ : N⁻¹ * N = 1 := inv_mul_cancel₀ hN0
  set M := besselSqMellin s with hM
  set δ := P.dilateFactor s with hδ
  set W := unitFrequencyWeight s with hW
  set Z := clearedCubeZeta s with hZ
  set E := P.eulerFactorQ s with hE
  set C2 := star rationalSourceThetaScalar ^ 2 with hC2
  have hcd : P.combinationDenom s = C2 * (2 / 3) * Z * E := rfl
  set cd := P.combinationDenom s with hcddef
  have hM0 : M ≠ 0 := besselSqMellin_ne_zero s (by linarith)
  have hδ0 : δ ≠ 0 := P.dilateFactor_ne_zero s (by linarith)
  have hκ0 : κ ≠ 0 := P.twistFactor_ne_zero
  have hW0 : W ≠ 0 := unitFrequencyWeight_ne_zero s
  have hZ0 : Z ≠ 0 := clearedCubeZeta_ne_zero (by linarith)
  have hE0 : E ≠ 0 := P.eulerFactorQ_ne_zero (by linarith)
  have hC20 : C2 ≠ 0 := pow_ne_zero 2 scalar_star_ne_zero
  have hcd0 : cd ≠ 0 := by rw [hcd]; exact mul_ne_zero (mul_ne_zero (mul_ne_zero hC20 (by norm_num)) hZ0) hE0
  have hXe : P.remainderComb s =
      P.remainder_remainderData.pairing s - P.heckeShiftRemainder_remainderData.pairing s := by
    rw [remainderComb, hPh, hPs]
  have key : 2 * ((2 / 3) * (completedThetaSq s - completedTranslated s)) + (2 / 3) * N⁻¹ * P.remainderComb s =
      M * δ * κ * besselDirichlet P.unramTwistCoeff s := by
    rw [hXe]
    linear_combination (4 / 3 : ℂ) * e₁ - (4 / 3 : ℂ) * e₂ + (2 / 3) * N⁻¹ * e₃ - (2 / 3) * N⁻¹ * e₄ +
      (2 / 3) * M * ((2 * ((‖ringComplex P.p‖ : ℝ) : ℂ) ^ (-s) * besselDirichlet P.shiftSqCoeff s +
        ((‖ringComplex P.p‖ : ℝ) : ℂ) ^ (s - 1) * besselDirichlet P.dilateCoeff s - 2 * thetaSqDirichlet s) -
        (2 * ((‖ringComplex P.p‖ : ℝ) : ℂ) ^ (-s) * besselDirichlet (P.phShiftSq omega) s +
        ((‖ringComplex P.p‖ : ℝ) : ℂ) ^ (s - 1) * besselDirichlet (P.phDilate omega) s -
          2 * besselDirichlet translatedCoeff s)) * e₀ +
      (2 / 3) * M * e₅ - (2 / 3) * M * e₆ + (2 / 3) * M * δ * e₇ - (2 / 3) * M * δ * e₈ +
      (2 / 3) * M * δ * κ * e₉
  have hQ : δ * κ * (2 * W * cd) * M ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero hδ0 hκ0) (mul_ne_zero (mul_ne_zero two_ne_zero hW0) hcd0)) hM0
  have h1 : P.unitWeight s * ((s - 4 / 3) * ((2 / 3) * (completedThetaSq s - completedTranslated s)) /
      (2 * W * C2 * (2 / 3) * Z) / M) =
        (s - 4 / 3) * (2 * ((2 / 3) * (completedThetaSq s - completedTranslated s))) /
          (δ * κ * (2 * W * cd) * M) := by
    rw [unitWeight, ← hδ, ← hκ, ← hE, hcd]
    field_simp
  have h2 : P.remainderWeight s * P.remainderComb s =
      (s - 4 / 3) * ((2 / 3) * N⁻¹ * P.remainderComb s) / (δ * κ * (2 * W * cd) * M) := by
    rw [remainderWeight, ← hδ, ← hκ, ← hW, ← hcddef, ← hM, ← hN]
    ring
  rw [cubicUnitLayerCont, hs2, hUT, h1, h2, ← add_div, ← mul_add, key, div_eq_iff hQ]
  linear_combination (δ * κ * M) * hL

theorem cubicUnitLayerCont_differentiableAt (w : ℂ) (hw : 5 / 8 < w.re) (hB : w.re < 13 / 6)
    (hp : w ≠ 2 / 3) : DifferentiableAt ℂ P.cubicUnitLayerCont w := by
  have hlin : DifferentiableAt ℂ (fun w : ℂ => 2 * w) w := differentiableAt_id.const_mul 2
  have hr : (2 * w).re = 2 * w.re := by simp
  have hs1 : 5 / 4 < (2 * w).re := by rw [hr]; linarith
  have hs2 : (2 * w).re < 13 / 3 := by rw [hr]; linarith
  have hp' : 2 * w ≠ 4 / 3 := fun h => hp (by linear_combination h / 2)
  have hA : DifferentiableAt ℂ P.unitWeight (2 * w) := by
    unfold unitWeight
    exact (differentiableAt_const _).div
      (((P.dilateFactor_differentiableAt _ (by linarith)).mul_const _).mul (P.eulerFactorQ_differentiable _))
      (mul_ne_zero (mul_ne_zero (P.dilateFactor_ne_zero _ (by linarith)) P.twistFactor_ne_zero)
        (P.eulerFactorQ_ne_zero (by linarith)))
  have hBd : DifferentiableAt ℂ P.remainderWeight (2 * w) := by
    unfold remainderWeight
    exact (((differentiableAt_id.sub_const _).mul_const _).mul_const _).div
      ((((P.dilateFactor_differentiableAt _ (by linarith)).mul_const _).mul
        (((unitFrequencyWeight_differentiable _).const_mul 2).mul (P.combinationDenom_differentiable _))).mul
          (besselSqMellin_differentiableAt _ (by linarith)))
      (mul_ne_zero (mul_ne_zero (mul_ne_zero (P.dilateFactor_ne_zero _ (by linarith)) P.twistFactor_ne_zero)
        (mul_ne_zero (mul_ne_zero two_ne_zero (unitFrequencyWeight_ne_zero _))
          (P.combinationDenom_ne_zero_of_five_fourths hs1)))
        (besselSqMellin_ne_zero _ (by linarith)))
  have hC : DifferentiableAt ℂ P.remainderComb (2 * w) :=
    (P.remainder_remainderData.regPairing_differentiableAt _ (by linarith) hs2 hp').sub
      (P.heckeShiftRemainder_remainderData.regPairing_differentiableAt _ (by linarith) hs2 hp')
  exact ((hA.comp w hlin).mul (regularizedUntwistedTheta_differentiableAt w hw hB hp)).add
    ((hBd.comp w hlin).mul (hC.comp w hlin))

/-- **The continuation is the series** on `1 < Re w < 13/6`. -/
theorem cubicUnitLayerCont_eq_series (w : ℂ) (hw : 1 < w.re) (hB : w.re < 13 / 6) :
    P.cubicUnitLayerCont w = P.twistedSquarefreeSeriesW P.chi 1 w := by
  let U : Set ℂ := {z | 1 < z.re ∧ z.re < 13 / 6}
  have hU : IsOpen U := (isOpen_lt continuous_const Complex.continuous_re).inter
    (isOpen_lt Complex.continuous_re continuous_const)
  have hconv : Convex ℝ U :=
    (convex_halfSpace_gt ⟨fun _ _ => rfl, fun c z => by simp⟩ (1 : ℝ)).inter
      (convex_halfSpace_lt ⟨fun _ _ => rfl, fun c z => by simp⟩ (13 / 6 : ℝ))
  have hf : AnalyticOnNhd ℂ P.cubicUnitLayerCont U := by
    apply DifferentiableOn.analyticOnNhd _ hU
    intro z hz
    apply (P.cubicUnitLayerCont_differentiableAt z (by linarith only [hz.1]) hz.2 ?_).differentiableWithinAt
    intro he
    have hre := hz.1
    rw [he] at hre
    norm_num at hre
  have hser : idealSeries P.cubicUnitCoeff = P.twistedSquarefreeSeriesW P.chi 1 :=
    funext P.idealSeries_cubicUnitCoeff
  have hg : AnalyticOnNhd ℂ (P.twistedSquarefreeSeriesW P.chi 1) U := by
    apply DifferentiableOn.analyticOnNhd _ hU
    intro z hz
    rw [← hser]
    exact (P.cubicUnitCoeff_bounded.idealSeries_differentiableAt z hz.1).differentiableWithinAt
  have hc : (25 / 12 + Complex.I : ℂ) ∈ U := by norm_num [U]
  apply hf.eqOn_of_preconnected_of_eventuallyEq hg hconv.isPreconnected hc _ ⟨hw, hB⟩
  have hopen : IsOpen {z : ℂ | 2 < z.re ∧ z.re < 13 / 6 ∧ 0 < z.im} :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      ((isOpen_lt Complex.continuous_re continuous_const).inter
        (isOpen_lt continuous_const Complex.continuous_im))
  filter_upwards [hopen.mem_nhds (by norm_num)] with z hz
  have h := P.cubicUnitLayerCont_eq_upper (2 * z) (by simp; linarith only [hz.1])
    (by simp; linarith only [hz.2.1]) (by simp; linarith only [hz.2.2])
  rwa [show 2 * z / 2 = z by ring] at h

/-- **The simple pole.** `(w − 2/3)·S^{χ_p}_1(w) → A_p(4/3)Res S₁`. -/
theorem cubicUnitLayerCont_simple_pole :
    Tendsto (fun w => (w - 2 / 3) * P.cubicUnitLayerCont w) (𝓝[≠] (2 / 3 : ℂ))
      (𝓝 (P.unitWeight (4 / 3) * untwistedThetaResidue)) := by
  have h43 : (2 : ℂ) * (2 / 3) = 4 / 3 := by norm_num
  have hre43 : (2 / 3 : ℝ) < (4 / 3 : ℂ).re := by norm_num
  have hAd : DifferentiableAt ℂ P.unitWeight (4 / 3) := by
    unfold unitWeight
    exact (differentiableAt_const _).div
      (((P.dilateFactor_differentiableAt _ hre43).mul_const _).mul (P.eulerFactorQ_differentiable _))
      (mul_ne_zero (mul_ne_zero (P.dilateFactor_ne_zero _ hre43) P.twistFactor_ne_zero)
        (P.eulerFactorQ_ne_zero hre43))
  have hA : Tendsto (fun w : ℂ => P.unitWeight (2 * w)) (𝓝[≠] (2 / 3 : ℂ)) (𝓝 (P.unitWeight (4 / 3))) := by
    have hc : ContinuousAt (fun w : ℂ => P.unitWeight (2 * w)) (2 / 3) :=
      ContinuousAt.comp_of_eq (g := P.unitWeight) (f := fun w : ℂ => 2 * w) hAd.continuousAt
        (continuous_const_mul (2 : ℂ)).continuousAt (by norm_num)
    have h := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := {(2 / 3 : ℂ)}ᶜ))
    simpa only [h43] using h
  -- the remainder factor `b(s) = B_p(s)/(s − 4/3)` is continuous at `4/3`
  set b : ℂ → ℂ := fun s => (2 / 3) * ((Fintype.card P.Res : ℂ) * periodArea)⁻¹ /
    (P.dilateFactor s * (ringComplex (symbol 9 P.p) * star (normalizedCubicUnitGauss P.p)) *
      (2 * unitFrequencyWeight s * P.combinationDenom s) * besselSqMellin s) with hb
  have hbd : DifferentiableAt ℂ b (4 / 3) :=
    (differentiableAt_const _).div
      ((((P.dilateFactor_differentiableAt _ hre43).mul_const _).mul
        (((unitFrequencyWeight_differentiable _).const_mul 2).mul (P.combinationDenom_differentiable _))).mul
          (besselSqMellin_differentiableAt _ hre43))
      (mul_ne_zero (mul_ne_zero (mul_ne_zero (P.dilateFactor_ne_zero _ hre43) P.twistFactor_ne_zero)
        (mul_ne_zero (mul_ne_zero two_ne_zero (unitFrequencyWeight_ne_zero _))
          P.combinationDenom_four_thirds_ne_zero))
        (besselSqMellin_ne_zero _ hre43))
  have hbt : Tendsto (fun w : ℂ => b (2 * w)) (𝓝[≠] (2 / 3 : ℂ)) (𝓝 (b (4 / 3))) := by
    have hc : ContinuousAt (fun w : ℂ => b (2 * w)) (2 / 3) :=
      ContinuousAt.comp_of_eq (g := b) (f := fun w : ℂ => 2 * w) hbd.continuousAt
        (continuous_const_mul (2 : ℂ)).continuousAt (by norm_num)
    have h := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := {(2 / 3 : ℂ)}ᶜ))
    simpa only [h43] using h
  have hX : Tendsto (fun s => (s - 4 / 3) ^ 2 * P.remainderComb s) (𝓝[≠] (4 / 3 : ℂ)) (𝓝 0) := by
    have h := P.remainder_remainderData.regPairing_near_four_thirds.sub
      P.heckeShiftRemainder_remainderData.regPairing_near_four_thirds
    rw [sub_zero] at h
    exact h.congr fun s => by rw [remainderComb]; ring
  have hX2 := hX.comp two_mul_tendsto_punctured
  have hrest : Tendsto (fun w : ℂ => (w - 2 / 3) * (P.remainderWeight (2 * w) * P.remainderComb (2 * w)))
      (𝓝[≠] (2 / 3 : ℂ)) (𝓝 0) := by
    have h := (hbt.mul hX2).const_mul (1 / 2 : ℂ)
    rw [mul_zero, mul_zero] at h
    refine h.congr fun w => ?_
    simp only [Function.comp, hb, remainderWeight]
    ring
  have hmain := (hA.mul regularizedUntwistedTheta_simple_pole).add hrest
  rw [add_zero] at hmain
  refine hmain.congr fun w => ?_
  rw [cubicUnitLayerCont]
  ring

/-! ### Vertical bounds -/

theorem norm_dilateFactor_inv_le (a : ℝ) (ha : 2 / 3 < a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, a ≤ s.re → ‖(P.dilateFactor s)⁻¹‖ ≤ C := by
  have hρ0 : 0 < ‖ringComplex P.p‖ := P.norm_pos
  have hρ1 : 1 < ‖ringComplex P.p‖ := by
    have h := ringComplex_norm_sq_eq_absNorm_span P.p
    have hN : (1 : ℝ) < Ideal.absNorm (Ideal.span {P.p} : Ideal O) := by exact_mod_cast P.one_lt_absNorm
    nlinarith
  have hnt : ∀ s : ℂ, ‖((‖ringComplex P.p‖ : ℝ) : ℂ) ^ (-s)‖ = ‖ringComplex P.p‖ ^ (-s.re) := fun s => by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hρ0, Complex.neg_re]
  have hnx : ∀ s : ℂ, ‖(‖ringComplex P.p‖ : ℂ) ^ 2 * (((‖ringComplex P.p‖ : ℝ) : ℂ) ^ (-s)) ^ 3‖ =
      ‖ringComplex P.p‖ ^ 2 * (‖ringComplex P.p‖ ^ (-s.re)) ^ 3 := fun s => by
    rw [norm_mul, norm_pow, norm_pow, hnt, Complex.norm_real, Real.norm_of_nonneg hρ0.le]
  obtain ⟨x₀, hx₀⟩ : ∃ x₀ : ℝ, x₀ = ‖ringComplex P.p‖ ^ 2 * (‖ringComplex P.p‖ ^ (-a)) ^ 3 := ⟨_, rfl⟩
  have hx₀1 : x₀ < 1 := by
    have h := P.norm_rho_cube_lt (a : ℂ) (by simpa using ha)
    rw [hnx] at h
    rw [hx₀]
    simpa using h
  refine ⟨‖ringComplex P.p‖ * ‖ringComplex P.p‖ ^ (-a) * 2 / (1 - x₀),
    div_nonneg (by positivity) (by linarith), fun s hs => ?_⟩
  have hs23 : 2 / 3 < s.re := by linarith
  have key := P.dilateFactor_mul s hs23
  have hne := P.one_sub_ne_zero s hs23
  have ht0 := P.rho_cpow_ne_zero s
  have hA0 : (‖ringComplex P.p‖ : ℂ) * ((‖ringComplex P.p‖ : ℝ) : ℂ) ^ (-s) *
      (1 - (‖ringComplex P.p‖ : ℂ) ^ 2 * (((‖ringComplex P.p‖ : ℝ) : ℂ) ^ (-s)) ^ 3) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (Complex.ofReal_ne_zero.mpr hρ0.ne') ht0) hne
  have htle : ‖ringComplex P.p‖ ^ (-s.re) ≤ ‖ringComplex P.p‖ ^ (-a) :=
    Real.rpow_le_rpow_of_exponent_le hρ1.le (by linarith)
  have hxle : ‖(‖ringComplex P.p‖ : ℂ) ^ 2 * (((‖ringComplex P.p‖ : ℝ) : ℂ) ^ (-s)) ^ 3‖ ≤ x₀ := by
    rw [hnx, hx₀]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) htle 3) (by positivity)
  have hinv : (P.dilateFactor s)⁻¹ = ((‖ringComplex P.p‖ : ℂ) * ((‖ringComplex P.p‖ : ℝ) : ℂ) ^ (-s) *
      (1 - (‖ringComplex P.p‖ : ℂ) ^ 2 * (((‖ringComplex P.p‖ : ℝ) : ℂ) ^ (-s)) ^ 3)) /
        (1 + (‖ringComplex P.p‖ : ℂ) ^ 2 * (((‖ringComplex P.p‖ : ℝ) : ℂ) ^ (-s)) ^ 3) := by
    rw [← key]
    exact (div_mul_cancel_right₀ hA0 _).symm
  set x := (‖ringComplex P.p‖ : ℂ) ^ 2 * (((‖ringComplex P.p‖ : ℝ) : ℂ) ^ (-s)) ^ 3 with hx
  have hnum : ‖1 - x‖ ≤ 2 := by
    have := norm_sub_le (1 : ℂ) x
    rw [norm_one] at this
    linarith
  have hden : 1 - x₀ ≤ ‖1 + x‖ := by
    have := norm_sub_norm_le (1 : ℂ) (-x)
    rw [norm_one, norm_neg, sub_neg_eq_add] at this
    linarith
  rw [hinv, norm_div, norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hρ0.le, hnt,
    div_le_div_iff₀ (by linarith) (by linarith)]
  calc
    ‖ringComplex P.p‖ * ‖ringComplex P.p‖ ^ (-s.re) * ‖1 - x‖ * (1 - x₀) ≤
        ‖ringComplex P.p‖ * ‖ringComplex P.p‖ ^ (-a) * 2 * (1 - x₀) := by gcongr
    _ ≤ ‖ringComplex P.p‖ * ‖ringComplex P.p‖ ^ (-a) * 2 * ‖1 + x‖ := by gcongr

theorem norm_eulerFactorQ_inv_le (a : ℝ) (ha : 2 / 3 < a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, a ≤ s.re → ‖(P.eulerFactorQ s)⁻¹‖ ≤ C := by
  have hN1 : (1 : ℝ) < (Ideal.absNorm (Ideal.span {P.p} : Ideal O) : ℝ) := by
    exact_mod_cast P.one_lt_absNorm
  have hy₀1 : (Ideal.absNorm (Ideal.span {P.p} : Ideal O) : ℝ) ^ (-(3 * (a / 2) - 1)) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg hN1 (by linarith)
  refine ⟨(1 - (Ideal.absNorm (Ideal.span {P.p} : Ideal O) : ℝ) ^ (-(3 * (a / 2) - 1)))⁻¹,
    (inv_pos.mpr (by linarith)).le, fun s hs => ?_⟩
  have hy : ‖unramifiedNormWeight (3 * (s / 2) - 1) (Ideal.span {P.p})‖ ≤
      (Ideal.absNorm (Ideal.span {P.p} : Ideal O) : ℝ) ^ (-(3 * (a / 2) - 1)) := by
    rw [P.normWeight_primeIdeal, Complex.norm_natCast_cpow_of_pos (by have := P.one_lt_absNorm; omega)]
    apply Real.rpow_le_rpow_of_exponent_le hN1.le
    rw [Complex.neg_re, cubeZeta_re]
    linarith
  have hE : 1 - (Ideal.absNorm (Ideal.span {P.p} : Ideal O) : ℝ) ^ (-(3 * (a / 2) - 1)) ≤
      ‖P.eulerFactorQ s‖ := by
    have := norm_sub_norm_le (1 : ℂ) (unramifiedNormWeight (3 * (s / 2) - 1) (Ideal.span {P.p}))
    rw [norm_one] at this
    rw [eulerFactorQ]
    linarith
  rw [norm_inv]
  exact inv_anti₀ (by linarith) hE

/-- `e^{w²}` times the continuation is `O((1 + Im² w)^{−1})` on `a ≤ Re w ≤ 2`, `|Im w| ≥ 1`. -/
theorem cubicUnitLayerCont_gaussian_bound (a : ℝ) (ha : 5 / 8 < a) (ha2 : a ≤ 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w : ℂ, a ≤ w.re → w.re ≤ 2 → 1 ≤ |w.im| →
      ‖Complex.exp (w ^ 2) * P.cubicUnitLayerCont w‖ ≤ C * (1 + w.im ^ 2)⁻¹ := by
  have ha23 : 2 / 3 < 2 * a := by linarith
  obtain ⟨Kd, hKd, hkd⟩ := P.norm_dilateFactor_inv_le (2 * a) ha23
  obtain ⟨Ke, hKe, hke⟩ := P.norm_eulerFactorQ_inv_le (2 * a) ha23
  obtain ⟨Kw, hKw, hkw⟩ := unitFrequencyWeight_inv_le 4
  obtain ⟨Kz, hKz, hkz⟩ := clearedCubeZeta_inv_vertical_bound (2 * a) (by linarith)
  obtain ⟨Km, hKm, hkm⟩ := besselSqMellin_inv_vertical_bound a 2 (by linarith)
  obtain ⟨Kh, hKh, hkh⟩ := P.remainder_remainderData.regPairing_vertical_bound (2 * a) 4 (by linarith) (by norm_num)
  obtain ⟨Ks, hKs, hks⟩ := P.heckeShiftRemainder_remainderData.regPairing_vertical_bound (2 * a) 4
    (by linarith) (by norm_num)
  obtain ⟨C₁, hC₁, hc₁⟩ := continuedUntwistedTheta_gaussian_vertical_bound a 2 ha ha2 (by norm_num)
  set κ := ringComplex (symbol 9 P.p) * star (normalizedCubicUnitGauss P.p) with hκ
  set c₀ : ℂ := (2 / 3) * ((Fintype.card P.Res : ℂ) * periodArea)⁻¹ * κ⁻¹ * 2⁻¹ *
    (star rationalSourceThetaScalar ^ 2 * (2 / 3))⁻¹ with hc₀
  -- the remainder part has growth `(1 + |w|)³e^{4π|Im w|}`
  have hf : ∀ w : ℂ, a ≤ w.re → w.re ≤ 2 → 1 ≤ |w.im| →
      ‖P.remainderWeight (2 * w) * P.remainderComb (2 * w)‖ ≤
        (8 * ‖c₀‖ * Kd * Kw * Kz * Ke * Km * (Kh + Ks)) * (1 + ‖w‖) ^ 3 * Real.exp (4 * Real.pi * |w.im|) := by
    intro w hwa hw2 hwi
    have hr : (2 * w).re = 2 * w.re := by simp
    have hi : (2 * w).im = 2 * w.im := by simp
    have hi1 : 1 ≤ |(2 * w).im| := by rw [hi, abs_mul]; norm_num; linarith
    have hsa : 2 * a ≤ (2 * w).re := by rw [hr]; linarith
    have hs4 : (2 * w).re ≤ 4 := by rw [hr]; linarith
    have hWexp : P.remainderWeight (2 * w) = (2 * w - 4 / 3) * c₀ * (P.dilateFactor (2 * w))⁻¹ *
        (unitFrequencyWeight (2 * w))⁻¹ * (clearedCubeZeta (2 * w))⁻¹ * (P.eulerFactorQ (2 * w))⁻¹ *
          (besselSqMellin (2 * w))⁻¹ := by
      rw [remainderWeight, ← hκ, combinationDenom, hc₀]
      simp only [div_eq_mul_inv, mul_inv]
      ring
    have hX : ‖P.remainderComb (2 * w)‖ ≤ Kh + Ks := by
      rw [remainderComb]
      exact (norm_sub_le _ _).trans (add_le_add (hkh _ hsa (by linarith) hi1) (hks _ hsa (by linarith) hi1))
    have hlin : ‖2 * w - 4 / 3‖ ≤ 2 * (1 + ‖w‖) := by
      have h := norm_sub_le (2 * w) (4 / 3 : ℂ)
      rw [norm_mul] at h
      norm_num at h
      linarith only [h, norm_nonneg w]
    have hz : ‖(clearedCubeZeta (2 * w))⁻¹‖ ≤ Kz * (4 * (1 + ‖w‖) ^ 2) := by
      refine (hkz _ hsa hi1).trans (mul_le_mul_of_nonneg_left ?_ hKz)
      have h := Complex.abs_im_le_norm w
      have h2 := mul_le_mul h h (abs_nonneg _) (norm_nonneg _)
      rw [hi, abs_mul, abs_two]
      nlinarith only [h, h2, abs_nonneg w.im, norm_nonneg w]
    have hw1 : 1 ≤ 1 + ‖w‖ := by linarith [norm_nonneg w]
    rw [hWexp, norm_mul, norm_mul, norm_mul, norm_mul, norm_mul, norm_mul, norm_mul]
    have g1 := hkd _ hsa
    have g2 := hkw _ (by linarith) hs4
    have g3 := hke _ hsa
    have g4 := hkm w hwa hw2 hwi
    calc
      _ ≤ (2 * (1 + ‖w‖)) * ‖c₀‖ * Kd * Kw * (Kz * (4 * (1 + ‖w‖) ^ 2)) * Ke *
          (Km * Real.exp (4 * Real.pi * |w.im|)) * (Kh + Ks) := by gcongr
      _ = _ := by ring
  obtain ⟨C₂, hC₂, hc₂⟩ := gaussian_bound_of_exp_growth (by linarith : (0 : ℝ) ≤ a)
    (by positivity : 0 ≤ 8 * ‖c₀‖ * Kd * Kw * Kz * Ke * Km * (Kh + Ks)) 3 hf
  refine ⟨2 * Kd * ‖κ⁻¹‖ * Ke * C₁ + C₂, by positivity, fun w hwa hw2 hwi => ?_⟩
  have hr : (2 * w).re = 2 * w.re := by simp
  have hsa : 2 * a ≤ (2 * w).re := by rw [hr]; linarith
  have hi0 : w.im ≠ 0 := by intro h; rw [h, abs_zero] at hwi; linarith
  have hA : ‖P.unitWeight (2 * w)‖ ≤ 2 * Kd * ‖κ⁻¹‖ * Ke := by
    have he : P.unitWeight (2 * w) =
        2 * (P.dilateFactor (2 * w))⁻¹ * κ⁻¹ * (P.eulerFactorQ (2 * w))⁻¹ := by
      rw [unitWeight, ← hκ]
      simp only [div_eq_mul_inv, mul_inv]
      ring
    rw [he, norm_mul, norm_mul, norm_mul, show ‖(2 : ℂ)‖ = 2 by norm_num]
    have h1 := hkd _ hsa
    have h2 := hke _ hsa
    gcongr
  rw [cubicUnitLayerCont, mul_add, add_mul]
  refine (norm_add_le _ _).trans (add_le_add ?_ (hc₂ w hwa hw2 hwi))
  rw [regularizedUntwistedTheta_eq_nonreal w (by linarith) hi0,
    show Complex.exp (w ^ 2) * (P.unitWeight (2 * w) * continuedUntwistedTheta w) =
      P.unitWeight (2 * w) * (Complex.exp (w ^ 2) * continuedUntwistedTheta w) by ring, norm_mul]
  calc
    _ ≤ (2 * Kd * ‖κ⁻¹‖ * Ke) * (C₁ * (1 + w.im ^ 2)⁻¹) :=
      mul_le_mul hA (hc₁ w hwa hw2 hwi) (norm_nonneg _) (by positivity)
    _ = _ := by ring

/-! ### The smoothed main term -/

/-- `A_p(4/3) = 2N(p)^{5/6}/(N(p) + 1)·\overline{(9/p)₃}G̃(p)`. -/
theorem unitWeight_four_thirds :
    P.unitWeight (4 / 3) = 2 * ((‖ringComplex P.p‖ : ℝ) : ℂ) ^ (5 / 3 : ℂ) / ((‖ringComplex P.p‖ : ℂ) ^ 2 + 1) *
      (star (ringComplex (symbol 9 P.p)) * normalizedCubicUnitGauss P.p) := by
  have h1 := P.twistUnitResidue_eq_mul
  have h2 := P.twistUnitResidue_closed
  have hR := untwistedSResidue_ne_zero
  apply mul_right_cancel₀ hR
  rw [← h2, h1, unitWeight]
  ring

/-- **The smoothed main term of the unit layer of the cubic twist.** For every primary prime `p` and
`5/8 < a < 2/3`: `Σ_A χ_p(gen A)σ(A) g(log(N(A)/X)) = e^{4/9}A_p(4/3)Res S₁·X^{2/3} + O(X^a)`. -/
theorem cubicUnitLayer_smoothed_main_term (a : ℝ) (ha : 5 / 8 < a) (ha' : a < 2 / 3) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ X : ℝ, 1 ≤ X →
      ‖gaussianSmoothedSum P.cubicUnitCoeff X - (X : ℂ) ^ (2 / 3 : ℂ) *
        (Complex.exp ((2 / 3 : ℂ) ^ 2) * (P.unitWeight (4 / 3) * untwistedThetaResidue))‖ ≤ K * X ^ a := by
  obtain ⟨C, -, hC⟩ := P.cubicUnitLayerCont_gaussian_bound a ha (by linarith)
  refine P.cubicUnitCoeff_bounded.gaussianSmoothedSum_main_term ha'
    (fun w hwa hw2 hp => P.cubicUnitLayerCont_differentiableAt w (by linarith) (by linarith) hp)
    P.cubicUnitLayerCont_simple_pole hC (fun t => ?_)
  rw [P.idealSeries_cubicUnitCoeff]
  exact P.cubicUnitLayerCont_eq_series _ (by norm_num) (by norm_num)

end PrimaryPrime

end GaloisForLFunctions.OrderSixMetaplecticTheory
