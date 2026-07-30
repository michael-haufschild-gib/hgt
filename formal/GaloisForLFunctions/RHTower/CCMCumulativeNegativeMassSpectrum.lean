import Mathlib.NumberTheory.LSeries.SumCoeff
import GaloisForLFunctions.RHTower.CCMPrimeGammaSourceEnergySpectrum
import GaloisForLFunctions.RHTower.XiGuinandWeilRectangularGammaPolarSourceLaw

/-!
# Cumulative negative-mass spectra of the sharp prime--Gamma and prime--polar carriers

For a nonnegative Dirichlet coefficient, the absolute-convergence abscissa is exactly the
threshold for supercritical power bounds on its cumulative mass.  Applying this general
Tauberian equivalence to the negative part of the explicit sharp prime--Gamma carrier gives a
cumulative source spectrum for the horizontal Xi divisor:

* every horizontal Xi zero bound is equivalent to the corresponding cumulative growth law;
* RH is equivalent to the critical cumulative bound at exponent one;
* under false RH the exact cumulative-growth threshold is `1 + xiRightTransverseSup`.

The bounded Gamma--polar correction transfers the same spectrum to the literal finite
prime--polar source.  This replaces a convergence-only carrier by a positive monotone quantity
visible directly in finite arithmetic coefficients.
-/

open Complex Filter Function Set LSeries Finset Asymptotics

namespace RHTower

noncomputable section

/-- Supercritical power bounds for the cumulative mass of a real sequence. -/
def NonnegativeDirichletSummatoryGrowthAt (a : ℕ → ℝ) (sigma : ℝ) : Prop :=
  ∀ epsilon : ℝ, 0 < epsilon →
    (fun N : ℕ => ∑ n ∈ Finset.Icc 1 N, a n) =O[atTop]
      (fun N : ℕ => (N : ℝ) ^ (sigma + epsilon))

private theorem summatory_isBigO_of_nonnegative_LSeriesSummable
    {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) {x y : ℝ}
    (hx : 0 ≤ x) (hxy : x ≤ y)
    (hsum : Summable fun n : ℕ => a n / (n : ℝ) ^ x) :
    (fun N : ℕ => ∑ n ∈ Finset.Icc 1 N, a n) =O[atTop]
      (fun N : ℕ => (N : ℝ) ^ y) := by
  let T : ℝ := ∑' n : ℕ, a n / (n : ℝ) ^ x
  have hT : 0 ≤ T := by
    exact tsum_nonneg fun n => div_nonneg (ha n) (Real.rpow_nonneg (Nat.cast_nonneg n) x)
  apply Asymptotics.IsBigO.of_bound T
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hsum_nonneg : 0 ≤ ∑ n ∈ Finset.Icc 1 N, a n :=
    Finset.sum_nonneg fun n _ => ha n
  have hpowN_nonneg : 0 ≤ (N : ℝ) ^ y :=
    Real.rpow_nonneg (Nat.cast_nonneg N) y
  rw [Real.norm_eq_abs, abs_of_nonneg hsum_nonneg,
    Real.norm_eq_abs, abs_of_nonneg hpowN_nonneg]
  calc
    ∑ n ∈ Finset.Icc 1 N, a n =
        ∑ n ∈ Finset.Icc 1 N, (a n / (n : ℝ) ^ x) * (n : ℝ) ^ x := by
      apply Finset.sum_congr rfl
      intro n hn
      have hn0 : (n : ℝ) ^ x ≠ 0 :=
        (Real.rpow_pos_of_pos (by exact_mod_cast (Finset.mem_Icc.mp hn).1) x).ne'
      exact (div_mul_cancel₀ (a n) hn0).symm
    _ ≤ ∑ n ∈ Finset.Icc 1 N, (a n / (n : ℝ) ^ x) * (N : ℝ) ^ x := by
      apply Finset.sum_le_sum
      intro n hn
      apply mul_le_mul_of_nonneg_left
      · apply Real.rpow_le_rpow (Nat.cast_nonneg n)
        · exact_mod_cast (Finset.mem_Icc.mp hn).2
        · exact hx
      · exact div_nonneg (ha n) (Real.rpow_nonneg (Nat.cast_nonneg n) x)
    _ = (∑ n ∈ Finset.Icc 1 N, a n / (n : ℝ) ^ x) * (N : ℝ) ^ x := by
      rw [Finset.sum_mul]
    _ ≤ T * (N : ℝ) ^ x := by
      apply mul_le_mul_of_nonneg_right
      · exact hsum.sum_le_tsum (Finset.Icc 1 N)
          (fun n _ => div_nonneg (ha n) (Real.rpow_nonneg (Nat.cast_nonneg n) x))
      · exact Real.rpow_nonneg (Nat.cast_nonneg N) x
    _ ≤ T * (N : ℝ) ^ y := by
      apply mul_le_mul_of_nonneg_left
      · exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN) hxy
      · exact hT

/-- For nonnegative coefficients, the absolute-convergence abscissa is at most `sigma`
exactly when every supercritical power bounds the cumulative coefficient mass. -/
theorem abscissaOfAbsConv_le_iff_nonnegativeDirichletSummatoryGrowthAt
    {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) {sigma : ℝ} (hsigma : 0 ≤ sigma) :
    LSeries.abscissaOfAbsConv (fun n => ((a n : ℝ) : ℂ)) ≤ (sigma : EReal) ↔
      NonnegativeDirichletSummatoryGrowthAt a sigma := by
  constructor
  · intro habs epsilon hepsilon
    let x : ℝ := sigma + epsilon / 2
    have hx : 0 ≤ x := by
      dsimp only [x]
      linarith
    have habsx :
        LSeries.abscissaOfAbsConv (fun n => ((a n : ℝ) : ℂ)) < (x : EReal) := by
      apply habs.trans_lt
      exact_mod_cast (by dsimp only [x]; linarith : sigma < x)
    have hsum : Summable fun n : ℕ => a n / (n : ℝ) ^ x :=
      LSeries.summable_real_of_abscissaOfAbsConv_lt habsx
    apply summatory_isBigO_of_nonnegative_LSeriesSummable ha hx (by
      dsimp only [x]
      linarith : x ≤ sigma + epsilon) hsum
  · intro hgrowth
    apply LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable
    intro y hy
    let epsilon : ℝ := (y - sigma) / 2
    have hepsilon : 0 < epsilon := by
      dsimp only [epsilon]
      linarith
    have hO := hgrowth epsilon hepsilon
    apply LSeriesSummable_of_sum_norm_bigO_and_nonneg hO ha
    · dsimp only [epsilon]
      linarith
    · simp only [ofReal_re]
      dsimp only [epsilon]
      linarith

/-- Every horizontal Xi zero bound is exactly a cumulative-growth law for the explicit
prime--Gamma negative mass. -/
theorem xiZeroHalfPlaneBound_iff_primeGammaCumulativeNegativeMassGrowth
    {L alpha : ℝ} (hL : 0 < L) (halpha : 0 ≤ alpha) {N : ℕ}
    (hN : ∀ n : ℕ, N ≤ n → 1 ≤ n ∧ L ≤ Real.log n / 2) :
    XiZeroHalfPlaneBound alpha ↔
      NonnegativeDirichletSummatoryGrowthAt
        (xiRectangularPrimeGammaTailNegativePart L N) (1 + alpha) := by
  have hnonneg : ∀ n, 0 ≤ xiRectangularPrimeGammaTailNegativePart L N n := by
    intro n
    exact negPart_nonneg _
  rw [← abscissaOfAbsConv_le_iff_nonnegativeDirichletSummatoryGrowthAt
    hnonneg (by linarith : 0 ≤ 1 + alpha)]
  constructor
  · intro hzeros
    apply LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable
    intro sigma hsigma
    have hepsilon : 0 < sigma - (1 + alpha) := by linarith
    have henergy :=
      (xiZeroHalfPlaneBound_iff_primeGammaTailNegativeEnergyAbove hL halpha hN).mp hzeros
    convert henergy (sigma - (1 + alpha)) hepsilon using 1
    ring_nf
  · intro habscissa
    apply (xiZeroHalfPlaneBound_iff_primeGammaTailNegativeEnergyAbove hL halpha hN).mpr
    intro epsilon hepsilon
    apply LSeriesSummable_of_abscissaOfAbsConv_lt_re
    have hstrict : ((1 + alpha : ℝ) : EReal) <
        ((1 + alpha + epsilon : ℝ) : EReal) := by
      exact_mod_cast (by linarith : (1 + alpha : ℝ) < 1 + alpha + epsilon)
    simpa only [ofReal_re] using habscissa.trans_lt hstrict

/-- RH is exactly the critical cumulative-mass law for the explicit prime--Gamma source. -/
theorem riemannHypothesis_iff_primeGammaCumulativeNegativeMassCriticalGrowth
    {L : ℝ} (hL : 0 < L) {N : ℕ}
    (hN : ∀ n : ℕ, N ≤ n → 1 ≤ n ∧ L ≤ Real.log n / 2) :
    RiemannHypothesis ↔
      NonnegativeDirichletSummatoryGrowthAt
        (xiRectangularPrimeGammaTailNegativePart L N) 1 := by
  have hnonneg : ∀ n, 0 ≤ xiRectangularPrimeGammaTailNegativePart L N n := by
    intro n
    exact negPart_nonneg _
  rw [← abscissaOfAbsConv_le_iff_nonnegativeDirichletSummatoryGrowthAt hnonneg zero_le_one]
  simpa only [xiRectangularPrimeGammaTailNegativeDirichletCoefficient] using!
    riemannHypothesis_iff_primeGammaTailNegativePart_abscissa_le_one hL hN

/-- Under false RH, the cumulative-growth threshold is exactly the shifted right-transverse
Xi displacement. -/
theorem primeGammaCumulativeNegativeMassGrowth_iff_transverseSup_le_of_not_rh
    {L sigma : ℝ} (hL : 0 < L) (hsigma : 0 ≤ sigma) {N : ℕ}
    (hN : ∀ n : ℕ, N ≤ n → 1 ≤ n ∧ L ≤ Real.log n / 2)
    (hnot : ¬ RiemannHypothesis) :
    NonnegativeDirichletSummatoryGrowthAt
        (xiRectangularPrimeGammaTailNegativePart L N) sigma ↔
      1 + xiRightTransverseSup ≤ sigma := by
  have hnonneg : ∀ n, 0 ≤ xiRectangularPrimeGammaTailNegativePart L N n := by
    intro n
    exact negPart_nonneg _
  rw [← abscissaOfAbsConv_le_iff_nonnegativeDirichletSummatoryGrowthAt hnonneg hsigma]
  rw [show LSeries.abscissaOfAbsConv
      (fun n => ((xiRectangularPrimeGammaTailNegativePart L N n : ℝ) : ℂ)) =
        ((1 + xiRightTransverseSup : ℝ) : EReal) by
    simpa only [xiRectangularPrimeGammaTailNegativeDirichletCoefficient] using!
      xiRectangularPrimeGammaTailNegativePart_abscissa_eq_transverseSup_of_not_rh
        hL hN hnot]
  exact EReal.coe_le_coe_iff

/-- Full unconditional dichotomy for the cumulative negative prime--Gamma mass.  Under RH every
nonnegative threshold is admissible; under false RH the exact threshold is
`1 + xiRightTransverseSup`. -/
theorem primeGammaCumulativeNegativeMassGrowth_dichotomy
    {L : ℝ} (hL : 0 < L) {N : ℕ}
    (hN : ∀ n : ℕ, N ≤ n → 1 ≤ n ∧ L ≤ Real.log n / 2) :
    (RiemannHypothesis ∧
        ∀ sigma : ℝ, 0 ≤ sigma →
          NonnegativeDirichletSummatoryGrowthAt
            (xiRectangularPrimeGammaTailNegativePart L N) sigma) ∨
      (¬ RiemannHypothesis ∧
        ∀ sigma : ℝ, 0 ≤ sigma →
          (NonnegativeDirichletSummatoryGrowthAt
              (xiRectangularPrimeGammaTailNegativePart L N) sigma ↔
            1 + xiRightTransverseSup ≤ sigma)) := by
  by_cases hRH : RiemannHypothesis
  · left
    refine ⟨hRH, fun sigma hsigma => ?_⟩
    have hnonneg : ∀ n, 0 ≤ xiRectangularPrimeGammaTailNegativePart L N n := by
      intro n
      exact negPart_nonneg _
    apply (abscissaOfAbsConv_le_iff_nonnegativeDirichletSummatoryGrowthAt
      hnonneg hsigma).mp
    rw [show LSeries.abscissaOfAbsConv
        (fun n => ((xiRectangularPrimeGammaTailNegativePart L N n : ℝ) : ℂ)) = ⊥ by
      simpa only [xiRectangularPrimeGammaTailNegativeDirichletCoefficient] using!
        xiRectangularPrimeGammaTailNegativePart_abscissa_eq_bot_of_rh hL hN hRH]
    exact bot_le
  · right
    exact ⟨hRH, fun sigma hsigma =>
      primeGammaCumulativeNegativeMassGrowth_iff_transverseSup_le_of_not_rh
        hL hsigma hN hRH⟩

/-- Under false RH, the cumulative negative mass has exact power order
`1 + xiRightTransverseSup`: every larger power is an upper bound, while no smaller power is. -/
theorem primeGammaCumulativeNegativeMass_exactPowerOrder_of_not_rh
    {L : ℝ} (hL : 0 < L) {N : ℕ}
    (hN : ∀ n : ℕ, N ≤ n → 1 ≤ n ∧ L ≤ Real.log n / 2)
    (hnot : ¬ RiemannHypothesis) :
    (∀ epsilon : ℝ, 0 < epsilon →
      (fun X : ℕ => ∑ n ∈ Finset.Icc 1 X,
          xiRectangularPrimeGammaTailNegativePart L N n) =O[atTop]
        (fun X : ℕ => (X : ℝ) ^ (1 + xiRightTransverseSup + epsilon))) ∧
    (∀ eta : ℝ, 0 < eta → eta < 1 + xiRightTransverseSup →
      ¬ (fun X : ℕ => ∑ n ∈ Finset.Icc 1 X,
          xiRectangularPrimeGammaTailNegativePart L N n) =O[atTop]
        (fun X : ℕ => (X : ℝ) ^ (1 + xiRightTransverseSup - eta))) := by
  have hsigma : 0 ≤ 1 + xiRightTransverseSup := by
    linarith [xiRightTransverseSup_nonneg]
  have hgrowth : NonnegativeDirichletSummatoryGrowthAt
      (xiRectangularPrimeGammaTailNegativePart L N) (1 + xiRightTransverseSup) :=
    (primeGammaCumulativeNegativeMassGrowth_iff_transverseSup_le_of_not_rh
      hL hsigma hN hnot).mpr le_rfl
  refine ⟨hgrowth, ?_⟩
  intro eta heta hetaThreshold hO
  have hnonneg : ∀ n, 0 ≤ xiRectangularPrimeGammaTailNegativePart L N n := by
    intro n
    exact negPart_nonneg _
  have habscissa : LSeries.abscissaOfAbsConv
      (fun n => ((xiRectangularPrimeGammaTailNegativePart L N n : ℝ) : ℂ)) ≤
        ((1 + xiRightTransverseSup - eta : ℝ) : EReal) := by
    apply LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable
    intro y hy
    apply LSeriesSummable_of_sum_norm_bigO_and_nonneg hO hnonneg
    · linarith
    · simpa only [ofReal_re] using hy
  have habscissaEq : LSeries.abscissaOfAbsConv
      (fun n => ((xiRectangularPrimeGammaTailNegativePart L N n : ℝ) : ℂ)) =
        ((1 + xiRightTransverseSup : ℝ) : EReal) := by
    simpa only [xiRectangularPrimeGammaTailNegativeDirichletCoefficient] using!
      xiRectangularPrimeGammaTailNegativePart_abscissa_eq_transverseSup_of_not_rh
        hL hN hnot
  rw [habscissaEq] at habscissa
  have : 1 + xiRightTransverseSup ≤ 1 + xiRightTransverseSup - eta := by
    exact_mod_cast habscissa
  linarith

/-- Every horizontal Xi zero bound is exactly a cumulative-growth law for the negative part of
the literal finite prime--polar source. -/
theorem all_xiZeros_re_le_iff_rectangularPrimePolarSource_cumulativeNegativeMassGrowth
    {L alpha : ℝ} (hL : 0 < L) (halpha : 0 ≤ alpha) {N : ℕ}
    (hN : ∀ n : ℕ, N ≤ n → 1 ≤ n ∧ L ≤ Real.log n / 2) :
    (∀ rho : ℂ, xi rho = 0 → rho.re ≤ 1 / 2 + alpha) ↔
      NonnegativeDirichletSummatoryGrowthAt
        (rectangularPrimePolarSourceTailNegativePart L N) (1 + alpha) := by
  have hnonneg : ∀ n, 0 ≤ rectangularPrimePolarSourceTailNegativePart L N n :=
    rectangularPrimePolarSourceTailNegativePart_nonneg L N
  rw [← abscissaOfAbsConv_le_iff_nonnegativeDirichletSummatoryGrowthAt
    hnonneg (by linarith : 0 ≤ 1 + alpha)]
  simpa only [rectangularPrimePolarSourceTailNegativeDirichletCoefficient] using!
    all_xiZeros_re_le_iff_rectangularPrimePolarSource_negativeAbscissa_le
      hL halpha hN

/-- RH is exactly the critical cumulative-mass law for the negative part of one literal finite
prime--polar source sequence. -/
theorem riemannHypothesis_iff_rectangularPrimePolarSource_cumulativeNegativeMassCriticalGrowth
    {L : ℝ} (hL : 0 < L) {N : ℕ}
    (hN : ∀ n : ℕ, N ≤ n → 1 ≤ n ∧ L ≤ Real.log n / 2) :
    RiemannHypothesis ↔
      NonnegativeDirichletSummatoryGrowthAt
        (rectangularPrimePolarSourceTailNegativePart L N) 1 := by
  have hnonneg : ∀ n, 0 ≤ rectangularPrimePolarSourceTailNegativePart L N n :=
    rectangularPrimePolarSourceTailNegativePart_nonneg L N
  rw [← abscissaOfAbsConv_le_iff_nonnegativeDirichletSummatoryGrowthAt hnonneg zero_le_one]
  simpa only [rectangularPrimePolarSourceTailNegativeDirichletCoefficient] using!
    riemannHypothesis_iff_rectangularPrimePolarSource_negativeAbscissa_le_one hL hN

/-- The cumulative negative finite prime--polar mass has exact transverse power order
`1 + xiRightTransverseSup`: every larger power is an upper bound, while no smaller power within
the transverse range is.  Under RH the lower assertion is vacuous and the upper assertion is the
critical cumulative law. -/
theorem rectangularPrimePolarSource_cumulativeNegativeMass_exactTransversePowerOrder
    {L : ℝ} (hL : 0 < L) {N : ℕ}
    (hN : ∀ n : ℕ, N ≤ n → 1 ≤ n ∧ L ≤ Real.log n / 2) :
    (∀ epsilon : ℝ, 0 < epsilon →
      (fun X : ℕ => ∑ n ∈ Finset.Icc 1 X,
          rectangularPrimePolarSourceTailNegativePart L N n) =O[atTop]
        (fun X : ℕ => (X : ℝ) ^ (1 + xiRightTransverseSup + epsilon))) ∧
    (∀ eta : ℝ, 0 < eta → eta < xiRightTransverseSup →
      ¬ (fun X : ℕ => ∑ n ∈ Finset.Icc 1 X,
          rectangularPrimePolarSourceTailNegativePart L N n) =O[atTop]
        (fun X : ℕ => (X : ℝ) ^ (1 + xiRightTransverseSup - eta))) := by
  have hsupNonneg : 0 ≤ xiRightTransverseSup := xiRightTransverseSup_nonneg
  have henergy :=
    (xiRightTransverseSup_le_iff_negativePartEnergyAbove
      hL hsupNonneg hN).mp le_rfl
  have hzeros : XiZeroHalfPlaneBound xiRightTransverseSup :=
    (xiZeroHalfPlaneBound_iff_rectangularNegativeEnergyAbove
      hL hsupNonneg hN).mpr henergy
  have hgrowth :=
    (all_xiZeros_re_le_iff_rectangularPrimePolarSource_cumulativeNegativeMassGrowth
      hL hsupNonneg hN).mp hzeros
  refine ⟨hgrowth, ?_⟩
  intro eta heta hetaSup hO
  let alpha : ℝ := xiRightTransverseSup - eta
  have halpha : 0 ≤ alpha := by
    dsimp only [alpha]
    linarith
  have hnonneg : ∀ n, 0 ≤ rectangularPrimePolarSourceTailNegativePart L N n :=
    rectangularPrimePolarSourceTailNegativePart_nonneg L N
  have habscissa : LSeries.abscissaOfAbsConv
      (rectangularPrimePolarSourceTailNegativeDirichletCoefficient L N) ≤
        ((1 + alpha : ℝ) : EReal) := by
    apply LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable
    intro y hy
    apply LSeriesSummable_of_sum_norm_bigO_and_nonneg hO hnonneg
    · linarith
    · simp only [ofReal_re]
      dsimp only [alpha] at hy
      linarith
  have hzero : XiZeroHalfPlaneBound alpha := by
    exact (all_xiZeros_re_le_iff_rectangularPrimePolarSource_negativeAbscissa_le
      hL halpha hN).mpr habscissa
  have henergyAlpha :=
    (xiZeroHalfPlaneBound_iff_rectangularNegativeEnergyAbove
      hL halpha hN).mp hzero
  have hsupAlpha :=
    (xiRightTransverseSup_le_iff_negativePartEnergyAbove
      hL halpha hN).mpr henergyAlpha
  dsimp only [alpha] at hsupAlpha
  linarith

end

end RHTower
