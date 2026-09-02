import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenTypeIPrimeAmplifierHeathBrownPowerSourceMoment
import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenTypeIPrimeAmplifierHeathBrownSourceScale

/-!
# Sparse-term absorption for the Heath--Brown Type-I receiver

The exact powered-prime schedule places every Heath--Brown block below `T^(7/25)`.  Consequently
the Deshouillers--Iwaniec sparse term `B^(3/4) T^(3/4)` is below `T^(24/25)`, retaining the fixed
height saving needed in Section 5.1 of Matomäki--Teräväinen.
-/

namespace RHTower.Sieve

open Filter Topology Finset ArithmeticFunction Complex MeasureTheory

noncomputable section

/-- Positivity of the fixed coefficient used after all divisor losses are absorbed. -/
theorem mtTypeIPrimeHeathBrownPowerConstant_nonneg
    {eta : ℝ} (heta : 0 < eta) :
    0 ≤ mtTypeIPrimeHeathBrownPowerConstant eta := by
  have hlemma : 0 ≤ heathBrownLemma34Coefficient eta := by
    have hdiv : 0 < divisorBoundConst (eta / 4) :=
      divisorBoundConst_pos (by linarith)
    rw [heathBrownLemma34Coefficient, heathBrownLemma34PositiveCoefficient,
      heathBrownTheoremFourCoefficient, heathBrownTheoremFourUniversalCoefficient,
      heathBrownMeanSquareCoefficient]
    positivity
  rw [mtTypeIPrimeHeathBrownPowerConstant]
  positivity

/-- Published-epsilon coefficient with the literal sparse term replaced by its fixed
`T^(24/25)` envelope. -/
def mtTypeIPrimeRaisedHeathBrownSparseEpsilonMomentCoefficient
    (N : ℕ) (T epsilon : ℝ) : ℝ :=
  4 * mtTypeIPrimeHeathBrownPowerConstant (epsilon / 24) * T ^ (epsilon / 2) *
    (1 + T / ((N : ℝ) ^ 2) + T ^ (24 / 25 : ℝ) / ((N : ℝ) ^ 2))

/-- The sparse height-envelope coefficient is nonnegative at positive epsilon and
nonnegative height. -/
theorem mtTypeIPrimeRaisedHeathBrownSparseEpsilonMomentCoefficient_nonneg
    {N : ℕ} {T epsilon : ℝ} (hepsilon : 0 < epsilon) (hT : 0 ≤ T) :
    0 ≤ mtTypeIPrimeRaisedHeathBrownSparseEpsilonMomentCoefficient N T epsilon := by
  have hconstant := mtTypeIPrimeHeathBrownPowerConstant_nonneg
    (show 0 < epsilon / 24 by linarith)
  rw [mtTypeIPrimeRaisedHeathBrownSparseEpsilonMomentCoefficient]
  positivity

/-- The block-dependent epsilon coefficient is bounded by the sparse height envelope. -/
theorem mtTypeIPrimeRaisedHeathBrownEpsilonMomentCoefficient_le_sparse
    {N B : ℕ} {T epsilon : ℝ} (hepsilon : 0 < epsilon) (hT : 0 ≤ T)
    (hsparse : (B : ℝ) ^ (3 / 4 : ℝ) * T ^ (3 / 4 : ℝ) ≤
      T ^ (24 / 25 : ℝ)) :
    mtTypeIPrimeRaisedHeathBrownEpsilonMomentCoefficient N B T epsilon ≤
      mtTypeIPrimeRaisedHeathBrownSparseEpsilonMomentCoefficient N T epsilon := by
  have hdiv :
      (B : ℝ) ^ (3 / 4 : ℝ) * T ^ (3 / 4 : ℝ) / ((N : ℝ) ^ 2) ≤
        T ^ (24 / 25 : ℝ) / ((N : ℝ) ^ 2) :=
    div_le_div_of_nonneg_right hsparse (by positivity)
  have houter :
      0 ≤ 4 * mtTypeIPrimeHeathBrownPowerConstant (epsilon / 24) *
        T ^ (epsilon / 2) := by
    have hconstant := mtTypeIPrimeHeathBrownPowerConstant_nonneg
      (show 0 < epsilon / 24 by linarith)
    exact mul_nonneg (mul_nonneg (by norm_num) hconstant)
      (Real.rpow_nonneg hT _)
  rw [mtTypeIPrimeRaisedHeathBrownEpsilonMomentCoefficient,
    mtTypeIPrimeRaisedHeathBrownSparseEpsilonMomentCoefficient]
  apply mul_le_mul_of_nonneg_left _ houter
  linarith

/-- Type-I block moment with the sparse fourth-moment loss already absorbed into height. -/
noncomputable def mtTypeIPrimeHeathBrownSparseEpsilonBlockMomentBound
    (epsilon : ℝ) (a : ℕ → ℂ) (A P ell N : ℕ) (T V : ℝ)
    (r : Fin ell) : ℝ :=
  let B := mtTypeIPrimeHeathBrownBlockLength P ell r
  ((ell : ℝ) / V) * Real.sqrt
      (mtTypeIPrimeRaisedHeathBrownSparseEpsilonMomentCoefficient N T epsilon *
        (∑ m ∈ Finset.Ioc B (2 * B),
          ‖mtTypeIPrimeRaisedCoeff P ell m‖ ^ 2)) *
    Real.sqrt
      (generalMeanSquareConst (fun n => mtTypeILongSquareAF a A n)
          (Finset.Icc 1 ((2 * A) * (2 * A))) 1 +
        generalMeanSquareRate (fun n => mtTypeILongSquareAF a A n)
          (Finset.Icc 1 ((2 * A) * (2 * A))) 1 * T)

/-- A literal block moment is bounded by its block-independent sparse envelope. -/
theorem mtTypeIPrimeHeathBrownEpsilonBlockMomentBound_le_sparse
    {epsilon : ℝ} (hepsilon : 0 < epsilon) (a : ℕ → ℂ)
    (A P ell N : ℕ) (T V : ℝ) (r : Fin ell) (hV : 0 < V)
    (hT : 0 ≤ T)
    (hsparse : (mtTypeIPrimeHeathBrownBlockLength P ell r : ℝ) ^
          (3 / 4 : ℝ) * T ^ (3 / 4 : ℝ) ≤ T ^ (24 / 25 : ℝ)) :
    mtTypeIPrimeHeathBrownEpsilonBlockMomentBound epsilon a A P ell N T V r ≤
      mtTypeIPrimeHeathBrownSparseEpsilonBlockMomentBound epsilon a A P ell N T V r := by
  let B := mtTypeIPrimeHeathBrownBlockLength P ell r
  have hcoeff := mtTypeIPrimeRaisedHeathBrownEpsilonMomentCoefficient_le_sparse
    (N := N) (B := B) hepsilon hT hsparse
  have henergy : 0 ≤ ∑ m ∈ Finset.Ioc B (2 * B),
      ‖mtTypeIPrimeRaisedCoeff P ell m‖ ^ 2 :=
    Finset.sum_nonneg fun m _ => sq_nonneg _
  have hsqrt := Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right hcoeff henergy)
  rw [mtTypeIPrimeHeathBrownEpsilonBlockMomentBound,
    mtTypeIPrimeHeathBrownSparseEpsilonBlockMomentBound]
  dsimp only [B] at hsqrt ⊢
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hsqrt (by positivity)) (Real.sqrt_nonneg _)

/-- Source-scale sub-height receiver with the sparse fourth-moment term uniformly replaced by
`T^(24/25)`. -/
theorem eventually_setIntegral_mtTypeI_primeAmplifier_heathBrown_sparse_sourceScale
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∀ᶠ X : ℝ in atTop,
      ∀ (alpha T : ℝ) (a : ℕ → ℂ) (A N N' : ℕ) (V : ℝ),
      (10999 / 10000 : ℝ) ≤ alpha → alpha ≤ 2 →
      X ^ (1 / 4 : ℝ) ≤ T → T ≤ X →
      2 ≤ N → (N : ℝ) ≤ T → N < N' → N' ≤ 2 * N → 0 < V →
      let P := mtTypeIPrimeScale X alpha
      let ell := mtTypeIPrimeDegree P T
      (∫ t in mtTypeIPrimeAmplifierLargeSet P ell T V,
          ‖mtWattCoefficientBlock a A t‖ ^ 2 *
            ‖mtWattUnitBlock N N' t‖ ^ 2) ≤
        ∑ r : Fin ell,
          mtTypeIPrimeHeathBrownSparseEpsilonBlockMomentBound
            epsilon a A P ell N T V r := by
  filter_upwards
    [eventually_setIntegral_mtTypeI_primeAmplifier_heathBrown_epsilon_sourceScale hepsilon,
      eventually_mtTypeIPrimeHeathBrownSparseTerm_le_height_twenty_four_twenty_fifths]
      with X hsource hsparse
  intro alpha T a A N N' V halpha halpha2 hXT hTX hN hNT hNN' hN'le hV
  dsimp only
  have hbase := hsource alpha T a A N N' V halpha halpha2 hXT hTX
    hN hNT hNN' hN'le hV
  have hT0 : 0 ≤ T := by
    have hN0 : (0 : ℝ) ≤ N := by positivity
    exact hN0.trans hNT
  calc
    _ ≤ ∑ r : Fin (mtTypeIPrimeDegree (mtTypeIPrimeScale X alpha) T),
        mtTypeIPrimeHeathBrownEpsilonBlockMomentBound epsilon a A
          (mtTypeIPrimeScale X alpha)
          (mtTypeIPrimeDegree (mtTypeIPrimeScale X alpha) T) N T V r := hbase
    _ ≤ _ := Finset.sum_le_sum fun r _ =>
      mtTypeIPrimeHeathBrownEpsilonBlockMomentBound_le_sparse hepsilon a A
        (mtTypeIPrimeScale X alpha)
        (mtTypeIPrimeDegree (mtTypeIPrimeScale X alpha) T) N T V r hV
          hT0
          (hsparse alpha T (by linarith) halpha2 hXT r)

end

end RHTower.Sieve
