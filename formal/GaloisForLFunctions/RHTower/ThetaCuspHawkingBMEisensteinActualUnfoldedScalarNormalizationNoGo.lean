import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMEisensteinScalarLandingNoGo
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMEisensteinRamanujanProductDirichletSeries
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMEisensteinTwoKBesselMellinProduct
import GaloisForLFunctions.PNTPlus.MellinCalculus
import GaloisForLFunctions.RHTower.XiRealAxisGrowth

/-!
# Actual unfolded scalar normalization no-go at `(P,Q) = (2,5)`

This module evaluates the literal nonconstant Fourier source of the repeated Eisenstein scalar
unfolding at the honest absolute-convergence point `(P,Q) = (2,5)`.  The actual completed
Whittaker coefficient is first identified with the corpus generalized-divisor arithmetic.  After
the frequency pairing and the change of variables `x = 2πny`, the source is

`8 · Λ(10) · (2π)^(-5) · ∫₀⁺∞ x⁴ K_{3/2}(x)^(2 : ℕ) dx
  · L(σ_{-3}σ_{-3}, 2)`.

The two-shift Ramanujan product and two-K Mellin product give exactly

`Λ(8) · Λ(5)^(2 : ℕ) · Λ(2)`.

The global xi functional equation identifies `Λ(2) = Λ(-1)`, so this is also the corpus
classical Rankin--Selberg--Zagier value.  In contrast, the prescribed canonical four-xi vertex is
exactly `2800` times this nonzero source.  Consequently the unmodified family-level HB scalar
landing is false already inside the absolute-convergence chamber; meromorphic continuation and
regularization cannot repair this pointwise normalization mismatch.

This kills the chain

`actual meromorphic scalar triple regularization -> canonical four-xi scalar landing ->
 C-A.9u balanced source -> negative BM -> left QNM -> HC94 cocycle -> RH`.

The sharp positive survivor is the exact pole-fill multiplier `2800` at `(2,5)`, together with the
requirement that any replacement HB scalar landing include its normalization before analytic
continuation.

`[NEW] [PAPER-PROVED] [LEAN-PROVED] [ROUTE KILLED] [HB] [C-A.9x-c] [C-A.9x-d]`
-/

open Complex Real MeasureTheory Set
open scoped BigOperators

noncomputable section

namespace RHTower

/-- The corpus generalized-divisor convolution is the usual finite divisor sum on a positive
index.  This is the arithmetic identification needed to read the actual Whittaker coefficient. -/
lemma d4BMGeneralizedDivisorArithmetic_eq_divisorSum
    (a : ℂ) (n : D4BMPositiveIndex) :
    d4BMGeneralizedDivisorArithmetic a n.1 =
      ∑ d ∈ n.1.divisors, (d : ℂ) ^ a := by
  rw [d4BMGeneralizedDivisorArithmetic, mul_comm,
    ArithmeticFunction.mul_apply,
    Nat.sum_divisorsAntidiagonal (fun x y =>
      d4BMPowerArithmetic a x * (ArithmeticFunction.zeta : ArithmeticFunction ℂ) y)]
  apply Finset.sum_congr rfl
  intro d hd
  have hdvd : d ∣ n.1 := Nat.dvd_of_mem_divisors hd
  have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdvd n.2
  have hquot : n.1 / d ≠ 0 :=
    (Nat.div_pos (Nat.le_of_dvd n.2 hdvd) hdpos).ne'
  simp [d4BMPowerArithmetic_apply, ArithmeticFunction.zeta_apply,
    hdpos.ne', hquot]

/-- The actual completed Eisenstein Whittaker coefficient is precisely the generalized-divisor
coefficient used by the Ramanujan product theorem. -/
theorem d4BM_completedEisensteinWhittakerCoefficient_eq_generalizedDivisorArithmetic
    (u : ℂ) (n : D4BMPositiveIndex) :
    d4BMCompletedEisensteinWhittakerCoefficient u n =
      (n.1 : ℂ) ^ u * d4BMGeneralizedDivisorArithmetic (-2 * u) n.1 := by
  rw [d4BMCompletedEisensteinWhittakerCoefficient,
    d4BMGeneralizedDivisorArithmetic_eq_divisorSum]

/-- Closed Ramanujan chamber for the arithmetic source at `(P,Q) = (2,5)`. -/
def d4BMTwoFiveRamanujanProductChamber : D4BMRamanujanProductChamber where
  a := ⟨-3, by norm_num⟩
  b := ⟨-3, by norm_num⟩
  w := 2
  w_re_gt_one := by norm_num

/-- Exact two-shift divisor-product Dirichlet series at the source point. -/
lemma d4BM_twoFive_divisorProductLSeries_eq :
    LSeries (d4BMDivisorProductArithmetic (-3) (-3)) 2 =
      riemannZeta 2 * riemannZeta 5 * riemannZeta 5 * riemannZeta 8 /
        riemannZeta 10 := by
  have h := LSeries_d4BMDivisorProductArithmetic_eq_fourZetaQuotient
    d4BMTwoFiveRamanujanProductChamber
  norm_num [d4BMTwoFiveRamanujanProductChamber, d4BMRamanujanFourZetaValue,
    d4BMRamanujanPolarZetaValue] at h
  exact h

/-- Exact two-K Mellin integral at the source point. -/
lemma d4BM_twoFive_besselMellin_eq :
    (∫ x : ℝ in Set.Ioi 0,
      (x : ℂ) ^ ((5 : ℂ) - 1) *
        GaloisForLFunctions.HTGeometry.modifiedBesselKOrder x (3 / 2) *
        GaloisForLFunctions.HTGeometry.modifiedBesselKOrder x (3 / 2)) =
      (2 : ℂ) ^ ((5 : ℂ) - 3) / Complex.Gamma 5 *
        (Complex.Gamma ((5 + 3 / 2 + 3 / 2 : ℂ) / 2) *
          Complex.Gamma ((5 + 3 / 2 - 3 / 2 : ℂ) / 2) *
          Complex.Gamma ((5 - 3 / 2 + 3 / 2 : ℂ) / 2) *
          Complex.Gamma ((5 - 3 / 2 - 3 / 2 : ℂ) / 2)) := by
  exact _root_.GaloisForLFunctions.RHTower.integral_cpow_mul_modifiedBesselKOrder_mul_modifiedBesselKOrder
      (s := (5 : ℂ)) (mu := (3 / 2 : ℂ)) (nu := (3 / 2 : ℂ)) (by norm_num)

/-- Literal nonconstant unfolded scalar source after inserting the actual Fourier coefficient,
pairing the frequencies `±n`, and scaling `x = 2πny`. -/
def d4BMActualTwoFiveUnfoldedScalarSource : ℂ :=
  8 * reflectedCompletedLambda 10 *
    ((((2 * Real.pi : ℝ) : ℂ) ^ (-(5 : ℂ)))) *
    (∫ x : ℝ in Set.Ioi 0,
      (x : ℂ) ^ ((5 : ℂ) - 1) *
        GaloisForLFunctions.HTGeometry.modifiedBesselKOrder x (3 / 2) *
        GaloisForLFunctions.HTGeometry.modifiedBesselKOrder x (3 / 2)) *
    LSeries (d4BMDivisorProductArithmetic (-3) (-3)) 2

/-- Positive-half-plane completed-zeta product forced by the literal source. -/
def d4BMTwoFivePositiveLambdaProduct : ℂ :=
  reflectedCompletedLambda 8 * reflectedCompletedLambda 5 ^ 2 *
    reflectedCompletedLambda 2

private lemma d4BM_archimedean_two_five :
    8 * Complex.Gammaℝ (10 : ℂ) *
        ((((2 * Real.pi : ℝ) : ℂ) ^ (-(5 : ℂ)))) *
        ((2 : ℂ) ^ ((5 : ℂ) - 3) / Complex.Gamma 5 *
          (Complex.Gamma 4 * Complex.Gamma (5 / 2) *
            Complex.Gamma (5 / 2) * Complex.Gamma 1)) =
      Complex.Gammaℝ (8 : ℂ) * Complex.Gammaℝ (5 : ℂ) ^ 2 *
        Complex.Gammaℝ (2 : ℂ) := by
  rw [Complex.Gammaℝ, Complex.Gammaℝ, Complex.Gammaℝ, Complex.Gammaℝ]
  norm_num
  have h2pi : ((2 : ℂ) * (Real.pi : ℂ)) ^ (-(5 : ℂ)) =
      (2 : ℂ) ^ (-(5 : ℂ)) * (Real.pi : ℂ) ^ (-(5 : ℂ)) := by
    simpa using Complex.mul_cpow_ofReal_nonneg
      (by norm_num : (0 : ℝ) ≤ 2) Real.pi_pos.le (-(5 : ℂ))
  rw [h2pi]
  have hpow2 : (2 : ℂ) ^ (-(5 : ℂ)) = 1 / 32 := by
    have h := Complex.cpow_neg_eq_inv_pow_ofReal_pos
      (a := 2) (by norm_num : (0 : ℝ) < 2) (5 : ℂ)
    norm_num at h
    exact h
  rw [hpow2]
  ring_nf
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hleft : ((Real.pi : ℂ) ^ (-(5 : ℂ))) ^ 2 =
      (Real.pi : ℂ) ^ (-(10 : ℂ)) := by
    rw [pow_two, ← Complex.cpow_add _ _ hpi]
    congr 1
    ring
  have hhalf : ((Real.pi : ℂ) ^ (-(5 / 2 : ℂ))) ^ 2 =
      (Real.pi : ℂ) ^ (-(5 : ℂ)) := by
    rw [pow_two, ← Complex.cpow_add _ _ hpi]
    congr 1
    ring
  have houter :
      (Real.pi : ℂ) ^ (-(4 : ℂ)) * (Real.pi : ℂ) ^ (-(5 : ℂ)) *
          (Real.pi : ℂ) ^ (-(1 : ℂ)) =
        (Real.pi : ℂ) ^ (-(10 : ℂ)) := by
    rw [← Complex.cpow_add _ _ hpi, ← Complex.cpow_add _ _ hpi]
    congr 1
    ring
  have hhalf' : ((Real.pi : ℂ) ^ (-(5 : ℂ) / 2)) ^ 2 =
      (Real.pi : ℂ) ^ (-(5 : ℂ)) := by
    convert hhalf using 1
    all_goals ring
  rw [hleft, hhalf']
  calc
    (Real.pi : ℂ) ^ (-(10 : ℂ)) * Complex.Gamma (5 / 2) ^ 2 * 6 =
        Complex.Gamma (5 / 2) ^ 2 * 6 *
          (Real.pi : ℂ) ^ (-(10 : ℂ)) := by ring
    _ = Complex.Gamma (5 / 2) ^ 2 * 6 *
          ((Real.pi : ℂ) ^ (-(4 : ℂ)) * (Real.pi : ℂ) ^ (-(5 : ℂ)) *
            (Real.pi : ℂ) ^ (-(1 : ℂ))) := by rw [houter]
    _ = Complex.Gamma (5 / 2) ^ 2 * (Real.pi : ℂ) ^ (-(4 : ℂ)) *
          (Real.pi : ℂ) ^ (-(5 : ℂ)) * (Real.pi : ℂ) ^ (-(1 : ℂ)) * 6 := by ring

/- Exact evaluation of the literal unfolded source. -/
set_option maxHeartbeats 800000 in
theorem d4BM_actualTwoFiveUnfoldedScalarSource_eq_positiveLambdaProduct :
    d4BMActualTwoFiveUnfoldedScalarSource = d4BMTwoFivePositiveLambdaProduct := by
  rw [d4BMActualTwoFiveUnfoldedScalarSource, d4BMTwoFivePositiveLambdaProduct,
    d4BM_twoFive_besselMellin_eq, d4BM_twoFive_divisorProductLSeries_eq]
  norm_num
  simp only [reflectedCompletedLambda]
  have hzeta10 : riemannZeta (10 : ℂ) ≠ 0 :=
    riemannZeta_ne_zero_of_one_lt_re (by norm_num)
  let A : ℂ :=
    8 * Complex.Gammaℝ (10 : ℂ) *
      ((2 * (Real.pi : ℂ)) ^ (-(5 : ℂ))) *
      (1 / 6 * (6 * Complex.Gamma (5 / 2) * Complex.Gamma (5 / 2)))
  have hA : A = Complex.Gammaℝ (8 : ℂ) * Complex.Gammaℝ (5 : ℂ) ^ 2 *
      Complex.Gammaℝ (2 : ℂ) := by
    dsimp [A]
    convert d4BM_archimedean_two_five using 1
    all_goals norm_num
  calc
    8 * (Complex.Gammaℝ 10 * riemannZeta 10) *
        (2 * (Real.pi : ℂ)) ^ (-(5 : ℂ)) *
          (1 / 6 * (6 * Complex.Gamma (5 / 2) * Complex.Gamma (5 / 2))) *
          (riemannZeta 2 * riemannZeta 5 * riemannZeta 5 * riemannZeta 8 /
            riemannZeta 10) =
        A * riemannZeta 10 *
        (riemannZeta 2 * riemannZeta 5 * riemannZeta 5 * riemannZeta 8 /
          riemannZeta 10) := by dsimp [A]; ring
    _ = A * (riemannZeta 8 * riemannZeta 5 ^ 2 * riemannZeta 2) := by
          field_simp
    _ = (Complex.Gammaℝ (8 : ℂ) * Complex.Gammaℝ (5 : ℂ) ^ 2 *
          Complex.Gammaℝ (2 : ℂ)) *
        (riemannZeta 8 * riemannZeta 5 ^ 2 * riemannZeta 2) := by rw [hA]
    _ = (Complex.Gammaℝ (8 : ℂ) * riemannZeta 8) *
          (Complex.Gammaℝ (5 : ℂ) * riemannZeta 5) ^ 2 *
          (Complex.Gammaℝ (2 : ℂ) * riemannZeta 2) := by ring

private lemma d4BM_gammaR_neg_one_ne_zero : Complex.Gammaℝ (-1 : ℂ) ≠ 0 := by
  rw [Complex.Gammaℝ]
  apply mul_ne_zero
  · rw [Complex.cpow_def_of_ne_zero
      (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)]
    exact Complex.exp_ne_zero _
  · apply Complex.Gamma_ne_zero
    intro m hm
    have hre := congrArg Complex.re hm
    norm_num at hre
    have hnat : 2 * m = 1 := by exact_mod_cast (show (2 : ℝ) * m = 1 by linarith)
    omega

private lemma d4BM_completedRiemannZeta_neg_one_eq :
    completedRiemannZeta (-1 : ℂ) =
      Complex.Gammaℝ (-1 : ℂ) * riemannZeta (-1 : ℂ) := by
  rw [riemannZeta_def_of_ne_zero (by norm_num : (-1 : ℂ) ≠ 0)]
  field_simp [d4BM_gammaR_neg_one_ne_zero]

/-- Functional-equation weld needed to compare the positive-half-plane source with the corpus
classical RSZ normalization. -/
lemma d4BM_reflectedCompletedLambda_neg_one_eq_two :
    reflectedCompletedLambda (-1 : ℂ) = reflectedCompletedLambda (2 : ℂ) := by
  have hneg := xi_eq_mul_completedRiemannZeta
    (s := (-1 : ℂ)) (by norm_num) (by norm_num)
  have hpos := xi_eq_mul_completedRiemannZeta
    (s := (2 : ℂ)) (by norm_num) (by norm_num)
  norm_num at hneg hpos
  have hfe := xi_one_sub (2 : ℂ)
  norm_num at hfe
  rw [reflectedCompletedLambda, reflectedCompletedLambda,
    ← d4BM_completedRiemannZeta_neg_one_eq,
    ← completedRiemannZeta_eq_Gammaℝ_mul_levinsonDetectorFE (by norm_num : 0 < (2 : ℂ).re)]
  rw [← hneg, hfe, hpos]

/-- Projecting Eisenstein parameter `Q = 5`, inside the actual convergence chamber. -/
def d4BMEisensteinAbsoluteConvergenceParameterFive :
    D4BMEisensteinAbsoluteConvergenceParameter :=
  ⟨5, by norm_num⟩

/-- The literal unfolded source agrees with the corpus classical RSZ value at `(2,5)`. -/
theorem d4BM_actualTwoFiveUnfoldedScalarSource_eq_classicalRSZ :
    d4BMActualTwoFiveUnfoldedScalarSource =
      d4BMClassicalCompletedDiagonalRSZValue
        d4BMEisensteinAbsoluteConvergenceParameterTwo
        d4BMEisensteinAbsoluteConvergenceParameterFive := by
  rw [d4BM_actualTwoFiveUnfoldedScalarSource_eq_positiveLambdaProduct]
  simp only [d4BMTwoFivePositiveLambdaProduct,
    d4BMClassicalCompletedDiagonalRSZValue,
    d4BMEisensteinAbsoluteConvergenceParameterTwo,
    d4BMEisensteinAbsoluteConvergenceParameterFive]
  norm_num only
  rw [d4BM_reflectedCompletedLambda_neg_one_eq_two]

private lemma d4BM_completedXiFactor_fifteen_halves_eq :
    thetaCuspHawkingCompletedEisensteinXiFactor (15 / 2 : ℂ) =
      28 * reflectedCompletedLambda 8 := by
  unfold thetaCuspHawkingCompletedEisensteinXiFactor XiC
  have harg : (1 / 2 : ℂ) + (-Complex.I * (15 / 2 : ℂ)) * Complex.I = 8 := by
    apply Complex.ext <;> norm_num
  rw [harg, xi_eq_mul_completedRiemannZeta (by norm_num) (by norm_num),
    completedRiemannZeta_eq_Gammaℝ_mul_levinsonDetectorFE (by norm_num)]
  unfold reflectedCompletedLambda
  ring

private lemma d4BM_completedXiFactor_nine_halves_eq :
    thetaCuspHawkingCompletedEisensteinXiFactor (9 / 2 : ℂ) =
      10 * reflectedCompletedLambda 5 := by
  unfold thetaCuspHawkingCompletedEisensteinXiFactor XiC
  have harg : (1 / 2 : ℂ) + (-Complex.I * (9 / 2 : ℂ)) * Complex.I = 5 := by
    apply Complex.ext <;> norm_num
  rw [harg, xi_eq_mul_completedRiemannZeta (by norm_num) (by norm_num),
    completedRiemannZeta_eq_Gammaℝ_mul_levinsonDetectorFE (by norm_num)]
  unfold reflectedCompletedLambda
  ring

private lemma d4BM_completedXiFactor_neg_three_halves_eq :
    thetaCuspHawkingCompletedEisensteinXiFactor (-3 / 2 : ℂ) =
      reflectedCompletedLambda (-1) := by
  unfold thetaCuspHawkingCompletedEisensteinXiFactor XiC
  have harg : (1 / 2 : ℂ) + (-Complex.I * (-3 / 2 : ℂ)) * Complex.I = -1 := by
    apply Complex.ext <;> norm_num
  rw [harg, xi_eq_mul_completedRiemannZeta (by norm_num) (by norm_num),
    d4BM_completedRiemannZeta_neg_one_eq]
  unfold reflectedCompletedLambda
  ring

/-- Exact canonical-to-literal ratio at `(2,5)`, first expressed against the positive completed-zeta
product. -/
theorem d4BM_canonicalScalarVertex_eq_2800_mul_positiveLambdaProduct :
    d4BMActualCanonicalScalarTripleVertex
        d4BMEisensteinAbsoluteConvergenceParameterTwo
        d4BMEisensteinAbsoluteConvergenceParameterFive =
      2800 * d4BMTwoFivePositiveLambdaProduct := by
  rw [d4BMActualCanonicalScalarTripleVertex,
    thetaCuspHawkingDiagonalCompletedEisensteinCubicVertex_factorization]
  norm_num [d4BMActualCenteredEisensteinParameter,
    d4BMEisensteinAbsoluteConvergenceParameterTwo,
    d4BMEisensteinAbsoluteConvergenceParameterFive]
  have hneg : thetaCuspHawkingCompletedEisensteinXiFactor (-(3 / 2 : ℂ)) =
      reflectedCompletedLambda (-1) := by
    convert d4BM_completedXiFactor_neg_three_halves_eq using 1
    all_goals ring
  rw [d4BM_completedXiFactor_fifteen_halves_eq,
    d4BM_completedXiFactor_nine_halves_eq, hneg]
  rw [d4BM_reflectedCompletedLambda_neg_one_eq_two]
  norm_num [d4BMTwoFivePositiveLambdaProduct]
  ring

/-- **Sharp positive survivor.**  The prescribed canonical vertex is exactly `2800` times the
literal unfolded source at the honest absolute-convergence point `(2,5)`. -/
theorem d4BM_canonicalScalarVertex_eq_2800_mul_actualUnfoldedSource_two_five :
    d4BMActualCanonicalScalarTripleVertex
        d4BMEisensteinAbsoluteConvergenceParameterTwo
        d4BMEisensteinAbsoluteConvergenceParameterFive =
      2800 * d4BMActualTwoFiveUnfoldedScalarSource := by
  rw [d4BM_canonicalScalarVertex_eq_2800_mul_positiveLambdaProduct,
    d4BM_actualTwoFiveUnfoldedScalarSource_eq_positiveLambdaProduct]

/-- The literal unfolded source is nonzero. -/
theorem d4BM_actualTwoFiveUnfoldedScalarSource_ne_zero :
    d4BMActualTwoFiveUnfoldedScalarSource ≠ 0 := by
  rw [d4BM_actualTwoFiveUnfoldedScalarSource_eq_positiveLambdaProduct]
  have hLambda (s : ℂ) (hs : 1 < s.re) : reflectedCompletedLambda s ≠ 0 := by
    unfold reflectedCompletedLambda
    exact mul_ne_zero (Complex.Gammaℝ_ne_zero_of_re_pos (by linarith))
      (riemannZeta_ne_zero_of_one_lt_re hs)
  exact mul_ne_zero
    (mul_ne_zero (hLambda 8 (by norm_num))
      (pow_ne_zero 2 (hLambda 5 (by norm_num))))
    (hLambda 2 (by norm_num))

/-- **Actual scalar-normalization no-go.**  The canonical four-xi vertex is not the literal
nonconstant unfolded source at `(P,Q) = (2,5)`.  Since the point is in the absolute-convergence
chamber, this disproves the unmodified family-level landing before any continuation or
regularization issue arises. -/
theorem d4BM_actualCanonicalScalarVertex_ne_unfoldedSource_two_five :
    d4BMActualCanonicalScalarTripleVertex
        d4BMEisensteinAbsoluteConvergenceParameterTwo
        d4BMEisensteinAbsoluteConvergenceParameterFive ≠
      d4BMActualTwoFiveUnfoldedScalarSource := by
  rw [d4BM_canonicalScalarVertex_eq_2800_mul_actualUnfoldedSource_two_five]
  intro h
  have hzero : d4BMActualTwoFiveUnfoldedScalarSource = 0 := by
    linear_combination (1 / 2799 : ℂ) * h
  exact d4BM_actualTwoFiveUnfoldedScalarSource_ne_zero hzero

/-- Analytic-family regularized scalar value after adjoining an arbitrary diagonal
triple-Eisenstein constant-boundary family to the literal unfolded source.  The coefficient family
is completely unrestricted; this contains every possible choice of the eight Weyl-sector
coefficients. -/
def d4BMTwoFiveAnalyticFamilyRegularizedScalarValue
    (coefficient : Bool → Bool → Bool → ℂ) : ℂ :=
  d4BMActualTwoFiveUnfoldedScalarSource +
    d4BMCuspAnalyticFamilyFinitePart
      (d4BMDiagonalEisensteinCuspBoundaryFamily coefficient)

/-- Universal boundary rigidity: analytic-family finite part kills every allowed constant-boundary
correction, so every source-compatible scalar regularization has exactly the unfolded value. -/
theorem d4BM_twoFiveAnalyticFamilyRegularizedScalarValue_eq_source
    (coefficient : Bool → Bool → Bool → ℂ) :
    d4BMTwoFiveAnalyticFamilyRegularizedScalarValue coefficient =
      d4BMActualTwoFiveUnfoldedScalarSource := by
  rw [d4BMTwoFiveAnalyticFamilyRegularizedScalarValue,
    d4BMCuspAnalyticFamilyFinitePart_diagonalEisensteinBoundary_eq_zero,
    add_zero]

/-- **Exact classification of every allowed analytic-family correction.**  Independently of all
eight constant-boundary coefficients, the canonical vertex is exactly `2800` times the resulting
regularized scalar value. -/
theorem d4BM_canonicalScalarVertex_eq_2800_mul_analyticFamilyRegularizedScalarValue_two_five
    (coefficient : Bool → Bool → Bool → ℂ) :
    d4BMActualCanonicalScalarTripleVertex
        d4BMEisensteinAbsoluteConvergenceParameterTwo
        d4BMEisensteinAbsoluteConvergenceParameterFive =
      2800 * d4BMTwoFiveAnalyticFamilyRegularizedScalarValue coefficient := by
  rw [d4BM_twoFiveAnalyticFamilyRegularizedScalarValue_eq_source]
  exact d4BM_canonicalScalarVertex_eq_2800_mul_actualUnfoldedSource_two_five

/-- Every diagonal analytic-family constant-boundary correction still misses the canonical HB
vertex. -/
theorem d4BM_twoFiveAnalyticFamilyRegularizedScalarValue_ne_canonical
    (coefficient : Bool → Bool → Bool → ℂ) :
    d4BMTwoFiveAnalyticFamilyRegularizedScalarValue coefficient ≠
      d4BMActualCanonicalScalarTripleVertex
        d4BMEisensteinAbsoluteConvergenceParameterTwo
        d4BMEisensteinAbsoluteConvergenceParameterFive := by
  rw [d4BM_twoFiveAnalyticFamilyRegularizedScalarValue_eq_source]
  exact Ne.symm d4BM_actualCanonicalScalarVertex_ne_unfoldedSource_two_five

/-- **Family-level HB route kill.**  No choice of diagonal triple-Eisenstein constant-boundary
coefficients makes the source-compatible analytic-family regularization land on the prescribed
canonical four-xi vertex.  This is a closed negated-existence theorem over the entire allowed
boundary class, not a conditional comparison for one reporter. -/
theorem d4BM_no_diagonalBoundaryFamily_repairs_unfoldedSource_two_five :
    ¬ ∃ coefficient : Bool → Bool → Bool → ℂ,
      d4BMTwoFiveAnalyticFamilyRegularizedScalarValue coefficient =
        d4BMActualCanonicalScalarTripleVertex
          d4BMEisensteinAbsoluteConvergenceParameterTwo
          d4BMEisensteinAbsoluteConvergenceParameterFive := by
  rintro ⟨coefficient, h⟩
  exact d4BM_twoFiveAnalyticFamilyRegularizedScalarValue_ne_canonical coefficient h

/-- **Actual finite-part incompatibility.**  There is no linear reporter on the literal truncated
scalar moments which is simultaneously compatible with any allowed analytic-family unfolded
regularization and lands on the canonical HB vertex.  This closed theorem mentions the actual
truncated scalar moment through `d4BMActualScalarTripleFinitePart`; it rules out the complete pair
of properties required by the surviving scalar-landing route. -/
theorem d4BM_no_actualFinitePart_sourceCompatible_and_canonical_two_five :
    ¬ ∃ finitePart : D4BMActualHeightFinitePart,
      ∃ coefficient : Bool → Bool → Bool → ℂ,
        d4BMActualScalarTripleFinitePart finitePart
            d4BMEisensteinAbsoluteConvergenceParameterTwo
            d4BMEisensteinAbsoluteConvergenceParameterFive =
          d4BMTwoFiveAnalyticFamilyRegularizedScalarValue coefficient ∧
        d4BMActualScalarTripleFinitePart finitePart
            d4BMEisensteinAbsoluteConvergenceParameterTwo
            d4BMEisensteinAbsoluteConvergenceParameterFive =
          d4BMActualCanonicalScalarTripleVertex
            d4BMEisensteinAbsoluteConvergenceParameterTwo
            d4BMEisensteinAbsoluteConvergenceParameterFive := by
  rintro ⟨finitePart, coefficient, hsource, hcanonical⟩
  exact d4BM_twoFiveAnalyticFamilyRegularizedScalarValue_ne_canonical coefficient
    (hsource.symm.trans hcanonical)

end RHTower
