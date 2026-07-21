import GaloisForLFunctions.RHTower.SoninCoupledProjectiveFeshbachEquivalence
import GaloisForLFunctions.RHTower.PrimeArchShiftThirteenCircleCone
import GaloisForLFunctions.RHTower.XiSquaredEulerAllDegreeChargeCriterion

/-!
# Centered analytic-tail vacuum cone

The vacuum-Feshbach reduction leaves one target-normalized variance for each zero-constant
integer polynomial tail.  This module discharges an explicit part of that right-edge interface.

The endpoint disk makes every nonconstant polynomial tail small at every reciprocal-square Xi
atom.  If its coefficient `l1` mass is at most eight times the centered vacuum amplitude, the
sector law then makes every multiplicity-copy trace-Hankel summand nonnegative.  Summation gives
target variance positivity without a Sonin comparison.  Consequently the coupled-Sonin
normalized-variance hypothesis is required only on the strict complementary coefficient family.
-/

open Complex Polynomial Filter Topology
open scoped BigOperators

namespace RHTower

noncomputable section

/-- `l1` mass of all nonconstant coefficients, indexed without support bookkeeping. -/
def polynomialNonconstantCoeffL1 (p : Polynomial ℝ) : ℝ :=
  ∑ k ∈ Finset.range p.natDegree, |p.coeff (k + 1)|

/-- Split real-polynomial evaluation into the vacuum coefficient and its nonconstant tail. -/
theorem evalRealPolynomial_eq_coeff_zero_add_tail (p : Polynomial ℝ) (z : ℂ) :
    evalRealPolynomial p z =
      (p.coeff 0 : ℂ) +
        ∑ k ∈ Finset.range p.natDegree, (p.coeff (k + 1) : ℂ) * z ^ (k + 1) := by
  rw [evalRealPolynomial, Polynomial.eval_eq_sum_range]
  simp only [Polynomial.natDegree_map_eq_of_injective
      (f := algebraMap ℝ ℂ) Complex.ofReal_injective,
    Polynomial.coeff_map, coe_algebraMap]
  rw [Finset.sum_range_succ']
  simp only [pow_zero, mul_one]
  abel

/-- Inside the unit disk, a zero-constant polynomial is bounded by radius times coefficient
`l1` mass. -/
theorem norm_evalRealPolynomial_le_norm_mul_nonconstantCoeffL1_of_coeff_zero
    (p : Polynomial ℝ) (z : ℂ) (hp : p.coeff 0 = 0) (hz : ‖z‖ ≤ 1) :
    ‖evalRealPolynomial p z‖ ≤ ‖z‖ * polynomialNonconstantCoeffL1 p := by
  rw [evalRealPolynomial_eq_coeff_zero_add_tail, hp]
  simp only [Complex.ofReal_zero, zero_add]
  calc
    ‖∑ k ∈ Finset.range p.natDegree,
        (p.coeff (k + 1) : ℂ) * z ^ (k + 1)‖ ≤
        ∑ k ∈ Finset.range p.natDegree,
          ‖(p.coeff (k + 1) : ℂ) * z ^ (k + 1)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ k ∈ Finset.range p.natDegree,
          ‖z‖ * |p.coeff (k + 1)| := by
      apply Finset.sum_le_sum
      intro k hk
      rw [norm_mul, norm_pow, Complex.norm_real]
      have hpow : ‖z‖ ^ (k + 1) ≤ ‖z‖ ^ 1 :=
        pow_le_pow_of_le_one (norm_nonneg z) hz (by omega)
      simpa [mul_comm] using
        mul_le_mul_of_nonneg_left hpow (abs_nonneg (p.coeff (k + 1)))
    _ = ‖z‖ * polynomialNonconstantCoeffL1 p := by
      rw [polynomialNonconstantCoeffL1, Finset.mul_sum]

/-- The squared reciprocal-sector estimate implies a linear norm/real-mass estimate. -/
theorem norm_xiZeroCopyReciprocalSquare_le_eightyFive_div_eightyFour_mul_re
    (q : XiZeroCopy) :
    ‖xiZeroCopyReciprocalSquare q‖ ≤
      (85 / 84 : ℝ) * (xiZeroCopyReciprocalSquare q).re := by
  let z := xiZeroCopyReciprocalSquare q
  have hre : 0 < z.re := xiZeroCopyReciprocalSquare_re_pos q
  have hratio := xiZeroCopyReciprocalSquare_normSq_div_re_le q
  have hsq : ‖z‖ ^ 2 ≤ (85 / 84 : ℝ) * z.re ^ 2 := by
    have h := (div_le_iff₀ hre).mp hratio
    rw [Complex.sq_norm]
    change Complex.normSq z ≤ (85 / 84 : ℝ) * z.re ^ 2
    change Complex.normSq z ≤ (85 / 84 : ℝ) * z.re * z.re at h
    nlinarith
  have hsq' : ‖z‖ ^ 2 ≤ ((85 / 84 : ℝ) * z.re) ^ 2 := by
    calc
      ‖z‖ ^ 2 ≤ (85 / 84 : ℝ) * z.re ^ 2 := hsq
      _ ≤ ((85 / 84 : ℝ) * z.re) ^ 2 := by
        nlinarith [sq_nonneg z.re]
  exact (sq_le_sq₀ (norm_nonneg z) (by positivity)).mp hsq'

/-- **Atomwise centered analytic-tail law.**  The endpoint radius and reciprocal sector make each
multiplicity-copy trace-Hankel term nonnegative throughout the coefficient cone. -/
theorem xiCenteredAnalyticTailHankelTerm_nonneg
    (p : Polynomial ℝ) (hp : p.coeff 0 = 0) (μ : ℝ)
    (htail : polynomialNonconstantCoeffL1 p ≤ 8 * |μ|)
    (q : XiZeroCopy) :
    0 ≤ xiSquaredEulerApertureHankelTerm (p - C μ) q := by
  let z := xiZeroCopyReciprocalSquare q
  let w := evalRealPolynomial p z
  have hzrad : ‖z‖ < (2 / 41 : ℝ) := by
    simpa only [z] using norm_xiZeroCopyReciprocalSquare_lt_two_over_fortyOne q
  have hzone : ‖z‖ ≤ 1 := by linarith [norm_nonneg z]
  have hw0 : ‖w‖ ≤ ‖z‖ * polynomialNonconstantCoeffL1 p := by
    simpa only [w] using
      norm_evalRealPolynomial_le_norm_mul_nonconstantCoeffL1_of_coeff_zero p z hp hzone
  have hw : ‖w‖ ≤ (16 / 41 : ℝ) * |μ| := by
    have htail0 : 0 ≤ polynomialNonconstantCoeffL1 p := by
      exact Finset.sum_nonneg fun _ _ => abs_nonneg _
    calc
      ‖w‖ ≤ ‖z‖ * polynomialNonconstantCoeffL1 p := hw0
      _ ≤ (2 / 41 : ℝ) * (8 * |μ|) := by
        gcongr
      _ = (16 / 41 : ℝ) * |μ| := by ring
  have hzre : ‖z‖ ≤ (85 / 84 : ℝ) * z.re := by
    simpa only [z] using
      norm_xiZeroCopyReciprocalSquare_le_eightyFive_div_eightyFour_mul_re q
  have hre : 0 < z.re := by
    simpa only [z] using xiZeroCopyReciprocalSquare_re_pos q
  have hperturbNorm :
      ‖z * ((-2 * μ : ℂ) * w + w ^ 2)‖ ≤ z.re * μ ^ 2 := by
    calc
      ‖z * ((-2 * μ : ℂ) * w + w ^ 2)‖ =
          ‖z‖ * ‖(-2 * μ : ℂ) * w + w ^ 2‖ := by rw [norm_mul]
      _ ≤ ‖z‖ * (2 * |μ| * ‖w‖ + ‖w‖ ^ 2) := by
        gcongr
        calc
          ‖(-2 * μ : ℂ) * w + w ^ 2‖ ≤
              ‖(-2 * μ : ℂ) * w‖ + ‖w ^ 2‖ := norm_add_le _ _
          _ = 2 * |μ| * ‖w‖ + ‖w‖ ^ 2 := by
            rw [norm_mul, norm_pow]
            have hnorm : ‖(-2 * μ : ℂ)‖ = 2 * |μ| := by
              rw [show (-2 * μ : ℂ) = ((-2 * μ : ℝ) : ℂ) by push_cast; ring,
                Complex.norm_real, Real.norm_eq_abs, abs_mul]
              simp
            rw [hnorm]
      _ ≤ ((85 / 84 : ℝ) * z.re) *
          (2 * |μ| * ((16 / 41 : ℝ) * |μ|) +
            ((16 / 41 : ℝ) * |μ|) ^ 2) := by
        gcongr
      _ ≤ z.re * μ ^ 2 := by
        have hcoef :
            (85 / 84 : ℝ) * (2 * (16 / 41 : ℝ) + (16 / 41 : ℝ) ^ 2) ≤ 1 := by
          norm_num
        calc
          (85 / 84 : ℝ) * z.re *
              (2 * |μ| * ((16 / 41 : ℝ) * |μ|) +
                ((16 / 41 : ℝ) * |μ|) ^ 2) =
              z.re * ((85 / 84 : ℝ) *
                (2 * (16 / 41 : ℝ) + (16 / 41 : ℝ) ^ 2)) * |μ| ^ 2 := by ring
          _ ≤ z.re * 1 * |μ| ^ 2 := by gcongr
          _ = z.re * μ ^ 2 := by rw [sq_abs]; ring
  unfold xiSquaredEulerApertureHankelTerm
  change 0 ≤ (z * evalRealPolynomial (p - C μ) z ^ 2).re
  have heval : evalRealPolynomial (p - C μ) z = w - (μ : ℂ) := by
    simp [evalRealPolynomial, w]
  rw [heval]
  have hsplit :
      (z * (w - (μ : ℂ)) ^ 2).re =
        z.re * μ ^ 2 + (z * ((-2 * μ : ℂ) * w + w ^ 2)).re := by
    simp [pow_two, mul_re, mul_im]
    ring
  rw [hsplit]
  have hreal :
      -(z.re * μ ^ 2) ≤ (z * ((-2 * μ : ℂ) * w + w ^ 2)).re := by
    calc
      -(z.re * μ ^ 2) ≤ -‖z * ((-2 * μ : ℂ) * w + w ^ 2)‖ := by
        exact neg_le_neg hperturbNorm
      _ ≤ (z * ((-2 * μ : ℂ) * w + w ^ 2)).re := by
        have habs := Complex.abs_re_le_norm
          (z * ((-2 * μ : ℂ) * w + w ^ 2))
        have hneg := neg_abs_le
          (z * ((-2 * μ : ℂ) * w + w ^ 2)).re
        linarith
  linarith

/-- Atomwise analytic-tail control sums to a nonnegative completed prime--Gamma Hankel value. -/
theorem re_primeArchSourceTraceHankel_sub_C_nonneg_of_tailL1
    (p : Polynomial ℝ) (hp : p.coeff 0 = 0) (μ : ℝ)
    (htail : polynomialNonconstantCoeffL1 p ≤ 8 * |μ|) :
    0 ≤ (primeArchSourceTraceHankel (p - C μ)).re := by
  have hsum :
      0 ≤ xiSquaredEulerApertureHankelValue (p - C μ) :=
    tsum_nonneg (xiCenteredAnalyticTailHankelTerm_nonneg p hp μ htail)
  rw [xiSquaredEulerApertureHankelValue_eq_traceHankel_re,
    xiCentralTraceHankel_eq_primeArchSourceTraceHankel] at hsum
  exact hsum

/-- Uncentered formulation: a polynomial is nonnegative whenever the `l1` mass of its vacuum tail
is at most eight times its constant amplitude. -/
theorem re_primeArchSourceTraceHankel_nonneg_of_vacuumTailL1
    (p : Polynomial ℝ)
    (htail : polynomialNonconstantCoeffL1 (HTGeometry.polynomialVacuumTail p) ≤
      8 * |p.coeff 0|) :
    0 ≤ (primeArchSourceTraceHankel p).re := by
  let q := HTGeometry.polynomialVacuumTail p
  have h := re_primeArchSourceTraceHankel_sub_C_nonneg_of_tailL1 q
    (HTGeometry.polynomialVacuumTail_coeff_zero p) (-p.coeff 0) (by simpa only [abs_neg] using htail)
  have hsplit := HTGeometry.C_coeff_zero_add_polynomialVacuumTail p
  change 0 ≤ (primeArchSourceTraceHankel (q - C (-p.coeff 0))).re at h
  have hpoly : q - C (-p.coeff 0) = p := by
    calc
      q - C (-p.coeff 0) = q + C (p.coeff 0) := by simp
      _ = C (p.coeff 0) + q := add_comm _ _
      _ = p := hsplit
  rw [hpoly] at h
  exact h

/-- The target-normalized mean used by the centered coefficient cone. -/
def primeArchNormalizedPolynomialMean (p : Polynomial ℝ) : ℝ :=
  HTGeometry.momentNormalizedExpectation normalizedPrimeArchMoment p

/-- Target centering preserves the atomwise analytic-tail cone. -/
theorem re_primeArchSourceTraceHankel_vacuumCentered_nonneg_of_tailL1
    (p : Polynomial ℝ) (hp : p.coeff 0 = 0)
    (htail : polynomialNonconstantCoeffL1 p ≤
      8 * |primeArchNormalizedPolynomialMean p|) :
    0 ≤ (primeArchSourceTraceHankel
      (HTGeometry.momentVacuumCenteredPolynomial normalizedPrimeArchMoment p)).re := by
  have h := re_primeArchSourceTraceHankel_sub_C_nonneg_of_tailL1 p hp
    (primeArchNormalizedPolynomialMean p) htail
  simpa only [HTGeometry.momentVacuumCenteredPolynomial,
    primeArchNormalizedPolynomialMean, HTGeometry.momentNormalizedExpectation] using h

/-- The centered analytic-tail cone unconditionally has nonnegative target variance. -/
theorem primeArchNormalizedVariance_nonneg_of_centeredTailL1
    (q : Polynomial ℤ) (hq : q.coeff 0 = 0)
    (htail : polynomialNonconstantCoeffL1 (q.map (Int.castRingHom ℝ)) ≤
      8 * |primeArchNormalizedPolynomialMean (q.map (Int.castRingHom ℝ))|) :
    0 ≤ HTGeometry.momentNormalizedVariance normalizedPrimeArchMoment
      (q.map (Int.castRingHom ℝ)) := by
  apply (HTGeometry.momentNormalizedVariance_nonneg_iff_feshbach
    normalizedPrimeArchMoment normalizedPrimeArchMoment_zero_pos _).2
  rw [← re_primeArchSourceTraceHankel_vacuumCentered_eq_feshbach]
  exact re_primeArchSourceTraceHankel_vacuumCentered_nonneg_of_tailL1
    (q.map (Int.castRingHom ℝ)) (by simpa using congrArg (Int.castRingHom ℝ) hq) htail

/-- Strict complement of the centered analytic-tail cone. -/
def PrimeArchCenteredAnalyticTailResidual (q : Polynomial ℤ) : Prop :=
  8 * |primeArchNormalizedPolynomialMean (q.map (Int.castRingHom ℝ))| <
    polynomialNonconstantCoeffL1 (q.map (Int.castRingHom ℝ))

/-- **Counterexample localization.**  Any failure of RH has a negative target-normalized variance
witness in the strict complement of the centered analytic-tail cone.  Thus no possible
counterexample can be detected by a zero-constant integer tail inside the discharged cone. -/
theorem exists_centeredAnalyticTailResidual_negativeVariance_of_not_riemannHypothesis
    (hRH : ¬ RiemannHypothesis) :
    ∃ q : Polynomial ℤ,
      q.coeff 0 = 0 ∧
        PrimeArchCenteredAnalyticTailResidual q ∧
          HTGeometry.momentNormalizedVariance normalizedPrimeArchMoment
              (q.map (Int.castRingHom ℝ)) < 0 := by
  have hnot : ¬ PrimeArchVacuumFeshbachIntNonnegative := by
    intro h
    exact hRH (primeArchVacuumFeshbachIntNonnegative_iff_riemannHypothesis.mp h)
  simp only [PrimeArchVacuumFeshbachIntNonnegative] at hnot
  push Not at hnot
  obtain ⟨q, hq, hrem⟩ := hnot
  let p : Polynomial ℝ := q.map (Int.castRingHom ℝ)
  let targetVar : ℝ :=
    HTGeometry.momentNormalizedVariance normalizedPrimeArchMoment p
  have hvar : targetVar < 0 := by
    have heq := HTGeometry.momentVacuumFeshbachRemainder_eq_mass_mul_normalizedVariance
      normalizedPrimeArchMoment normalizedPrimeArchMoment_zero_pos.ne' p
    change HTGeometry.momentVacuumFeshbachRemainder normalizedPrimeArchMoment p < 0 at hrem
    change HTGeometry.momentVacuumFeshbachRemainder normalizedPrimeArchMoment p =
      normalizedPrimeArchMoment 0 * targetVar at heq
    rw [heq] at hrem
    nlinarith [normalizedPrimeArchMoment_zero_pos]
  have hres : PrimeArchCenteredAnalyticTailResidual q := by
    unfold PrimeArchCenteredAnalyticTailResidual
    by_contra hcone
    have htail : polynomialNonconstantCoeffL1 p ≤
        8 * |primeArchNormalizedPolynomialMean p| := by
      exact le_of_not_gt hcone
    have hnonneg := primeArchNormalizedVariance_nonneg_of_centeredTailL1 q hq htail
    change 0 ≤ targetVar at hnonneg
    linarith
  exact ⟨q, hq, hres, hvar⟩

/-- Rightmost Sonin comparison restricted to tails not already discharged by the centered cone. -/
def SoninCoupledPrimeArchCenteredResidualNormalizedVarianceUpperBound : Prop :=
  ∀ (q : Polynomial ℤ), q.coeff 0 = 0 →
    PrimeArchCenteredAnalyticTailResidual q →
    ∀ ε : ℝ, 0 < ε →
      ∃ a : SoninCoupledNondegenerateAperture,
        normalizedPrimeArchMoment 0 *
            HTGeometry.momentNormalizedVariance
              (soninAllPrimeCoupledRealTraceMoment a.1)
              (q.map (Int.castRingHom ℝ)) ≤
          normalizedPrimeArchMoment 0 *
              HTGeometry.momentNormalizedVariance normalizedPrimeArchMoment
                (q.map (Int.castRingHom ℝ)) + ε

/-- Restricted comparison plus the unconditional centered cone restores every target vacuum
Feshbach inequality. -/
theorem primeArchVacuumFeshbachIntNonnegative_of_centeredResidualNormalizedVariance
    (h : SoninCoupledPrimeArchCenteredResidualNormalizedVarianceUpperBound) :
    PrimeArchVacuumFeshbachIntNonnegative := by
  intro q hq
  let p : Polynomial ℝ := q.map (Int.castRingHom ℝ)
  let targetVar : ℝ :=
    HTGeometry.momentNormalizedVariance normalizedPrimeArchMoment p
  by_cases hcone : polynomialNonconstantCoeffL1 p ≤
      8 * |primeArchNormalizedPolynomialMean p|
  · apply (HTGeometry.momentNormalizedVariance_nonneg_iff_feshbach
      normalizedPrimeArchMoment normalizedPrimeArchMoment_zero_pos p).1
    exact primeArchNormalizedVariance_nonneg_of_centeredTailL1 q hq hcone
  · have hres : PrimeArchCenteredAnalyticTailResidual q := by
      exact lt_of_not_ge hcone
    by_contra htarget
    have htargetRemNeg :
        HTGeometry.momentVacuumFeshbachRemainder normalizedPrimeArchMoment p < 0 :=
      lt_of_not_ge htarget
    have htargetVarNeg : targetVar < 0 := by
      have heq := HTGeometry.momentVacuumFeshbachRemainder_eq_mass_mul_normalizedVariance
        normalizedPrimeArchMoment normalizedPrimeArchMoment_zero_pos.ne' p
      dsimp only [targetVar]
      rw [heq] at htargetRemNeg
      nlinarith [normalizedPrimeArchMoment_zero_pos]
    let ε : ℝ := -(normalizedPrimeArchMoment 0 * targetVar) / 2
    have hε : 0 < ε := by
      dsimp only [ε]
      have hprod :=
        mul_neg_of_pos_of_neg normalizedPrimeArchMoment_zero_pos htargetVarNeg
      linarith
    obtain ⟨a, ha⟩ := h q hq hres ε hε
    have hsourceVar :
        0 ≤ HTGeometry.momentNormalizedVariance
          (soninAllPrimeCoupledRealTraceMoment a.1) p := by
      apply (HTGeometry.momentNormalizedVariance_nonneg_iff_feshbach
        (soninAllPrimeCoupledRealTraceMoment a.1)
        (soninAllPrimeCoupledRealTraceMoment_zero_pos a) p).2
      exact soninAllPrimeCoupledSourceFeshbach_nonneg a p
    have hleft : 0 ≤ normalizedPrimeArchMoment 0 *
        HTGeometry.momentNormalizedVariance
          (soninAllPrimeCoupledRealTraceMoment a.1) p :=
      mul_nonneg normalizedPrimeArchMoment_zero_pos.le hsourceVar
    have hright : normalizedPrimeArchMoment 0 * targetVar + ε < 0 := by
      dsimp only [ε]
      linarith [mul_neg_of_pos_of_neg normalizedPrimeArchMoment_zero_pos htargetVarNeg]
    change normalizedPrimeArchMoment 0 *
        HTGeometry.momentNormalizedVariance
          (soninAllPrimeCoupledRealTraceMoment a.1) p ≤
      normalizedPrimeArchMoment 0 * targetVar + ε at ha
    linarith

/-- **Restricted centered-residual Sonin chain to RH.**  No source comparison is needed inside
the centered analytic-tail cone. -/
theorem riemannHypothesis_of_soninCoupledPrimeArchCenteredResidualNormalizedVarianceUpperBound
    (h : SoninCoupledPrimeArchCenteredResidualNormalizedVarianceUpperBound) :
    RiemannHypothesis :=
  primeArchVacuumFeshbachIntNonnegative_iff_riemannHypothesis.mp
    (primeArchVacuumFeshbachIntNonnegative_of_centeredResidualNormalizedVariance h)

end

end RHTower
