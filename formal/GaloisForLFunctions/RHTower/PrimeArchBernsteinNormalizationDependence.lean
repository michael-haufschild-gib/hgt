import GaloisForLFunctions.RHTower.PrimeArchBernsteinSectorConfinedPhase

/-!
# Normalization dependence of Bernstein susceptibility collars

The exact endpoint normalization is useful because it is supplied by a distinguished completed
source value.  Numerical closeness of a Bernstein-susceptibility radius to one is nevertheless
not invariant under rescaling the moment coordinate.  This file proves that point without any
assumption on RH.

For every uniform reciprocal-square norm bound `M` and every scale `R > 0`, the affine amplitude
of the normalized atom `z/R` is at most `1 + 2M/R`.  The full divisor envelope then bounds the
degree-`n` Bernstein purity by

`(absoluteMass * (1 + 2M/R)^n)^2`.

Taking `R` sufficiently large makes this unconditional exponential ceiling arbitrarily close to
one.  Thus a small open collar is not by itself an invariant measure of progress toward RH; only
an exact, independently distinguished endpoint statement can carry that meaning.
-/

open Complex Filter Topology
open scoped BigOperators Polynomial
open Polynomial

namespace RHTower

noncomputable section

/-- One normalized complex atom has affine Bernstein amplitude at most `1 + 2M/R`. -/
theorem norm_div_add_norm_one_sub_div_le_one_add_two_mul_div
    {z : ℂ} {R M : ℝ} (hR : 0 < R) (hM : ‖z‖ ≤ M) :
    ‖z / (R : ℂ)‖ + ‖1 - z / (R : ℂ)‖ ≤ 1 + 2 * M / R := by
  have hdiv : ‖z / (R : ℂ)‖ ≤ M / R := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR]
    exact div_le_div_of_nonneg_right hM hR.le
  have htriangle : ‖1 - z / (R : ℂ)‖ ≤ 1 + ‖z / (R : ℂ)‖ := by
    simpa using norm_sub_le (1 : ℂ) (z / (R : ℂ))
  nlinarith

/-- Pointwise divisor-envelope bound for a Bernstein coefficient at an arbitrary positive
normalization radius. -/
theorem abs_bernsteinCoefficient_radiusNormalized_le_divisorEnvelope
    (R : ℝ) (n i : ℕ) :
    |bernsteinCoefficient
        (radiusNormalizedMoment R normalizedPrimeArchMoment) n i| ≤
      ∑' q : XiZeroCopy,
        ‖xiZeroCopyReciprocalSquare q‖ *
          ‖evalRealPolynomial (bernsteinPolynomial ℝ n i)
            (xiZeroCopyReciprocalSquare q / (R : ℂ))‖ := by
  let p := bernsteinPolynomial ℝ n i
  have hsumm := summable_xiCentralRadiusNormalizedPolynomialTerm R p
  rw [← Real.norm_eq_abs, ← Complex.norm_real,
    bernsteinCoefficient,
    ← xiCentralRadiusNormalizedPolynomialMoment_eq_source,
    xiCentralRadiusNormalizedPolynomialMoment_eq_tsum]
  refine (norm_tsum_le_tsum_norm hsumm.norm).trans_eq ?_
  apply tsum_congr
  intro q
  rw [norm_mul]
  rfl

/-- The complete radius-normalized Bernstein vector inherits the scale-dependent affine
amplitude ceiling. -/
theorem bernsteinCoefficientL1_radiusNormalized_le_largeScale
    {R M : ℝ} (hR : 0 < R) (hM0 : 0 ≤ M)
    (hM : ∀ q : XiZeroCopy, ‖xiZeroCopyReciprocalSquare q‖ ≤ M)
    (n : ℕ) :
    bernsteinCoefficientL1
        (radiusNormalizedMoment R normalizedPrimeArchMoment) n ≤
      xiReciprocalSquareAbsoluteMass * (1 + 2 * M / R) ^ n := by
  rw [bernsteinCoefficientL1]
  calc
    (∑ i ∈ Finset.range (n + 1),
        |bernsteinCoefficient
          (radiusNormalizedMoment R normalizedPrimeArchMoment) n i|) ≤
      ∑ i ∈ Finset.range (n + 1),
        ∑' q : XiZeroCopy,
          ‖xiZeroCopyReciprocalSquare q‖ *
            ‖evalRealPolynomial (bernsteinPolynomial ℝ n i)
              (xiZeroCopyReciprocalSquare q / (R : ℂ))‖ := by
        exact Finset.sum_le_sum fun i _ =>
          abs_bernsteinCoefficient_radiusNormalized_le_divisorEnvelope R n i
    _ = ∑' q : XiZeroCopy,
        ∑ i ∈ Finset.range (n + 1),
          (‖xiZeroCopyReciprocalSquare q‖ *
            ‖evalRealPolynomial (bernsteinPolynomial ℝ n i)
              (xiZeroCopyReciprocalSquare q / (R : ℂ))‖) := by
        rw [Summable.tsum_finsetSum]
        intro i hi
        simpa only [norm_mul, Real.norm_eq_abs, abs_norm] using
          (summable_xiCentralRadiusNormalizedPolynomialTerm
            R (bernsteinPolynomial ℝ n i)).norm
    _ = ∑' q : XiZeroCopy,
        ‖xiZeroCopyReciprocalSquare q‖ *
          (‖xiZeroCopyReciprocalSquare q / (R : ℂ)‖ +
            ‖1 - xiZeroCopyReciprocalSquare q / (R : ℂ)‖) ^ n := by
        apply tsum_congr
        intro q
        rw [← Finset.mul_sum,
          sum_norm_evalRealPolynomial_bernsteinPolynomial]
    _ ≤ ∑' q : XiZeroCopy,
        ‖xiZeroCopyReciprocalSquare q‖ * (1 + 2 * M / R) ^ n := by
        have hbase : 0 ≤ 1 + 2 * M / R := by positivity
        apply Summable.tsum_le_tsum
        · intro q
          exact mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀
              (add_nonneg (norm_nonneg _) (norm_nonneg _))
              (norm_div_add_norm_one_sub_div_le_one_add_two_mul_div hR (hM q)) n)
            (norm_nonneg _)
        · exact Summable.of_nonneg_of_le
            (fun q => mul_nonneg (norm_nonneg _)
              (pow_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _)) n))
            (fun q => mul_le_mul_of_nonneg_left
              (pow_le_pow_left₀
                (add_nonneg (norm_nonneg _) (norm_nonneg _))
                (norm_div_add_norm_one_sub_div_le_one_add_two_mul_div hR (hM q)) n)
              (norm_nonneg _))
            (summable_xiZeroCopyReciprocalSquare.norm.mul_right
              ((1 + 2 * M / R) ^ n))
        · exact summable_xiZeroCopyReciprocalSquare.norm.mul_right
            ((1 + 2 * M / R) ^ n)
    _ = xiReciprocalSquareAbsoluteMass * (1 + 2 * M / R) ^ n := by
      rw [xiReciprocalSquareAbsoluteMass, tsum_mul_right]

/-- The squared `l2` packet purity obeys the corresponding scale-dependent bound. -/
theorem bernsteinCoefficientPurity_radiusNormalized_le_largeScale
    {R M : ℝ} (hR : 0 < R) (hM0 : 0 ≤ M)
    (hM : ∀ q : XiZeroCopy, ‖xiZeroCopyReciprocalSquare q‖ ≤ M)
    (n : ℕ) :
    bernsteinCoefficientPurity
        (radiusNormalizedMoment R normalizedPrimeArchMoment) n ≤
      (xiReciprocalSquareAbsoluteMass * (1 + 2 * M / R) ^ n) ^ 2 := by
  exact (bernsteinCoefficientPurity_le_l1_sq _ _).trans
    ((sq_le_sq₀
      (Finset.sum_nonneg fun _ _ => abs_nonneg _)
      (mul_nonneg xiReciprocalSquareAbsoluteMass_nonneg
        (pow_nonneg (by positivity) n))).2
      (bernsteinCoefficientL1_radiusNormalized_le_largeScale hR hM0 hM n))

/-- Any prescribed positive excess over the neutral amplitude can be reached by enlarging the
normalization scale. -/
theorem exists_largeScale_affineAmplitude_lt
    {M ε : ℝ} (hM : 0 ≤ M) (hε : 0 < ε) :
    ∃ R : ℝ, 0 < R ∧ 1 + 2 * M / R < 1 + ε := by
  let R : ℝ := 2 * M / ε + 1
  have hR : 0 < R := by
    dsimp only [R]
    positivity
  have hcore : 2 * M < ε * R := by
    have heq : ε * R = 2 * M + ε := by
      dsimp only [R]
      field_simp [hε.ne']
      ring
    linarith
  refine ⟨R, hR, ?_⟩
  have hdiv : 2 * M / R < ε := (div_lt_iff₀ hR).2 hcore
  linarith

/-- **Arbitrarily narrow unconditional normalization collar.**  For every positive `ε`, one
can choose a normalization radius for which the complete Xi Bernstein purity has exponential
ceiling `(1+ε)^(2n)`, independently of RH. -/
theorem exists_radius_bernsteinCoefficientPurity_le_arbitrarilyNarrow
    {M ε : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ q : XiZeroCopy, ‖xiZeroCopyReciprocalSquare q‖ ≤ M)
    (hε : 0 < ε) :
    ∃ R : ℝ, 0 < R ∧ ∀ n : ℕ,
      bernsteinCoefficientPurity
          (radiusNormalizedMoment R normalizedPrimeArchMoment) n ≤
        (xiReciprocalSquareAbsoluteMass * (1 + ε) ^ n) ^ 2 := by
  obtain ⟨R, hR, hbase⟩ := exists_largeScale_affineAmplitude_lt hM0 hε
  refine ⟨R, hR, fun n => ?_⟩
  have hraw :=
    bernsteinCoefficientPurity_radiusNormalized_le_largeScale hR hM0 hM n
  have hpow : (1 + 2 * M / R) ^ n ≤ (1 + ε) ^ n := by
    exact pow_le_pow_left₀ (by positivity) hbase.le n
  exact hraw.trans ((sq_le_sq₀
    (mul_nonneg xiReciprocalSquareAbsoluteMass_nonneg (pow_nonneg (by positivity) n))
    (mul_nonneg xiReciprocalSquareAbsoluteMass_nonneg (pow_nonneg (by positivity) n))).2
    (mul_le_mul_of_nonneg_left hpow xiReciprocalSquareAbsoluteMass_nonneg))

end

end RHTower
