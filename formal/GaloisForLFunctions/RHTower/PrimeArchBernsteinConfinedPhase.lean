import GaloisForLFunctions.RHTower.PrimeArchBernsteinLoschmidtPurity
import GaloisForLFunctions.RHTower.PrimeArchScaledHausdorffDivisorValueRelation

/-!
# Confined exponential phase of the prime--archimedean Bernstein source

The completed endpoint curvature confines every off-line reciprocal-square atom to a disk whose
radius is strictly less than one quarter after Hausdorff normalization.  Consequently the complete
Bernstein coefficient vector has a universal exponential amplitude base strictly below `3 / 2`.
This is an unconditional quantitative estimate on the RH-bearing Loschmidt purity.
-/

open Complex Filter Topology
open scoped BigOperators Polynomial
open Polynomial

namespace RHTower

noncomputable section

/-- Normalized radius of the unconditional off-line reciprocal-square disk. -/
def xiOffLineNormalizedBernsteinRadius : ℝ :=
  (1 - xiEndpointCompletedCurvature) / (4 - xiEndpointCompletedCurvature)

/-- Universal affine Bernstein amplitude base supplied by the off-line curvature disk. -/
def xiUniversalBernsteinAmplitudeBase : ℝ :=
  1 + 2 * xiOffLineNormalizedBernsteinRadius

theorem xiOffLineNormalizedBernsteinRadius_pos :
    0 < xiOffLineNormalizedBernsteinRadius := by
  exact div_pos (sub_pos.mpr xiEndpointCompletedCurvature_lt_one)
    (by nlinarith [xiEndpointCompletedCurvature_lt_one])

theorem xiOffLineNormalizedBernsteinRadius_lt_one_fourth :
    xiOffLineNormalizedBernsteinRadius < 1 / 4 := by
  let C := xiEndpointCompletedCurvature
  have hC : 0 < C := xiEndpointCompletedCurvature_pos
  have hC4 : 0 < 4 - C := by nlinarith [xiEndpointCompletedCurvature_lt_one]
  dsimp only [xiOffLineNormalizedBernsteinRadius]
  rw [div_lt_iff₀ hC4]
  nlinarith

theorem one_lt_xiUniversalBernsteinAmplitudeBase :
    1 < xiUniversalBernsteinAmplitudeBase := by
  dsimp only [xiUniversalBernsteinAmplitudeBase]
  nlinarith [xiOffLineNormalizedBernsteinRadius_pos]

theorem xiUniversalBernsteinAmplitudeBase_lt_three_halves :
    xiUniversalBernsteinAmplitudeBase < 3 / 2 := by
  dsimp only [xiUniversalBernsteinAmplitudeBase]
  nlinarith [xiOffLineNormalizedBernsteinRadius_lt_one_fourth]

theorem xiUniversalBernsteinAmplitudeBase_sq_lt_nine_fourths :
    xiUniversalBernsteinAmplitudeBase ^ 2 < 9 / 4 := by
  calc
    xiUniversalBernsteinAmplitudeBase ^ 2 < (3 / 2 : ℝ) ^ 2 :=
      pow_lt_pow_left₀ xiUniversalBernsteinAmplitudeBase_lt_three_halves
        (zero_le_one.trans one_lt_xiUniversalBernsteinAmplitudeBase.le) (by norm_num)
    _ = 9 / 4 := by norm_num

/-- Reciprocal-square divisor coordinate normalized by the endpoint Hausdorff radius. -/
def xiEndpointNormalizedReciprocalSquare (q : XiZeroCopy) : ℂ :=
  xiZeroCopyReciprocalSquare q / (primeArchEndpointHausdorffRadius : ℂ)

/-- Elliptic affine base controlling the total Bernstein mass of one divisor atom. -/
def xiEndpointBernsteinAtomAmplitudeBase (q : XiZeroCopy) : ℝ :=
  ‖xiEndpointNormalizedReciprocalSquare q‖ +
    ‖1 - xiEndpointNormalizedReciprocalSquare q‖

/-- Every off-line normalized atom lies in the strict quarter disk. -/
theorem norm_xiEndpointNormalizedReciprocalSquare_le_offLineRadius
    (q : XiZeroCopy) (hoff : (q.1 : ℂ).re ≠ 1 / 2) :
    ‖xiEndpointNormalizedReciprocalSquare q‖ ≤
      xiOffLineNormalizedBernsteinRadius := by
  let C := xiEndpointCompletedCurvature
  have hR : 0 < primeArchEndpointHausdorffRadius :=
    primeArchEndpointHausdorffRadius_pos
  have hnorm := xiZeroCopyReciprocalSquare_norm_le_offLineEndpointRadius q hoff
  rw [xiEndpointNormalizedReciprocalSquare, norm_div, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hR]
  calc
    ‖xiZeroCopyReciprocalSquare q‖ / primeArchEndpointHausdorffRadius ≤
        (C / (4 - C)) / primeArchEndpointHausdorffRadius :=
      div_le_div_of_nonneg_right hnorm hR.le
    _ = xiOffLineNormalizedBernsteinRadius := by
      change (C / (4 - C)) / (C / (1 - C)) = (1 - C) / (4 - C)
      have hC : C ≠ 0 := xiEndpointCompletedCurvature_pos.ne'
      have hC1 : 1 - C ≠ 0 :=
        (sub_pos.mpr xiEndpointCompletedCurvature_lt_one).ne'
      have hC4 : 4 - C ≠ 0 :=
        (by nlinarith [xiEndpointCompletedCurvature_lt_one] : 0 < 4 - C).ne'
      apply (div_eq_iff (div_ne_zero hC hC1)).2
      field_simp [hC, hC1, hC4]

/-- A critical-line atom has neutral affine amplitude base exactly one. -/
theorem xiEndpointBernsteinAtomAmplitudeBase_eq_one_of_onLine
    (q : XiZeroCopy) (hline : (q.1 : ℂ).re = 1 / 2) :
    xiEndpointBernsteinAtomAmplitudeBase q = 1 := by
  let z := xiZeroCopyReciprocalSquare q
  let R := primeArchEndpointHausdorffRadius
  have hR : 0 < R := primeArchEndpointHausdorffRadius_pos
  have him : z.im = 0 := by
    rw [show z = xiCentralReciprocalSquare (q.1 : ℂ) by
      exact xiZeroCopyReciprocalSquare_eq q]
    exact (xiCentralReciprocalSquare_im_eq_zero_iff q.1).2 hline
  have hz : z = ((xiThermalNode q : ℝ) : ℂ) := by
    apply Complex.ext
    · rfl
    · simpa only [Complex.ofReal_im] using him
  let x : ℝ := xiThermalNode q / R
  have hx0 : 0 ≤ x := div_nonneg (xiThermalNode_pos q).le hR.le
  have hx1 : x ≤ 1 := by
    rw [div_le_one hR]
    exact xiThermalNode_le_primeArchEndpointHausdorffRadius q
  change ‖z / (R : ℂ)‖ + ‖1 - z / (R : ℂ)‖ = 1
  rw [hz]
  have hcast : ((xiThermalNode q : ℂ) / (R : ℂ)) = (x : ℂ) := by
    apply Complex.ext <;> simp [x]
  rw [hcast]
  have hxnorm : ‖(x : ℂ)‖ = x := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx0]
  have hsubcast : (1 : ℂ) - (x : ℂ) = ((1 - x : ℝ) : ℂ) := by
    push_cast
    ring
  have hsubnorm : ‖(1 : ℂ) - (x : ℂ)‖ = 1 - x := by
    rw [hsubcast, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (sub_nonneg.mpr hx1)]
  rw [hxnorm, hsubnorm]
  ring

/-- **Universal atom phase confinement.** Every divisor atom, on or off the critical line, has
affine Bernstein amplitude at most the fixed base `B_* < 3/2`. -/
theorem xiEndpointBernsteinAtomAmplitudeBase_le_universal
    (q : XiZeroCopy) :
    xiEndpointBernsteinAtomAmplitudeBase q ≤ xiUniversalBernsteinAmplitudeBase := by
  by_cases hoff : (q.1 : ℂ).re ≠ 1 / 2
  · have hu := norm_xiEndpointNormalizedReciprocalSquare_le_offLineRadius q hoff
    have hsub : ‖1 - xiEndpointNormalizedReciprocalSquare q‖ ≤
        1 + ‖xiEndpointNormalizedReciprocalSquare q‖ := by
      calc
        ‖1 - xiEndpointNormalizedReciprocalSquare q‖ ≤
            ‖(1 : ℂ)‖ + ‖xiEndpointNormalizedReciprocalSquare q‖ := norm_sub_le _ _
        _ = 1 + ‖xiEndpointNormalizedReciprocalSquare q‖ := by norm_num
    dsimp only [xiEndpointBernsteinAtomAmplitudeBase,
      xiUniversalBernsteinAmplitudeBase]
    linarith
  · have hline : (q.1 : ℂ).re = 1 / 2 := not_ne_iff.mp hoff
    rw [xiEndpointBernsteinAtomAmplitudeBase_eq_one_of_onLine q hline]
    exact one_lt_xiUniversalBernsteinAmplitudeBase.le

/-- The absolute reciprocal-square divisor mass is finite. -/
def xiReciprocalSquareAbsoluteMass : ℝ :=
  ∑' q : XiZeroCopy, ‖xiZeroCopyReciprocalSquare q‖

theorem xiReciprocalSquareAbsoluteMass_nonneg :
    0 ≤ xiReciprocalSquareAbsoluteMass :=
  tsum_nonneg fun _ => norm_nonneg _

/-- Every nonnegative uniformly bounded energy sequence has zero exponential rate. -/
theorem subexponentialSquareEnergy_of_bounded
    (E : ℕ → ℝ) (hE : ∀ n, 0 ≤ E n) (C : ℝ) (hC : ∀ n, E n ≤ C) :
    SubexponentialSquareEnergyAtNatInfinity E := by
  intro r hr
  have hpow : Tendsto (fun n : ℕ => (r⁻¹) ^ n) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one
      (inv_nonneg.mpr (zero_le_one.trans hr.le))
      (inv_lt_one_of_one_lt₀ hr)
  have hupper : Tendsto (fun n : ℕ => C * (r⁻¹) ^ n) atTop (nhds 0) := by
    simpa using tendsto_const_nhds.mul hpow
  apply squeeze_zero
    (fun n => div_nonneg (hE n) (pow_nonneg (zero_le_one.trans hr.le) n))
    (fun n => ?_) hupper
  rw [div_eq_mul_inv, ← inv_pow]
  exact mul_le_mul_of_nonneg_right (hC n)
    (pow_nonneg (inv_nonneg.mpr (zero_le_one.trans hr.le)) n)

/-- The endpoint dephased purity stays in one finite energy chamber. -/
def PrimeArchEndpointBernsteinPurityBounded : Prop :=
  ∃ C : ℝ, ∀ n : ℕ, primeArchEndpointBernsteinPurity n ≤ C

private lemma bernsteinCoefficientL1_zero (m : ℕ → ℝ) :
    bernsteinCoefficientL1 m 0 = |m 0| := by
  have hsum := sum_bernsteinCoefficient m 0
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add] at hsum
  rw [bernsteinCoefficientL1]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, hsum]

/-- Under RH the endpoint purity is bounded by the square of the conserved zeroth source mass at
every degree. -/
theorem primeArchEndpointBernsteinPurity_le_mass_sq_of_riemannHypothesis
    (hRH : RiemannHypothesis) (n : ℕ) :
    primeArchEndpointBernsteinPurity n ≤ normalizedPrimeArchMoment 0 ^ 2 := by
  have hL1 :
      bernsteinCoefficientL1
          (radiusNormalizedMoment primeArchEndpointHausdorffRadius
            normalizedPrimeArchMoment) n =
        normalizedPrimeArchMoment 0 := by
    cases n with
    | zero =>
        rw [bernsteinCoefficientL1_zero]
        simp only [radiusNormalizedMoment, pow_zero, div_one]
        exact abs_of_pos normalizedPrimeArchMoment_zero_pos
    | succ N =>
        exact
          riemannHypothesis_iff_forall_primeArchBernsteinCoefficientL1_eq_mass.mp hRH N
  calc
    primeArchEndpointBernsteinPurity n ≤
        (bernsteinCoefficientL1
          (radiusNormalizedMoment primeArchEndpointHausdorffRadius
            normalizedPrimeArchMoment) n) ^ 2 :=
      bernsteinCoefficientPurity_le_l1_sq _ _
    _ = normalizedPrimeArchMoment 0 ^ 2 := by rw [hL1]

/-- **Bounded Loschmidt-purity RH law.**  The endpoint lies in the critical phase exactly when its
positive dephased purity remains uniformly bounded in the Bernstein degree. -/
theorem riemannHypothesis_iff_primeArchEndpointBernsteinPurity_bounded :
    RiemannHypothesis ↔ PrimeArchEndpointBernsteinPurityBounded := by
  constructor
  · intro hRH
    exact ⟨normalizedPrimeArchMoment 0 ^ 2,
      primeArchEndpointBernsteinPurity_le_mass_sq_of_riemannHypothesis hRH⟩
  · rintro ⟨C, hC⟩
    apply riemannHypothesis_iff_primeArchEndpointBernsteinTotalVariation_subexponential.mpr
    apply (subexponentialSquareEnergy_iff_l1
      (radiusNormalizedMoment primeArchEndpointHausdorffRadius
        normalizedPrimeArchMoment)).mp
    exact subexponentialSquareEnergy_of_bounded _
      (fun n => bernsteinCoefficientPurity_nonneg _ n) C hC

/-- The critical phase is equivalently the sharp mass-squared chamber; no larger unspecified
bound is needed. -/
theorem riemannHypothesis_iff_primeArchEndpointBernsteinPurity_le_mass_sq :
    RiemannHypothesis ↔
      ∀ n : ℕ, primeArchEndpointBernsteinPurity n ≤ normalizedPrimeArchMoment 0 ^ 2 := by
  constructor
  · exact primeArchEndpointBernsteinPurity_le_mass_sq_of_riemannHypothesis
  · intro h
    exact riemannHypothesis_iff_primeArchEndpointBernsteinPurity_bounded.mpr
      ⟨normalizedPrimeArchMoment 0 ^ 2, h⟩

/-- Sum of the norms of all degree-`n` Bernstein basis values at a complex point. -/
theorem sum_norm_evalRealPolynomial_bernsteinPolynomial
    (n : ℕ) (u : ℂ) :
    ∑ i ∈ Finset.range (n + 1),
        ‖evalRealPolynomial (bernsteinPolynomial ℝ n i) u‖ =
      (‖u‖ + ‖1 - u‖) ^ n := by
  rw [add_pow]
  apply Finset.sum_congr rfl
  intro i hi
  rw [bernsteinPolynomial]
  simp only [evalRealPolynomial, Polynomial.eval_map, Polynomial.eval₂_mul,
    Polynomial.eval₂_natCast, Polynomial.eval₂_pow, Polynomial.eval₂_X,
    Polynomial.eval₂_sub, Polynomial.eval₂_one, norm_mul, norm_pow,
    Complex.norm_natCast]
  ring

/-- Pointwise divisor-envelope bound for one source Bernstein coefficient. -/
theorem abs_bernsteinCoefficient_endpoint_le_divisorEnvelope
    (n i : ℕ) :
    |bernsteinCoefficient
        (radiusNormalizedMoment primeArchEndpointHausdorffRadius
          normalizedPrimeArchMoment) n i| ≤
      ∑' q : XiZeroCopy,
        ‖xiZeroCopyReciprocalSquare q‖ *
          ‖evalRealPolynomial (bernsteinPolynomial ℝ n i)
            (xiEndpointNormalizedReciprocalSquare q)‖ := by
  let p := bernsteinPolynomial ℝ n i
  have hsumm := summable_xiCentralRadiusNormalizedPolynomialTerm
    primeArchEndpointHausdorffRadius p
  rw [← Real.norm_eq_abs, ← Complex.norm_real,
    bernsteinCoefficient,
    ← xiCentralRadiusNormalizedPolynomialMoment_eq_source,
    xiCentralRadiusNormalizedPolynomialMoment_eq_tsum]
  refine (norm_tsum_le_tsum_norm hsumm.norm).trans_eq ?_
  apply tsum_congr
  intro q
  rw [norm_mul]
  rfl

/-- **Unconditional source total-variation estimate.** The endpoint Bernstein coefficient vector
has amplitude growth bounded by the explicit base `B_* < 3/2`. -/
theorem primeArchEndpointBernsteinTotalVariation_le_confinedPhase (n : ℕ) :
    primeArchEndpointBernsteinTotalVariation n ≤
      xiReciprocalSquareAbsoluteMass * xiUniversalBernsteinAmplitudeBase ^ n := by
  rw [primeArchEndpointBernsteinTotalVariation, bernsteinCoefficientL1]
  calc
    (∑ i ∈ Finset.range (n + 1),
        |bernsteinCoefficient
          (radiusNormalizedMoment primeArchEndpointHausdorffRadius
            normalizedPrimeArchMoment) n i|) ≤
      ∑ i ∈ Finset.range (n + 1),
        ∑' q : XiZeroCopy,
          ‖xiZeroCopyReciprocalSquare q‖ *
            ‖evalRealPolynomial (bernsteinPolynomial ℝ n i)
              (xiEndpointNormalizedReciprocalSquare q)‖ := by
        exact Finset.sum_le_sum fun i _ =>
          abs_bernsteinCoefficient_endpoint_le_divisorEnvelope n i
    _ = ∑' q : XiZeroCopy,
        ∑ i ∈ Finset.range (n + 1),
          (‖xiZeroCopyReciprocalSquare q‖ *
            ‖evalRealPolynomial (bernsteinPolynomial ℝ n i)
              (xiEndpointNormalizedReciprocalSquare q)‖) := by
        rw [Summable.tsum_finsetSum]
        intro i hi
        simpa only [norm_mul, Real.norm_eq_abs, abs_norm] using
          (summable_xiCentralRadiusNormalizedPolynomialTerm
            primeArchEndpointHausdorffRadius
            (bernsteinPolynomial ℝ n i)).norm
    _ = ∑' q : XiZeroCopy,
        ‖xiZeroCopyReciprocalSquare q‖ *
          xiEndpointBernsteinAtomAmplitudeBase q ^ n := by
        apply tsum_congr
        intro q
        rw [← Finset.mul_sum,
          sum_norm_evalRealPolynomial_bernsteinPolynomial]
        rfl
    _ ≤ ∑' q : XiZeroCopy,
        ‖xiZeroCopyReciprocalSquare q‖ *
          xiUniversalBernsteinAmplitudeBase ^ n := by
        apply Summable.tsum_le_tsum
        · intro q
          exact mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀
              (by exact add_nonneg (norm_nonneg _) (norm_nonneg _))
              (xiEndpointBernsteinAtomAmplitudeBase_le_universal q) n)
            (norm_nonneg _)
        · exact Summable.of_nonneg_of_le
            (fun q => mul_nonneg (norm_nonneg _) (pow_nonneg
              (by exact add_nonneg (norm_nonneg _) (norm_nonneg _)) _))
            (fun q => mul_le_mul_of_nonneg_left
              (pow_le_pow_left₀
                (by exact add_nonneg (norm_nonneg _) (norm_nonneg _))
                (xiEndpointBernsteinAtomAmplitudeBase_le_universal q) n)
              (norm_nonneg _))
            (summable_xiZeroCopyReciprocalSquare.norm.mul_right
              (xiUniversalBernsteinAmplitudeBase ^ n))
        · exact summable_xiZeroCopyReciprocalSquare.norm.mul_right
            (xiUniversalBernsteinAmplitudeBase ^ n)
    _ = xiReciprocalSquareAbsoluteMass *
        xiUniversalBernsteinAmplitudeBase ^ n := by
      rw [xiReciprocalSquareAbsoluteMass, tsum_mul_right]

/-- The positive Loschmidt purity inherits the square of the confined amplitude estimate. -/
theorem primeArchEndpointBernsteinPurity_le_confinedPhase (n : ℕ) :
    primeArchEndpointBernsteinPurity n ≤
      (xiReciprocalSquareAbsoluteMass *
        xiUniversalBernsteinAmplitudeBase ^ n) ^ 2 :=
  (bernsteinCoefficientPurity_le_l1_sq _ _).trans
    ((sq_le_sq₀
      (Finset.sum_nonneg fun _ _ => abs_nonneg _)
      (mul_nonneg xiReciprocalSquareAbsoluteMass_nonneg
        (pow_nonneg
          (zero_le_one.trans one_lt_xiUniversalBernsteinAmplitudeBase.le) n))).2
      (primeArchEndpointBernsteinTotalVariation_le_confinedPhase n))

/-- Conserved total coefficient mass supplies a universal polynomial lower bound for purity. -/
theorem mass_sq_le_card_mul_primeArchEndpointBernsteinPurity (n : ℕ) :
    normalizedPrimeArchMoment 0 ^ 2 ≤
      (n + 1 : ℝ) * primeArchEndpointBernsteinPurity n := by
  have h := sq_sum_le_card_mul_sum_sq
    (s := Finset.range (n + 1))
    (f := fun i => bernsteinCoefficient
      (radiusNormalizedMoment primeArchEndpointHausdorffRadius
        normalizedPrimeArchMoment) n i)
  rw [sum_bernsteinCoefficient] at h
  simpa only [Finset.card_range, Nat.cast_add, Nat.cast_one,
    primeArchEndpointBernsteinPurity, bernsteinCoefficientPurity,
    radiusNormalizedMoment, pow_zero, div_one] using h

/-- Normalization above the square of the universal amplitude base kills the purity
unconditionally. -/
theorem tendsto_primeArchEndpointBernsteinPurity_div_pow_of_universalBase_sq_lt
    {r : ℝ} (hr : xiUniversalBernsteinAmplitudeBase ^ 2 < r) :
    Tendsto (fun n : ℕ => primeArchEndpointBernsteinPurity n / r ^ n)
      atTop (nhds 0) := by
  have hrpos : 0 < r := lt_trans
    (sq_pos_of_pos (zero_lt_one.trans one_lt_xiUniversalBernsteinAmplitudeBase)) hr
  let q : ℝ := xiUniversalBernsteinAmplitudeBase ^ 2 / r
  have hq0 : 0 ≤ q := div_nonneg
    (sq_nonneg xiUniversalBernsteinAmplitudeBase) hrpos.le
  have hq1 : q < 1 := (div_lt_one hrpos).2 hr
  have hpow : Tendsto (fun n : ℕ => q ^ n) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1
  have hupper : Tendsto
      (fun n : ℕ => xiReciprocalSquareAbsoluteMass ^ 2 * q ^ n)
      atTop (nhds 0) := by
    simpa using tendsto_const_nhds.mul hpow
  apply squeeze_zero
    (fun n => div_nonneg (bernsteinCoefficientPurity_nonneg _ n)
      (pow_nonneg hrpos.le n))
    (fun n => ?_) hupper
  calc
    primeArchEndpointBernsteinPurity n / r ^ n ≤
        (xiReciprocalSquareAbsoluteMass *
          xiUniversalBernsteinAmplitudeBase ^ n) ^ 2 / r ^ n :=
      div_le_div_of_nonneg_right
        (primeArchEndpointBernsteinPurity_le_confinedPhase n)
        (pow_nonneg hrpos.le n)
    _ = xiReciprocalSquareAbsoluteMass ^ 2 * q ^ n := by
      dsimp only [q]
      rw [div_pow]
      ring

/-- **Confined false-RH phase law.** Failure of RH forces a strict surviving purity exponent, but
the endpoint curvature confines that energy exponent below the square of `B_* < 3/2`. -/
theorem exists_confined_primeArchEndpointBernsteinPurity_phase_of_not_riemannHypothesis
    (hRH : ¬ RiemannHypothesis) :
    ∃ r : ℝ,
      1 < r ∧ r ≤ xiUniversalBernsteinAmplitudeBase ^ 2 ∧
        ¬ Tendsto (fun n : ℕ => primeArchEndpointBernsteinPurity n / r ^ n)
          atTop (nhds 0) := by
  have hnsub :
      ¬ SubexponentialSquareEnergyAtNatInfinity primeArchEndpointBernsteinPurity := by
    intro hsub
    exact hRH
      (riemannHypothesis_iff_primeArchEndpointBernsteinPurity_subexponential.mpr hsub)
  simp only [SubexponentialSquareEnergyAtNatInfinity] at hnsub
  push Not at hnsub
  obtain ⟨r, hr, hnot⟩ := hnsub
  refine ⟨r, hr, ?_, hnot⟩
  by_contra hle
  have hgt : xiUniversalBernsteinAmplitudeBase ^ 2 < r := lt_of_not_ge hle
  exact hnot
    (tendsto_primeArchEndpointBernsteinPurity_div_pow_of_universalBase_sq_lt hgt)

/-- **Confined Loschmidt phase master theorem.**  The source-defined purity is unconditionally
trapped between a conserved polynomial floor and an explicit strict exponential ceiling.  RH is
exactly its sharp bounded phase; failure of RH is exactly a surviving exponent inside the confined
window. -/
theorem primeArchBernsteinConfinedLoschmidtPhaseMaster :
    xiUniversalBernsteinAmplitudeBase < 3 / 2 ∧
    (∀ n : ℕ,
      normalizedPrimeArchMoment 0 ^ 2 ≤
          (n + 1 : ℝ) * primeArchEndpointBernsteinPurity n ∧
        primeArchEndpointBernsteinPurity n ≤
          (xiReciprocalSquareAbsoluteMass *
            xiUniversalBernsteinAmplitudeBase ^ n) ^ 2) ∧
    (RiemannHypothesis ↔
      ∀ n : ℕ,
        primeArchEndpointBernsteinPurity n ≤ normalizedPrimeArchMoment 0 ^ 2) ∧
    (RiemannHypothesis ↔ PrimeArchEndpointBernsteinPurityBounded) ∧
    (¬ RiemannHypothesis →
      ∃ r : ℝ,
        1 < r ∧ r ≤ xiUniversalBernsteinAmplitudeBase ^ 2 ∧
          ¬ Tendsto (fun n : ℕ => primeArchEndpointBernsteinPurity n / r ^ n)
            atTop (nhds 0)) := by
  exact ⟨
    xiUniversalBernsteinAmplitudeBase_lt_three_halves,
    fun n => ⟨mass_sq_le_card_mul_primeArchEndpointBernsteinPurity n,
      primeArchEndpointBernsteinPurity_le_confinedPhase n⟩,
    riemannHypothesis_iff_primeArchEndpointBernsteinPurity_le_mass_sq,
    riemannHypothesis_iff_primeArchEndpointBernsteinPurity_bounded,
    exists_confined_primeArchEndpointBernsteinPurity_phase_of_not_riemannHypothesis⟩

end

end RHTower
