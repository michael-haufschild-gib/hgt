import GaloisForLFunctions.RHTower.PrimeArchBernsteinConfinedPhase
import GaloisForLFunctions.RHTower.XiOffLineQuartetThermalOrientationBound

/-!
# Narrow-sector confinement of the prime--archimedean Bernstein phase

The disk-only Bernstein estimate loses the narrow sector forced by the exact off-line-quartet
orientation bound.  After endpoint normalization every reciprocal-square atom satisfies

`im u ^ 2 ≤ (1 / 84) * re u ^ 2`.

For an off-line atom one also has `‖u‖ < 1 / 4`.  These two source-derived inequalities imply the
strict elliptic bound

`‖u‖ + ‖1 - u‖ < 1003 / 1000`.

The complete Bernstein total variation and Loschmidt purity therefore have exponential bases
`1003 / 1000` and `(1003 / 1000)^2 = 1006009 / 1000000 < 1007 / 1000`, respectively.  Thus
failure of RH can occupy only a strict seven-per-mille purity window above the critical exponent
one.
-/

open Complex Filter Topology
open scoped BigOperators Polynomial
open Polynomial

namespace RHTower

noncomputable section

/-- Rational amplitude ceiling supplied jointly by the endpoint quarter disk and the exact
one-eighty-fourth orientation sector. -/
def xiSectorConfinedBernsteinAmplitudeBase : ℝ := 1003 / 1000

theorem one_lt_xiSectorConfinedBernsteinAmplitudeBase :
    1 < xiSectorConfinedBernsteinAmplitudeBase := by
  norm_num [xiSectorConfinedBernsteinAmplitudeBase]

theorem xiSectorConfinedBernsteinAmplitudeBase_sq_eq :
    xiSectorConfinedBernsteinAmplitudeBase ^ 2 = 1006009 / 1000000 := by
  norm_num [xiSectorConfinedBernsteinAmplitudeBase]

theorem xiSectorConfinedBernsteinAmplitudeBase_sq_lt_oneThousandSeven_over_oneThousand :
    xiSectorConfinedBernsteinAmplitudeBase ^ 2 < 1007 / 1000 := by
  norm_num [xiSectorConfinedBernsteinAmplitudeBase]

theorem xiSectorConfinedBernsteinAmplitudeBase_sq_lt_oneHundredOne_over_oneHundred :
    xiSectorConfinedBernsteinAmplitudeBase ^ 2 < 101 / 100 := by
  norm_num [xiSectorConfinedBernsteinAmplitudeBase]

/-- Pure geometry: the `1/84` sector inside the strict quarter disk lies in the Bernstein ellipse
with major-axis sum `1003/1000`. -/
theorem norm_add_norm_one_sub_lt_sectorConfinedBase
    {u : ℂ} (hr : ‖u‖ < 1 / 4)
    (hx : 0 ≤ u.re)
    (hy : u.im ^ 2 ≤ (1 / 84 : ℝ) * u.re ^ 2) :
    ‖u‖ + ‖1 - u‖ < xiSectorConfinedBernsteinAmplitudeBase := by
  let r : ℝ := ‖u‖
  let s : ℝ := ‖1 - u‖
  let x : ℝ := u.re
  have hr0 : 0 ≤ r := norm_nonneg u
  have hs0 : 0 ≤ s := norm_nonneg (1 - u)
  have hx0 : 0 ≤ x := hx
  have hrSq : r ^ 2 = x ^ 2 + u.im ^ 2 := by
    dsimp only [r, x]
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  have hrx : r ^ 2 ≤ (85 / 84 : ℝ) * x ^ 2 := by
    rw [hrSq]
    dsimp only [x] at hy ⊢
    nlinarith
  have hcxSq : ((913 / 919 : ℝ) * r) ^ 2 ≤ x ^ 2 := by
    have hconst : (913 / 919 : ℝ) ^ 2 * (85 / 84 : ℝ) < 1 := by
      norm_num
    nlinarith [sq_nonneg x]
  have hcx0 : 0 ≤ (913 / 919 : ℝ) * r := by positivity
  have hcx : (913 / 919 : ℝ) * r ≤ x := by
    nlinarith [sq_nonneg (x + (913 / 919 : ℝ) * r)]
  have hsSq : s ^ 2 = 1 - 2 * x + r ^ 2 := by
    dsimp only [s, x, r]
    rw [Complex.sq_norm, Complex.normSq_apply, Complex.sq_norm,
      Complex.normSq_apply]
    simp only [sub_re, one_re, sub_im, one_im]
    ring
  have hBr : 0 < xiSectorConfinedBernsteinAmplitudeBase - r := by
    dsimp only [r] at hr ⊢
    norm_num [xiSectorConfinedBernsteinAmplitudeBase] at hr ⊢
    linarith
  have hlinear :
      2 * (xiSectorConfinedBernsteinAmplitudeBase - 913 / 919) * r <
        xiSectorConfinedBernsteinAmplitudeBase ^ 2 - 1 := by
    have hcoeff :
        0 < xiSectorConfinedBernsteinAmplitudeBase - 913 / 919 := by
      norm_num [xiSectorConfinedBernsteinAmplitudeBase]
    have hconst :
        2 * (xiSectorConfinedBernsteinAmplitudeBase - 913 / 919) * (1 / 4 : ℝ) <
          xiSectorConfinedBernsteinAmplitudeBase ^ 2 - 1 := by
      norm_num [xiSectorConfinedBernsteinAmplitudeBase]
    nlinarith
  have hsLt : s ^ 2 < (xiSectorConfinedBernsteinAmplitudeBase - r) ^ 2 := by
    nlinarith
  have hs : s < xiSectorConfinedBernsteinAmplitudeBase - r := by
    nlinarith [sq_nonneg (s + (xiSectorConfinedBernsteinAmplitudeBase - r))]
  dsimp only [s, r] at hs ⊢
  linarith

/-- Endpoint normalization preserves the exact atomwise orientation ratio. -/
theorem xiEndpointNormalizedReciprocalSquare_orientation_sq_le
    (q : XiZeroCopy) :
    (xiEndpointNormalizedReciprocalSquare q).im ^ 2 ≤
      (1 / 84 : ℝ) * (xiEndpointNormalizedReciprocalSquare q).re ^ 2 := by
  have hR : 0 < primeArchEndpointHausdorffRadius :=
    primeArchEndpointHausdorffRadius_pos
  have h := xiThermalOrientationTerm_le_one_over_eightyFour_node_sq q
  rw [xiEndpointNormalizedReciprocalSquare]
  simp only [Complex.div_re, Complex.div_im, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, Complex.normSq_ofReal]
  rw [xiThermalNode] at h
  have hscaled := mul_le_mul_of_nonneg_right h
    (sq_nonneg primeArchEndpointHausdorffRadius)
  field_simp [hR.ne']
  nlinarith

/-- **Narrow-sector atom law.** Every endpoint-normalized Xi atom has Bernstein amplitude strictly
below `1003/1000`; line atoms have amplitude exactly one and off-line atoms use both the disk and
orientation constraints. -/
theorem xiEndpointBernsteinAtomAmplitudeBase_lt_sectorConfined
    (q : XiZeroCopy) :
    xiEndpointBernsteinAtomAmplitudeBase q <
      xiSectorConfinedBernsteinAmplitudeBase := by
  by_cases hoff : (q.1 : ℂ).re ≠ 1 / 2
  · have hr : ‖xiEndpointNormalizedReciprocalSquare q‖ < 1 / 4 :=
      (norm_xiEndpointNormalizedReciprocalSquare_le_offLineRadius q hoff).trans_lt
        xiOffLineNormalizedBernsteinRadius_lt_one_fourth
    have hx : 0 ≤ (xiEndpointNormalizedReciprocalSquare q).re := by
      have hR : 0 < primeArchEndpointHausdorffRadius :=
        primeArchEndpointHausdorffRadius_pos
      have hnode : 0 < (xiZeroCopyReciprocalSquare q).re := by
        simpa only [xiThermalNode] using xiThermalNode_pos q
      rw [xiEndpointNormalizedReciprocalSquare]
      simp only [Complex.div_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
        Complex.normSq_ofReal]
      positivity
    exact norm_add_norm_one_sub_lt_sectorConfinedBase hr hx
      (xiEndpointNormalizedReciprocalSquare_orientation_sq_le q)
  · have hline : (q.1 : ℂ).re = 1 / 2 := not_ne_iff.mp hoff
    rw [xiEndpointBernsteinAtomAmplitudeBase_eq_one_of_onLine q hline]
    exact one_lt_xiSectorConfinedBernsteinAmplitudeBase

/-- General transport of a uniform atom-ellipse bound through the complete divisor envelope. -/
theorem primeArchEndpointBernsteinTotalVariation_le_of_atomAmplitudeBase
    (B : ℝ)
    (hB : ∀ q : XiZeroCopy, xiEndpointBernsteinAtomAmplitudeBase q ≤ B)
    (n : ℕ) :
    primeArchEndpointBernsteinTotalVariation n ≤
      xiReciprocalSquareAbsoluteMass * B ^ n := by
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
        ‖xiZeroCopyReciprocalSquare q‖ * B ^ n := by
        apply Summable.tsum_le_tsum
        · intro q
          exact mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀
              (by exact add_nonneg (norm_nonneg _) (norm_nonneg _))
              (hB q) n)
            (norm_nonneg _)
        · exact Summable.of_nonneg_of_le
            (fun q => mul_nonneg (norm_nonneg _) (pow_nonneg
              (by exact add_nonneg (norm_nonneg _) (norm_nonneg _)) _))
            (fun q => mul_le_mul_of_nonneg_left
              (pow_le_pow_left₀
                (by exact add_nonneg (norm_nonneg _) (norm_nonneg _))
                (hB q) n)
              (norm_nonneg _))
            (summable_xiZeroCopyReciprocalSquare.norm.mul_right (B ^ n))
        · exact summable_xiZeroCopyReciprocalSquare.norm.mul_right (B ^ n)
    _ = xiReciprocalSquareAbsoluteMass * B ^ n := by
      rw [xiReciprocalSquareAbsoluteMass, tsum_mul_right]

/-- **Sector-confined total variation.** The complete endpoint Bernstein vector has amplitude
base `1003/1000`. -/
theorem primeArchEndpointBernsteinTotalVariation_le_sectorConfined (n : ℕ) :
    primeArchEndpointBernsteinTotalVariation n ≤
      xiReciprocalSquareAbsoluteMass *
        xiSectorConfinedBernsteinAmplitudeBase ^ n := by
  exact primeArchEndpointBernsteinTotalVariation_le_of_atomAmplitudeBase
    xiSectorConfinedBernsteinAmplitudeBase
    (fun q => (xiEndpointBernsteinAtomAmplitudeBase_lt_sectorConfined q).le) n

/-- The positive Loschmidt purity inherits the square of the narrow-sector amplitude estimate. -/
theorem primeArchEndpointBernsteinPurity_le_sectorConfined (n : ℕ) :
    primeArchEndpointBernsteinPurity n ≤
      (xiReciprocalSquareAbsoluteMass *
        xiSectorConfinedBernsteinAmplitudeBase ^ n) ^ 2 :=
  (bernsteinCoefficientPurity_le_l1_sq _ _).trans
    ((sq_le_sq₀
      (Finset.sum_nonneg fun _ _ => abs_nonneg _)
      (mul_nonneg xiReciprocalSquareAbsoluteMass_nonneg
        (pow_nonneg
          (zero_le_one.trans one_lt_xiSectorConfinedBernsteinAmplitudeBase.le) n))).2
      (primeArchEndpointBernsteinTotalVariation_le_sectorConfined n))

/-- Normalization above the narrow-sector squared base kills the endpoint purity
unconditionally. -/
theorem tendsto_primeArchEndpointBernsteinPurity_div_pow_of_sectorBase_sq_lt
    {r : ℝ} (hr : xiSectorConfinedBernsteinAmplitudeBase ^ 2 < r) :
    Tendsto (fun n : ℕ => primeArchEndpointBernsteinPurity n / r ^ n)
      atTop (nhds 0) := by
  have hrpos : 0 < r := lt_trans
    (sq_pos_of_pos (zero_lt_one.trans one_lt_xiSectorConfinedBernsteinAmplitudeBase)) hr
  let q : ℝ := xiSectorConfinedBernsteinAmplitudeBase ^ 2 / r
  have hq0 : 0 ≤ q := div_nonneg
    (sq_nonneg xiSectorConfinedBernsteinAmplitudeBase) hrpos.le
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
          xiSectorConfinedBernsteinAmplitudeBase ^ n) ^ 2 / r ^ n :=
      div_le_div_of_nonneg_right
        (primeArchEndpointBernsteinPurity_le_sectorConfined n)
        (pow_nonneg hrpos.le n)
    _ = xiReciprocalSquareAbsoluteMass ^ 2 * q ^ n := by
      dsimp only [q]
      rw [div_pow]
      ring

/-- **Exact false-RH phase law.** Failure of RH forces a surviving purity exponent above one and
at most the exact narrow-sector squared base. -/
theorem exists_sectorConfined_primeArchEndpointBernsteinPurity_phase_of_not_riemannHypothesis
    (hRH : ¬ RiemannHypothesis) :
    ∃ r : ℝ,
      1 < r ∧ r ≤ xiSectorConfinedBernsteinAmplitudeBase ^ 2 ∧
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
  have hrbase : r ≤ xiSectorConfinedBernsteinAmplitudeBase ^ 2 := by
    by_contra hle
    have hgt : xiSectorConfinedBernsteinAmplitudeBase ^ 2 < r := lt_of_not_ge hle
    exact hnot
      (tendsto_primeArchEndpointBernsteinPurity_div_pow_of_sectorBase_sq_lt hgt)
  exact ⟨r, hr, hrbase, hnot⟩

/-- A convenient decimal corollary of the exact false-RH chamber. -/
theorem exists_sevenPerMille_primeArchEndpointBernsteinPurity_phase_of_not_riemannHypothesis
    (hRH : ¬ RiemannHypothesis) :
    ∃ r : ℝ,
      1 < r ∧ r < 1007 / 1000 ∧
        ¬ Tendsto (fun n : ℕ => primeArchEndpointBernsteinPurity n / r ^ n)
          atTop (nhds 0) := by
  obtain ⟨r, hr, hrbase, hnot⟩ :=
    exists_sectorConfined_primeArchEndpointBernsteinPurity_phase_of_not_riemannHypothesis hRH
  exact ⟨r, hr,
    hrbase.trans_lt
      xiSectorConfinedBernsteinAmplitudeBase_sq_lt_oneThousandSeven_over_oneThousand,
    hnot⟩

/-- **Narrow-sector Loschmidt master theorem.** The endpoint purity is trapped between its
conserved polynomial floor and the exact `(1003/1000)^(2M)` energy ceiling.  RH is the bounded
phase; false RH is forced into the remaining seven-per-mille exponential chamber. -/
theorem primeArchBernsteinSectorConfinedLoschmidtPhaseMaster :
    xiSectorConfinedBernsteinAmplitudeBase ^ 2 = 1006009 / 1000000 ∧
    xiSectorConfinedBernsteinAmplitudeBase ^ 2 < 1007 / 1000 ∧
    (∀ n : ℕ,
      normalizedPrimeArchMoment 0 ^ 2 ≤
          (n + 1 : ℝ) * primeArchEndpointBernsteinPurity n ∧
        primeArchEndpointBernsteinPurity n ≤
          (xiReciprocalSquareAbsoluteMass *
            xiSectorConfinedBernsteinAmplitudeBase ^ n) ^ 2) ∧
    (RiemannHypothesis ↔
      ∀ n : ℕ,
        primeArchEndpointBernsteinPurity n ≤ normalizedPrimeArchMoment 0 ^ 2) ∧
    (RiemannHypothesis ↔ PrimeArchEndpointBernsteinPurityBounded) ∧
    (¬ RiemannHypothesis →
      ∃ r : ℝ,
        1 < r ∧ r ≤ xiSectorConfinedBernsteinAmplitudeBase ^ 2 ∧
          ¬ Tendsto (fun n : ℕ => primeArchEndpointBernsteinPurity n / r ^ n)
            atTop (nhds 0)) := by
  exact ⟨
    xiSectorConfinedBernsteinAmplitudeBase_sq_eq,
    xiSectorConfinedBernsteinAmplitudeBase_sq_lt_oneThousandSeven_over_oneThousand,
    fun n => ⟨mass_sq_le_card_mul_primeArchEndpointBernsteinPurity n,
      primeArchEndpointBernsteinPurity_le_sectorConfined n⟩,
    riemannHypothesis_iff_primeArchEndpointBernsteinPurity_le_mass_sq,
    riemannHypothesis_iff_primeArchEndpointBernsteinPurity_bounded,
    exists_sectorConfined_primeArchEndpointBernsteinPurity_phase_of_not_riemannHypothesis⟩

end

end RHTower
