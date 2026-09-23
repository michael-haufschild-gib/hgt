import GaloisForLFunctions.HTGeometry.SectorPowerMassLower
import GaloisForLFunctions.RHTower.PrimeArchValuationSixCone
import GaloisForLFunctions.RHTower.XiHeatShellMinimum

/-!
# Unconditional prime--Gamma valuation cones through valuation six

The reciprocal-square Xi atoms lie in the quadratic sector

`Im(u)² ≤ Re(u)² / 84`

and in the disk `‖u‖ < 2/41`.  The quantitative sector-power theorem therefore gives, for every
shift `s ≤ 11`, a positive lower bound for the shifted source mass.  The disk bound controls all
later moments.  Combining both estimates with polynomial coefficient energy proves the exact
low-valuation cones

`224 E_tail(q) ≤ (1960 - 13(2v+1)²) q(0)²`,  `v ≤ 5`.

Together with the separate thirteenth-power argument at `v = 6`, this removes the coupled-Sonin
comparison premise from the union of seven explicit source-positive families.
-/

open scoped BigOperators
open Polynomial

namespace RHTower

noncomputable section

/-- Absolute mass of the reciprocal-square Xi divisor after shift `s`. -/
def xiShiftAbsoluteMass (s : ℕ) : ℝ :=
  ∑' q : XiZeroCopy, ‖xiZeroCopyReciprocalSquare q‖ ^ (s + 1)

theorem summable_xiShiftAbsoluteMass (s : ℕ) :
    Summable (fun q : XiZeroCopy =>
      ‖xiZeroCopyReciprocalSquare q‖ ^ (s + 1)) := by
  simpa only [norm_pow] using (summable_xiZeroCopyReciprocalSquare_pow s).norm

theorem xiShiftAbsoluteMass_nonneg (s : ℕ) :
    0 ≤ xiShiftAbsoluteMass s := by
  exact tsum_nonneg fun q => pow_nonneg (norm_nonneg _) (s + 1)

/-- Every shifted absolute mass is strictly positive because the Xi divisor is nonempty and no
reciprocal-square atom vanishes. -/
theorem xiShiftAbsoluteMass_pos (s : ℕ) :
    0 < xiShiftAbsoluteMass s := by
  let q : XiZeroCopy := Classical.choice nonempty_xiZeroCopy
  exact (summable_xiShiftAbsoluteMass s).tsum_pos
    (fun r => pow_nonneg (norm_nonneg _) (s + 1)) q (by
      apply pow_pos
      rw [norm_pos_iff]
      intro hz
      have hre : 0 < (xiZeroCopyReciprocalSquare q).re := by
        simpa only [xiThermalNode] using xiThermalNode_pos q
      rw [hz] at hre
      norm_num at hre)

/-- Xi reciprocal-square specialization of the quantitative `1/84` sector-power bound. -/
theorem sectorFactor_mul_norm_xiZeroCopyReciprocalSquare_pow_le_re
    (q : XiZeroCopy) (k : ℕ) :
    (1 - (k : ℝ) ^ (2 : ℕ) / 168) *
        ‖xiZeroCopyReciprocalSquare q‖ ^ k ≤
      (xiZeroCopyReciprocalSquare q ^ k).re := by
  apply GaloisForLFunctions.HTGeometry.re_pow_lower_of_re_pos_of_im_sq_le_one_div_eightyFour
  · simpa only [xiThermalNode] using xiThermalNode_pos q
  · simpa only [xiThermalNode] using
      xiThermalOrientationTerm_le_one_over_eightyFour_node_sq q

/-- The shifted prime--Gamma source moment dominates its sectorial absolute mass. -/
theorem sectorFactor_mul_xiShiftAbsoluteMass_le_normalizedPrimeArchMoment
    (s : ℕ) :
    (1 - (((s + 1 : ℕ) : ℝ) ^ (2 : ℕ)) / 168) *
        xiShiftAbsoluteMass s ≤
      normalizedPrimeArchMoment s := by
  have hpow := summable_xiZeroCopyReciprocalSquare_pow s
  have hre : Summable
      (fun q : XiZeroCopy =>
        (xiZeroCopyReciprocalSquare q ^ (s + 1)).re) :=
    Complex.reCLM.summable hpow
  rw [normalizedPrimeArchMoment_eq_re_xiCentralReciprocalMoment,
    ← tsum_xiZeroCopyReciprocalSquare_pow, Complex.re_tsum hpow,
    xiShiftAbsoluteMass, ← tsum_mul_left]
  exact
    ((summable_xiShiftAbsoluteMass s).mul_left
      (1 - (((s + 1 : ℕ) : ℝ) ^ (2 : ℕ)) / 168)).tsum_le_tsum
      (fun q =>
        sectorFactor_mul_norm_xiZeroCopyReciprocalSquare_pow_le_re q (s + 1))
      hre

/-- The first twelve shifted source moments are strictly positive directly from the Xi sector. -/
theorem normalizedPrimeArchMoment_pos_of_le_eleven
    (s : ℕ) (hs : s ≤ 11) :
    0 < normalizedPrimeArchMoment s := by
  have hsCast : (((s + 1 : ℕ) : ℝ)) ≤ 12 := by
    exact_mod_cast (show s + 1 ≤ 12 by omega)
  have hfactor :
      0 < 1 - (((s + 1 : ℕ) : ℝ) ^ (2 : ℕ)) / 168 := by
    nlinarith [sq_nonneg ((((s + 1 : ℕ) : ℝ)) - 12)]
  have hpositive :
      0 < (1 - (((s + 1 : ℕ) : ℝ) ^ (2 : ℕ)) / 168) *
        xiShiftAbsoluteMass s :=
    mul_pos hfactor (xiShiftAbsoluteMass_pos s)
  exact hpositive.trans_le
    (sectorFactor_mul_xiShiftAbsoluteMass_le_normalizedPrimeArchMoment s)

/-- **Thirteen-moment positivity law.**  Every normalized prime--archimedean source moment from
index zero through twelve is unconditionally strictly positive.  Indices below twelve use the
quadratic sector estimate; index twelve uses the exact thirteenth-power sector polynomial. -/
theorem normalizedPrimeArchMoment_pos_of_le_twelve
    (s : ℕ) (hs : s ≤ 12) :
    0 < normalizedPrimeArchMoment s := by
  by_cases hs11 : s ≤ 11
  · exact normalizedPrimeArchMoment_pos_of_le_eleven s hs11
  · have hs12 : s = 12 := by omega
    subst s
    have hmass :
        0 < xiShiftThirteenAbsoluteMass := by
      simpa only [xiShiftAbsoluteMass, xiShiftThirteenAbsoluteMass] using
        xiShiftAbsoluteMass_pos 12
    have hlower :=
      one_eighth_xiShiftThirteenAbsoluteMass_le_normalizedPrimeArchMoment_twelve
    nlinarith

/-- Endpoint disk contraction for every shifted absolute mass. -/
theorem xiShiftAbsoluteTail_le (s n : ℕ) :
    (∑' q : XiZeroCopy,
        ‖xiZeroCopyReciprocalSquare q‖ ^ (s + 1 + n)) ≤
      (2 / 41 : ℝ) ^ n * xiShiftAbsoluteMass s := by
  have hleft : Summable
      (fun q : XiZeroCopy =>
        ‖xiZeroCopyReciprocalSquare q‖ ^ (s + 1 + n)) := by
    have h := (summable_xiZeroCopyReciprocalSquare_pow (s + n)).norm
    simpa only [norm_pow, show s + n + 1 = s + 1 + n by omega] using h
  rw [xiShiftAbsoluteMass, ← tsum_mul_left]
  exact hleft.tsum_le_tsum (fun q => by
    rw [pow_add]
    have hpow : ‖xiZeroCopyReciprocalSquare q‖ ^ n ≤ (2 / 41 : ℝ) ^ n :=
      pow_le_pow_left₀ (norm_nonneg _)
        (norm_xiZeroCopyReciprocalSquare_lt_two_over_fortyOne q).le n
    exact (mul_le_mul_of_nonneg_left hpow
      (pow_nonneg (norm_nonneg _) (s + 1))).trans_eq (mul_comm _ _))
    ((summable_xiShiftAbsoluteMass s).mul_left ((2 / 41 : ℝ) ^ n))

/-- Every later prime--Gamma source moment is bounded by the shifted absolute-mass envelope. -/
theorem abs_normalizedPrimeArchMoment_add_le_xiShiftAbsoluteMass
    (s n : ℕ) :
    |normalizedPrimeArchMoment (s + n)| ≤
      (2 / 41 : ℝ) ^ n * xiShiftAbsoluteMass s := by
  have hpow := summable_xiZeroCopyReciprocalSquare_pow (s + n)
  rw [normalizedPrimeArchMoment_eq_re_xiCentralReciprocalMoment,
    ← tsum_xiZeroCopyReciprocalSquare_pow]
  calc
    |(∑' q : XiZeroCopy,
        xiZeroCopyReciprocalSquare q ^ (s + n + 1)).re| ≤
        ‖∑' q : XiZeroCopy,
          xiZeroCopyReciprocalSquare q ^ (s + n + 1)‖ :=
      Complex.abs_re_le_norm _
    _ ≤ ∑' q : XiZeroCopy,
        ‖xiZeroCopyReciprocalSquare q ^ (s + n + 1)‖ :=
      norm_tsum_le_tsum_norm hpow.norm
    _ = ∑' q : XiZeroCopy,
        ‖xiZeroCopyReciprocalSquare q‖ ^ (s + 1 + n) := by
      apply tsum_congr
      intro q
      rw [norm_pow]
      congr 1
      omega
    _ ≤ (2 / 41 : ℝ) ^ n * xiShiftAbsoluteMass s :=
      xiShiftAbsoluteTail_le s n

/-- Prime--Gamma moment tail beginning at arbitrary shift `s`. -/
def primeArchShiftMoment (s n : ℕ) : ℝ :=
  normalizedPrimeArchMoment (s + n)

theorem summable_abs_primeArchShiftMoment_tail (s : ℕ) :
    Summable (fun n : ℕ => |primeArchShiftMoment s (n + 1)|) := by
  have hgeo :
      Summable (fun n : ℕ =>
        (2 / 41 : ℝ) ^ (n + 1) * xiShiftAbsoluteMass s) := by
    have hbase :
        Summable (fun n : ℕ => (2 / 41 : ℝ) ^ n) :=
      summable_geometric_of_norm_lt_one (by norm_num)
    simpa only [pow_succ, mul_assoc, mul_comm, mul_left_comm] using
      (hbase.mul_left (2 / 41 : ℝ)).mul_right (xiShiftAbsoluteMass s)
  apply Summable.of_nonneg_of_le (fun n => abs_nonneg _) (fun n => ?_) hgeo
  simpa only [primeArchShiftMoment] using
    abs_normalizedPrimeArchMoment_add_le_xiShiftAbsoluteMass s (n + 1)

/-- Total absolute tail after any shift is at most `2/39` of its shifted Xi mass. -/
theorem tsum_abs_primeArchShiftMoment_tail_le (s : ℕ) :
    (∑' n : ℕ, |primeArchShiftMoment s (n + 1)|) ≤
      (2 / 39 : ℝ) * xiShiftAbsoluteMass s := by
  have hgeo :
      HasSum (fun n : ℕ =>
        (2 / 41 : ℝ) ^ (n + 1) * xiShiftAbsoluteMass s)
        ((2 / 39 : ℝ) * xiShiftAbsoluteMass s) := by
    have hbase :
        HasSum (fun n : ℕ => (2 / 41 : ℝ) ^ n) (1 - (2 / 41 : ℝ))⁻¹ :=
      hasSum_geometric_of_lt_one (by norm_num) (by norm_num)
    have h := (hbase.mul_left (2 / 41 : ℝ)).mul_right (xiShiftAbsoluteMass s)
    have hfun : (fun n : ℕ =>
        2 / 41 * (2 / 41 : ℝ) ^ n * xiShiftAbsoluteMass s) =
        fun n : ℕ => (2 / 41 : ℝ) ^ (n + 1) * xiShiftAbsoluteMass s := by
      funext n
      rw [pow_succ]
      ring
    have hval : 2 / 41 * (1 - (2 / 41 : ℝ))⁻¹ * xiShiftAbsoluteMass s =
        (2 / 39 : ℝ) * xiShiftAbsoluteMass s := by
      norm_num
    rw [hfun, hval] at h
    exact h
  calc
    (∑' n : ℕ, |primeArchShiftMoment s (n + 1)|) ≤
        ∑' n : ℕ,
          (2 / 41 : ℝ) ^ (n + 1) * xiShiftAbsoluteMass s :=
      (summable_abs_primeArchShiftMoment_tail s).tsum_le_tsum
        (fun n => by
          simpa only [primeArchShiftMoment] using
            abs_normalizedPrimeArchMoment_add_le_xiShiftAbsoluteMass s (n + 1))
        hgeo.summable
    _ = (2 / 39 : ℝ) * xiShiftAbsoluteMass s := hgeo.tsum_eq

/-- For every shift below twelve, the exact paper coefficient cone makes the shifted Hankel
square nonnegative. -/
theorem momentFunctional_primeArchShiftMoment_sq_nonneg
    (s : ℕ) (hs : s ≤ 11) (p : Polynomial ℝ)
    (hcone : 224 * HTGeometry.polynomialNonconstantCoeffSqEnergy p ≤
      (1960 - 13 * (((s + 1 : ℕ) : ℝ) ^ (2 : ℕ))) * (p.coeff 0) ^ (2 : ℕ)) :
    0 ≤ HTGeometry.momentFunctional (primeArchShiftMoment s) (p ^ (2 : ℕ)) := by
  let E : ℝ := HTGeometry.polynomialCoeffSqEnergy p
  let A : ℝ := xiShiftAbsoluteMass s
  let m0 : ℝ := normalizedPrimeArchMoment s
  let C : ℝ := 168 - (((s + 1 : ℕ) : ℝ) ^ (2 : ℕ))
  have hsCast : (((s + 1 : ℕ) : ℝ)) ≤ 12 := by
    exact_mod_cast (show s + 1 ≤ 12 by omega)
  have hC : 0 < C := by
    dsimp only [C]
    nlinarith [sq_nonneg ((((s + 1 : ℕ) : ℝ)) - 12)]
  have hA : 0 ≤ A := by
    simpa only [A] using xiShiftAbsoluteMass_nonneg s
  have hmass :=
    sectorFactor_mul_xiShiftAbsoluteMass_le_normalizedPrimeArchMoment s
  have hmass' : (C / 168) * A ≤ m0 := by
    dsimp only [A, m0, C]
    convert hmass using 1
    all_goals ring
  have hm0 : 0 ≤ m0 := by
    have hfactor : 0 ≤ C / 168 := by positivity
    exact (mul_nonneg hfactor hA).trans hmass'
  have hAupper : A ≤ (168 / C) * m0 := by
    have hCA : A * C ≤ 168 * m0 := by
      nlinarith
    calc
      A ≤ (168 * m0) / C := (le_div_iff₀ hC).2 hCA
      _ = (168 / C) * m0 := by ring
  have hE : 0 ≤ E := by
    simpa only [E] using HTGeometry.polynomialCoeffSqEnergy_nonneg p
  have htotal :
      224 * E ≤ 13 * C * (p.coeff 0) ^ (2 : ℕ) := by
    dsimp only [E, C, HTGeometry.polynomialCoeffSqEnergy]
    nlinarith
  have hden : 0 < 13 * C := mul_pos (by norm_num) hC
  have hEratio :
      (224 * E) / (13 * C) ≤ (p.coeff 0) ^ (2 : ℕ) :=
    (div_le_iff₀ hden).2 (by
      nlinarith)
  have herr := HTGeometry.abs_momentFunctional_sq_sub_vacuum_le
    (primeArchShiftMoment s) p
    (summable_abs_primeArchShiftMoment_tail s)
    (tsum_abs_primeArchShiftMoment_tail_le s)
  have herr' :
      |HTGeometry.momentFunctional (primeArchShiftMoment s) (p ^ (2 : ℕ)) -
          (p.coeff 0) ^ (2 : ℕ) * m0| ≤
        m0 * (p.coeff 0) ^ (2 : ℕ) := by
    have hmiddle :
        2 * E * ((2 / 39 : ℝ) * A) ≤
          ((224 * E) / (13 * C)) * m0 := by
      calc
        2 * E * ((2 / 39 : ℝ) * A) ≤
            2 * E * ((2 / 39 : ℝ) * ((168 / C) * m0)) := by
          gcongr
        _ = ((224 * E) / (13 * C)) * m0 := by
          field_simp
          all_goals ring
    have hlast :
        ((224 * E) / (13 * C)) * m0 ≤
          m0 * (p.coeff 0) ^ (2 : ℕ) := by
      simpa only [mul_comm] using mul_le_mul_of_nonneg_right hEratio hm0
    exact (herr.trans hmiddle).trans hlast
  have hneg := neg_abs_le
    (HTGeometry.momentFunctional (primeArchShiftMoment s) (p ^ (2 : ℕ)) -
      (p.coeff 0) ^ (2 : ℕ) * m0)
  nlinarith

/-- A test `Xᵛ p`, `v ≤ 5`, has nonnegative source Hankel value on its exact sector coefficient
cone. -/
theorem re_primeArchSourceTraceHankel_X_pow_mul_nonneg_of_le_five
    (v : ℕ) (hv : v ≤ 5) (p : Polynomial ℝ)
    (hcone : 224 * HTGeometry.polynomialNonconstantCoeffSqEnergy p ≤
      (1960 - 13 * ((((2 * v + 1 : ℕ) : ℝ)) ^ (2 : ℕ))) *
        (p.coeff 0) ^ (2 : ℕ)) :
    0 ≤ (primeArchSourceTraceHankel
      ((Polynomial.X : Polynomial ℝ) ^ v * p)).re := by
  rw [re_primeArchSourceTraceHankel_eq_momentFunctional_sq]
  have hshift :
      HTGeometry.momentFunctional normalizedPrimeArchMoment
          (((Polynomial.X : Polynomial ℝ) ^ v * p) ^ (2 : ℕ)) =
        HTGeometry.momentFunctional (primeArchShiftMoment (2 * v)) (p ^ (2 : ℕ)) := by
    calc
      HTGeometry.momentFunctional normalizedPrimeArchMoment
          (((Polynomial.X : Polynomial ℝ) ^ v * p) ^ (2 : ℕ)) =
          HTGeometry.momentFunctional normalizedPrimeArchMoment
            ((p ^ (2 : ℕ)) * (((Polynomial.X : Polynomial ℝ) ^ v) ^ (2 : ℕ))) := by
        congr 1
        ring
      _ = HTGeometry.momentFunctional
          (momentPolynomialTransform normalizedPrimeArchMoment
            (((Polynomial.X : Polynomial ℝ) ^ v) ^ (2 : ℕ))) (p ^ (2 : ℕ)) := by
        rw [momentFunctional_momentPolynomialTransform]
      _ = HTGeometry.momentFunctional
          (shiftedPrimeArchMomentTail v) (p ^ (2 : ℕ)) := by
        rw [momentPolynomialTransform_X_pow_sq_eq_shiftedPrimeArchMomentTail]
      _ = HTGeometry.momentFunctional
          (primeArchShiftMoment (2 * v)) (p ^ (2 : ℕ)) := by
        congr 1
  rw [hshift]
  apply momentFunctional_primeArchShiftMoment_sq_nonneg (2 * v) (by omega) p
  simpa only [show 2 * v + 1 = 2 * v + 1 by rfl] using hcone

/-- Integer-polynomial family covered by the exact sector cones in valuations zero through five. -/
def PrimeArchLowValuationCoefficientCone (p : Polynomial ℤ) : Prop :=
  ∃ (v : ℕ), v ≤ 5 ∧ ∃ q : Polynomial ℤ,
    p = (Polynomial.X : Polynomial ℤ) ^ v * q ∧
      224 * HTGeometry.polynomialNonconstantCoeffSqEnergy
          (q.map (Int.castRingHom ℝ)) ≤
        (1960 - 13 * ((((2 * v + 1 : ℕ) : ℝ)) ^ (2 : ℕ))) *
          ((q.coeff 0 : ℤ) : ℝ) ^ (2 : ℕ)

theorem re_primeArchSourceTraceHankel_nonneg_of_lowValuationCoefficientCone
    (p : Polynomial ℤ) (hp : PrimeArchLowValuationCoefficientCone p) :
    0 ≤ (primeArchSourceTraceHankel (p.map (Int.castRingHom ℝ))).re := by
  obtain ⟨v, hv, q, rfl, hq⟩ := hp
  rw [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X]
  apply re_primeArchSourceTraceHankel_X_pow_mul_nonneg_of_le_five v hv
  simpa using hq

/-- Union of the exact valuation-zero-through-five cones and the thirteenth-power valuation-six
cone. -/
def PrimeArchValuationAtMostSixCoefficientCone (p : Polynomial ℤ) : Prop :=
  PrimeArchLowValuationCoefficientCone p ∨
    PrimeArchValuationSixCoefficientCone p

theorem re_primeArchSourceTraceHankel_nonneg_of_valuationAtMostSixCoefficientCone
    (p : Polynomial ℤ) (hp : PrimeArchValuationAtMostSixCoefficientCone p) :
    0 ≤ (primeArchSourceTraceHankel (p.map (Int.castRingHom ℝ))).re := by
  rcases hp with hp | hp
  · exact re_primeArchSourceTraceHankel_nonneg_of_lowValuationCoefficientCone p hp
  · exact re_primeArchSourceTraceHankel_nonneg_of_valuationSixCoefficientCone p hp

/-- Complement of all seven unconditional prime--Gamma valuation cones. -/
def PrimeArchValuationAtMostSixCoefficientResidual (p : Polynomial ℤ) : Prop :=
  ¬ PrimeArchValuationAtMostSixCoefficientCone p

/-- Coupled-Sonin comparison restricted to tests outside all seven unconditional valuation
cones. -/
def SoninCoupledPrimeArchValuationAtMostSixResidualVariationalUpperBound : Prop :=
  ∀ (p : Polynomial ℤ), PrimeArchValuationAtMostSixCoefficientResidual p →
    ∀ ε : ℝ, 0 < ε →
      ∃ a : SoninCoupledNondegenerateAperture,
        soninAllPrimeCoupledNormalizedPolynomialGramValue a
            (p.map (Int.castRingHom ℝ)) ≤
          (primeArchSourceTraceHankel (p.map (Int.castRingHom ℝ))).re + ε

/-- The unrestricted coupled-Sonin comparison supplies its restriction to tests outside all
seven unconditional valuation cones. -/
theorem
    soninCoupledPrimeArchValuationAtMostSixResidualVariationalUpperBound_of_perTest
    (h : SoninCoupledPrimeArchPerTestVariationalUpperBound) :
    SoninCoupledPrimeArchValuationAtMostSixResidualVariationalUpperBound := by
  intro p _ ε hε
  exact h p ε hε

/-- Exact normalized-value closure supplies the at-most-six residual comparison. -/
theorem
    soninCoupledPrimeArchValuationAtMostSixResidualVariationalUpperBound_of_valueClosure
    (h : SoninCoupledPrimeArchPerTestNormalizedValueClosure) :
    SoninCoupledPrimeArchValuationAtMostSixResidualVariationalUpperBound :=
  soninCoupledPrimeArchValuationAtMostSixResidualVariationalUpperBound_of_perTest
    (soninCoupledPrimeArchPerTestVariationalUpperBound_of_valueClosure h)

/-- Residual comparison outside the seven cones restores every integer source-Hankel
inequality. -/
theorem primeArchSourceTraceHankelIntNonnegative_of_valuationAtMostSixResidualVariationalUpperBound
    (h : SoninCoupledPrimeArchValuationAtMostSixResidualVariationalUpperBound) :
    PrimeArchSourceTraceHankelIntNonnegative := by
  intro p
  by_cases hp : PrimeArchValuationAtMostSixCoefficientCone p
  · exact re_primeArchSourceTraceHankel_nonneg_of_valuationAtMostSixCoefficientCone p hp
  · let q : Polynomial ℝ := p.map (Int.castRingHom ℝ)
    let target : ℝ := (primeArchSourceTraceHankel q).re
    by_contra htarget
    have htargetNeg : target < 0 := lt_of_not_ge htarget
    let ε : ℝ := -target / 2
    have hε : 0 < ε := by
      dsimp only [ε]
      linarith
    obtain ⟨a, ha⟩ := h p hp ε hε
    have hsource :
        0 ≤ soninAllPrimeCoupledNormalizedPolynomialGramValue a q :=
      soninAllPrimeCoupledNormalizedPolynomialGramValue_nonneg a q
    have htargetε : target + ε < 0 := by
      dsimp only [ε]
      linarith
    change soninAllPrimeCoupledNormalizedPolynomialGramValue a q ≤ target + ε at ha
    linarith

/-- Coupled-Sonin comparison only on the complement of the seven proved cones implies RH. -/
theorem riemannHypothesis_of_soninCoupledPrimeArchValuationAtMostSixResidualVariationalUpperBound
    (h : SoninCoupledPrimeArchValuationAtMostSixResidualVariationalUpperBound) :
    RiemannHypothesis :=
  riemannHypothesis_of_primeArchSourceTraceHankelIntNonnegative
    (primeArchSourceTraceHankelIntNonnegative_of_valuationAtMostSixResidualVariationalUpperBound h)

end

end RHTower
