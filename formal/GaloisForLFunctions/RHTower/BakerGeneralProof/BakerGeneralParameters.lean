import GaloisForLFunctions.RHTower.BakerGeneralProof.PolynomialAuxiliaryHeightBounds
import GaloisForLFunctions.RHTower.BakerProof.BakerParameters

/-!
# Parameter family for the general Baker long extrapolation

The construction parameters are powers of one base.  The component cutoff is halved at every
stage while the consecutive sample range gains one power of the base, and the additive and
exponential degree bounds are chosen so that the auxiliary matrix has exactly twice as many
columns as rows.  A base divisible by a fixed power of two makes every halving exact.

The analytic side of the construction is controlled through a single mechanism: every base
occurring in the closed scalar majorants is either a fixed constant or a polynomial in the
parameter, hence eventually below `exp` of the parameter, so every majorant becomes an exponential
whose exponent is a natural polynomial.
-/

open scoped Classical
open BigOperators NumberField
open Filter Topology

namespace GaloisForLFunctions.RHTower.BakerGeneralProof

namespace GeneralParameters

/-- Number of long-extrapolation stages. -/
def iterationLength (n : ℕ) : ℕ := 2 * n * n

/-- Component cutoff after `k` halvings. -/
def stageOrder (n q k : ℕ) : ℕ := q ^ (2 * n + 2) / 2 ^ k

/-- Consecutive sample count at stage `k`. -/
def stageSampleCount (q k : ℕ) : ℕ := q ^ (k + 2)

/-- Additive degree bound of the auxiliary polynomial. -/
def additiveWidth (n q : ℕ) : ℕ := 2 * q ^ (2 * n + 2)

/-- Exponential degree bound of the auxiliary polynomial. -/
def exponentWidth (n q : ℕ) : ℕ := q ^ (2 * n)

/-- Schwarz radius used at the transition out of stage `k`. -/
def stageRadius (q k : ℕ) : ℕ := 4 * q ^ (k + 3)

/-- Cofinal parameter family making every halving exact. -/
def structuredBase (n u : ℕ) : ℕ := 2 ^ (iterationLength n + 1) * u

@[simp] theorem stageOrder_zero (n q : ℕ) : stageOrder n q 0 = q ^ (2 * n + 2) := by
  simp [stageOrder]

/-- The parameter family has exactly twice as many columns as matrix rows. -/
theorem dimension_double (n q : ℕ) :
    2 * (stageSampleCount q 0 * stageOrder n q 0 ^ n) =
      additiveWidth n q * exponentWidth n q ^ n := by
  simp only [stageSampleCount, stageOrder_zero, additiveWidth, exponentWidth,
    ← pow_mul, ← pow_add]
  ring_nf

theorem stageSampleCount_pos {q k : ℕ} (hq : 0 < q) : 0 < stageSampleCount q k :=
  pow_pos hq _

theorem additiveWidth_pos {n q : ℕ} (hq : 0 < q) : 0 < additiveWidth n q :=
  Nat.mul_pos (by norm_num) (pow_pos hq _)

theorem exponentWidth_pos {n q : ℕ} (hq : 0 < q) : 0 < exponentWidth n q :=
  pow_pos hq _

theorem one_le_additiveWidth {n q : ℕ} (hq : 0 < q) : 1 ≤ additiveWidth n q :=
  additiveWidth_pos hq

/-- Halving the component cutoff is exact whenever the parameter carries enough powers of two. -/
theorem two_mul_stageOrder_succ {n q k : ℕ} (hdvd : 2 ^ (k + 1) ∣ q ^ (2 * n + 2)) :
    2 * stageOrder n q (k + 1) = stageOrder n q k := by
  obtain ⟨b, hb⟩ := hdvd
  unfold stageOrder
  rw [hb]
  rw [Nat.mul_div_cancel_left b (pow_pos (by norm_num) (k + 1))]
  rw [pow_succ, mul_assoc, Nat.mul_div_cancel_left _ (pow_pos (by norm_num : 0 < 2) k)]

theorem structuredBase_dvd (n u k : ℕ) (hk : k ≤ iterationLength n) :
    2 ^ (k + 1) ∣ (structuredBase n u) ^ (2 * n + 2) := by
  unfold structuredBase
  rw [mul_pow, ← pow_mul]
  refine Dvd.dvd.mul_right (pow_dvd_pow 2 ?_) _
  have h1 : k + 1 ≤ iterationLength n + 1 := by omega
  have h2 : iterationLength n + 1 ≤ (iterationLength n + 1) * (2 * n + 2) :=
    Nat.le_mul_of_pos_right _ (by omega)
  omega

theorem structuredBase_pos {n u : ℕ} (hu : 0 < u) : 0 < structuredBase n u :=
  Nat.mul_pos (pow_pos (by norm_num) _) hu

theorem two_pow_le_structuredBase {n u : ℕ} (hu : 0 < u) :
    2 ^ (iterationLength n + 1) ≤ structuredBase n u := by
  unfold structuredBase
  exact Nat.le_mul_of_pos_right _ hu

theorem structuredBase_tendsto_atTop (n : ℕ) :
    Tendsto (fun u : ℕ => structuredBase n u) atTop atTop := by
  unfold structuredBase
  exact Filter.tendsto_id.const_mul_atTop' (pow_pos (by norm_num) _)

/-- Every halving through the terminal stage of the structured family is exact. -/
theorem two_mul_stageOrder_succ_structured (n u k : ℕ) (hk : k ≤ iterationLength n) :
    2 * stageOrder n (structuredBase n u) (k + 1) = stageOrder n (structuredBase n u) k :=
  two_mul_stageOrder_succ (structuredBase_dvd n u k hk)


theorem le_exp_self {y : ℝ} : y ≤ Real.exp y :=
  le_trans (by linarith) (Real.add_one_le_exp y)

theorem pow_le_exp_mul {y w : ℝ} (hy : 0 ≤ y) (hyw : y ≤ Real.exp w) (E : ℕ) :
    y ^ E ≤ Real.exp (w * (E : ℝ)) := by
  calc
    y ^ E ≤ (Real.exp w) ^ E := pow_le_pow_left₀ hy hyw E
    _ = Real.exp ((E : ℝ) * w) := (Real.exp_nat_mul w E).symm
    _ = Real.exp (w * (E : ℝ)) := by rw [mul_comm]

/-- Every fixed real multiple of a natural power is eventually below the exponential. -/
theorem eventually_const_pow_le_exp (C : ℝ) (j : ℕ) :
    ∀ᶠ q : ℕ in atTop, C * (q : ℝ) ^ j ≤ Real.exp q :=
  GaloisForLFunctions.RHTower.BakerProof.BakerParameters.eventually_const_mul_natCast_pow_le_exp C j


@[simp] theorem additiveWidth_cast (n q : ℕ) :
    ((additiveWidth n q : ℕ) : ℝ) = 2 * (q : ℝ) ^ (2 * n + 2) := by
  simp [additiveWidth]

@[simp] theorem exponentWidth_cast (n q : ℕ) :
    ((exponentWidth n q : ℕ) : ℝ) = (q : ℝ) ^ (2 * n) := by
  simp [exponentWidth]

@[simp] theorem stageSampleCount_cast (q k : ℕ) :
    ((stageSampleCount q k : ℕ) : ℝ) = (q : ℝ) ^ (k + 2) := by
  simp [stageSampleCount]

@[simp] theorem stageRadius_cast (q k : ℕ) :
    ((stageRadius q k : ℕ) : ℝ) = 4 * (q : ℝ) ^ (k + 3) := by
  simp [stageRadius]

theorem columnCount_cast (n q : ℕ) :
    ((additiveWidth n q * exponentWidth n q ^ n : ℕ) : ℝ) =
      2 * (q : ℝ) ^ (2 * n * n + 2 * n + 2) := by
  push_cast [additiveWidth, exponentWidth]
  rw [← pow_mul, mul_assoc, ← pow_add]
  ring_nf

theorem rowCount_cast (n q : ℕ) :
    ((stageSampleCount q 0 * stageOrder n q 0 ^ n : ℕ) : ℝ) =
      (q : ℝ) ^ (2 * n * n + 2 * n + 2) := by
  rw [stageOrder_zero]
  push_cast [stageSampleCount]
  rw [← pow_mul, ← pow_add]
  ring_nf

theorem jetGrowthBase_stage_le
    (R : SolvedRelation) (c : ℤ) {q : ℕ} (hq : 1 ≤ q) :
    R.jetGrowthBase c (additiveWidth R.n q) (exponentWidth R.n q) ≤
      5 * (1 + |(c : ℝ)|) * (1 + R.eigenCoordinateHouseSum c) * (q : ℝ) ^ (4 * R.n + 2) := by
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hE0 : 0 ≤ R.eigenCoordinateHouseSum c := R.eigenCoordinateHouseSum_nonneg c
  have hc0 : (0 : ℝ) ≤ |(c : ℝ)| := abs_nonneg _
  have hpowA : (1 : ℝ) ≤ (q : ℝ) ^ (2 * R.n + 2) := one_le_pow₀ hq1
  have hpowB : (1 : ℝ) ≤ (q : ℝ) ^ (2 * R.n) := one_le_pow₀ hq1
  unfold _root_.GaloisForLFunctions.RHTower.BakerGeneralProof.SolvedRelation.jetGrowthBase
    _root_.GaloisForLFunctions.RHTower.BakerGeneralProof.SolvedRelation.eigenHouseBound
  rw [additiveWidth_cast, exponentWidth_cast]
  have h1 : 1 + 2 * (2 * (q : ℝ) ^ (2 * R.n + 2)) ≤ 5 * (q : ℝ) ^ (2 * R.n + 2) := by
    nlinarith
  have h2 : 1 + (q : ℝ) ^ (2 * R.n) * R.eigenCoordinateHouseSum c ≤
      (1 + R.eigenCoordinateHouseSum c) * (q : ℝ) ^ (2 * R.n) := by
    nlinarith
  have hpow : (q : ℝ) ^ (2 * R.n + 2) * (q : ℝ) ^ (2 * R.n) = (q : ℝ) ^ (4 * R.n + 2) := by
    rw [← pow_add]
    ring_nf
  have hcpos : (0 : ℝ) ≤ 1 + |(c : ℝ)| := by linarith
  calc
    (1 + 2 * (2 * (q : ℝ) ^ (2 * R.n + 2))) * (1 + |(c : ℝ)|) *
        (1 + (q : ℝ) ^ (2 * R.n) * R.eigenCoordinateHouseSum c) ≤
        (5 * (q : ℝ) ^ (2 * R.n + 2)) * (1 + |(c : ℝ)|) *
          ((1 + R.eigenCoordinateHouseSum c) * (q : ℝ) ^ (2 * R.n)) := by
      gcongr
    _ = 5 * (1 + |(c : ℝ)|) * (1 + R.eigenCoordinateHouseSum c) * (q : ℝ) ^ (4 * R.n + 2) := by
      rw [← hpow]; ring


theorem entryExponent_cast (n q : ℕ) :
    ((stageSampleCount q 0 * (n * exponentWidth n q) : ℕ) : ℝ) =
      (n : ℝ) * (q : ℝ) ^ (2 * n + 2) := by
  push_cast [stageSampleCount, exponentWidth]
  ring

theorem entryExponent_cast' (n q : ℕ) :
    ((n * exponentWidth n q * stageSampleCount q 0 : ℕ) : ℝ) =
      (n : ℝ) * (q : ℝ) ^ (2 * n + 2) := by
  push_cast [stageSampleCount, exponentWidth]
  ring

theorem orderExponent_cast (n q : ℕ) :
    ((n * stageOrder n q 0 : ℕ) : ℝ) = (n : ℝ) * (q : ℝ) ^ (2 * n + 2) := by
  rw [stageOrder_zero]
  push_cast
  ring

theorem exists_eventually_entryScalarBound_le_exp
    (R : SolvedRelation) (c d : ℤ) :
    ∃ CE : ℝ, 0 ≤ CE ∧ ∀ᶠ q : ℕ in atTop,
      R.auxiliaryEntryScalarBound c d (additiveWidth R.n q) (exponentWidth R.n q)
        (stageSampleCount q 0) (stageOrder R.n q 0) ≤
        Real.exp (CE * (q : ℝ) ^ (2 * R.n + 3)) := by
  have hBd : (0 : ℝ) ≤ R.baseHouseBound d :=
    le_trans zero_le_one (R.one_le_baseHouseBound d)
  refine ⟨(1 + |(d : ℝ)|) * R.n + 1 + R.n + 2 + R.baseHouseBound d * R.n, by positivity, ?_⟩
  have hG := eventually_const_pow_le_exp
    (5 * (1 + |(c : ℝ)|) * (1 + R.eigenCoordinateHouseSum c)) (4 * R.n + 2)
  have hT := eventually_const_pow_le_exp (1 : ℝ) (2 * R.n + 2)
  have hS := eventually_const_pow_le_exp (2 : ℝ) 2
  filter_upwards [hG, hT, hS, eventually_ge_atTop 1] with q hGq hTq hSq hq1
  have hq1R : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq1
  have hqpow : ∀ j : ℕ, (1 : ℝ) ≤ (q : ℝ) ^ j := fun j => one_le_pow₀ hq1R
  have hd1 : (1 : ℝ) ≤ 1 + |(d : ℝ)| := by have := abs_nonneg ((d : ℝ)); linarith
  have hGle : R.jetGrowthBase c (additiveWidth R.n q) (exponentWidth R.n q) ≤ Real.exp q :=
    le_trans (jetGrowthBase_stage_le R c hq1) hGq
  have hG0 : (0 : ℝ) ≤ R.jetGrowthBase c (additiveWidth R.n q) (exponentWidth R.n q) :=
    le_trans zero_le_one (R.one_le_jetGrowthBase _ _ _)
  have hTle : ((stageOrder R.n q 0 : ℕ) : ℝ) ≤ Real.exp q := by
    rw [stageOrder_zero]
    push_cast
    simpa using hTq
  have hSle : 1 + ((stageSampleCount q 0 : ℕ) : ℝ) ≤ Real.exp q := by
    rw [stageSampleCount_cast]
    refine le_trans ?_ hSq
    have hz : (q : ℝ) ^ (0 + 2) = (q : ℝ) ^ 2 := by norm_num
    rw [hz]
    nlinarith [hqpow 2]
  have hexp1 : (1 + |(d : ℝ)|) ^ (stageSampleCount q 0 * (R.n * exponentWidth R.n q)) ≤
      Real.exp ((1 + |(d : ℝ)|) *
        ((stageSampleCount q 0 * (R.n * exponentWidth R.n q) : ℕ) : ℝ)) :=
    pow_le_exp_mul (by linarith) le_exp_self _
  have hexp2 : R.jetGrowthBase c (additiveWidth R.n q) (exponentWidth R.n q) ^
      (R.n * stageOrder R.n q 0) ≤
      Real.exp ((q : ℝ) * ((R.n * stageOrder R.n q 0 : ℕ) : ℝ)) :=
    pow_le_exp_mul hG0 hGle _
  have hexp3 : (1 + ((stageSampleCount q 0 : ℕ) : ℝ)) ^ (additiveWidth R.n q) ≤
      Real.exp ((q : ℝ) * ((additiveWidth R.n q : ℕ) : ℝ)) :=
    pow_le_exp_mul (by positivity) hSle _
  have hexp4 : R.baseHouseBound d ^ (R.n * exponentWidth R.n q * stageSampleCount q 0) ≤
      Real.exp (R.baseHouseBound d *
        ((R.n * exponentWidth R.n q * stageSampleCount q 0 : ℕ) : ℝ)) :=
    pow_le_exp_mul hBd le_exp_self _
  unfold _root_.GaloisForLFunctions.RHTower.BakerGeneralProof.SolvedRelation.auxiliaryEntryScalarBound
  calc
    (1 + |(d : ℝ)|) ^ (stageSampleCount q 0 * (R.n * exponentWidth R.n q)) *
        (((stageOrder R.n q 0 : ℕ) : ℝ) *
          R.jetGrowthBase c (additiveWidth R.n q) (exponentWidth R.n q) ^
            (R.n * stageOrder R.n q 0) *
          (1 + ((stageSampleCount q 0 : ℕ) : ℝ)) ^ (additiveWidth R.n q)) *
        R.baseHouseBound d ^ (R.n * exponentWidth R.n q * stageSampleCount q 0) ≤
        Real.exp ((1 + |(d : ℝ)|) *
            ((stageSampleCount q 0 * (R.n * exponentWidth R.n q) : ℕ) : ℝ)) *
          (Real.exp q * Real.exp ((q : ℝ) * ((R.n * stageOrder R.n q 0 : ℕ) : ℝ)) *
            Real.exp ((q : ℝ) * ((additiveWidth R.n q : ℕ) : ℝ))) *
          Real.exp (R.baseHouseBound d *
            ((R.n * exponentWidth R.n q * stageSampleCount q 0 : ℕ) : ℝ)) := by
      gcongr
    _ = Real.exp ((1 + |(d : ℝ)|) *
            ((stageSampleCount q 0 * (R.n * exponentWidth R.n q) : ℕ) : ℝ) +
          ((q : ℝ) + (q : ℝ) * ((R.n * stageOrder R.n q 0 : ℕ) : ℝ) +
            (q : ℝ) * ((additiveWidth R.n q : ℕ) : ℝ)) +
          R.baseHouseBound d *
            ((R.n * exponentWidth R.n q * stageSampleCount q 0 : ℕ) : ℝ)) := by
      simp only [← Real.exp_add]
    _ ≤ Real.exp (((1 + |(d : ℝ)|) * R.n + 1 + R.n + 2 + R.baseHouseBound d * R.n) *
          (q : ℝ) ^ (2 * R.n + 3)) := by
      refine Real.exp_le_exp.mpr ?_
      rw [entryExponent_cast, orderExponent_cast, additiveWidth_cast, entryExponent_cast']
      have hpowsucc : (q : ℝ) * (q : ℝ) ^ (2 * R.n + 2) = (q : ℝ) ^ (2 * R.n + 3) := by
        rw [← pow_succ']
      have hqle : (q : ℝ) ^ (2 * R.n + 2) ≤ (q : ℝ) ^ (2 * R.n + 3) :=
        pow_le_pow_right₀ hq1R (by omega)
      have hq : (q : ℝ) ≤ (q : ℝ) ^ (2 * R.n + 3) := by
        simpa using pow_le_pow_right₀ hq1R (show 1 ≤ 2 * R.n + 3 by omega)
      have hn0 : (0 : ℝ) ≤ (R.n : ℝ) := Nat.cast_nonneg _
      have hkey : (q : ℝ) * ((R.n : ℝ) * (q : ℝ) ^ (2 * R.n + 2)) =
          (R.n : ℝ) * (q : ℝ) ^ (2 * R.n + 3) := by
        rw [← hpowsucc]; ring
      have hkey2 : (q : ℝ) * (2 * (q : ℝ) ^ (2 * R.n + 2)) =
          2 * (q : ℝ) ^ (2 * R.n + 3) := by
        rw [← hpowsucc]; ring
      rw [hkey, hkey2]
      have hsub : (0 : ℝ) ≤ (q : ℝ) ^ (2 * R.n + 3) - (q : ℝ) ^ (2 * R.n + 2) := by linarith
      have hA : 0 ≤ (1 + |(d : ℝ)|) * (R.n : ℝ) *
          ((q : ℝ) ^ (2 * R.n + 3) - (q : ℝ) ^ (2 * R.n + 2)) :=
        mul_nonneg (mul_nonneg (by linarith) hn0) hsub
      have hB : 0 ≤ R.baseHouseBound d * (R.n : ℝ) *
          ((q : ℝ) ^ (2 * R.n + 3) - (q : ℝ) ^ (2 * R.n + 2)) :=
        mul_nonneg (mul_nonneg hBd hn0) hsub
      nlinarith [hA, hB, hq]

theorem exists_eventually_coefficientBudget_le_exp
    (R : SolvedRelation) (c d : ℤ)
    (hcomp : ∀ dir, IsIntegral ℤ (R.scaledComponentCoeff c dir))
    (hbase : ∀ i, IsIntegral ℤ (R.scaledBase d i)) :
    ∃ CH : ℝ, 0 ≤ CH ∧ ∀ᶠ q : ℕ in atTop,
      R.coefficientBudget c d hcomp hbase (additiveWidth R.n q) (exponentWidth R.n q)
        (stageSampleCount q 0) (stageOrder R.n q 0) ≤
        Real.exp (CH * (q : ℝ) ^ (2 * R.n + 3)) := by
  obtain ⟨CE, hCE0, hCE⟩ := exists_eventually_entryScalarBound_le_exp R c d
  have hc1 : (1 : ℝ) ≤ GelfondSchneiderSiegel.c₁ R.CoefficientField :=
    one_le_siegelConstant R.CoefficientField
  refine ⟨2 * GelfondSchneiderSiegel.c₁ R.CoefficientField + 2 + CE, by linarith, ?_⟩
  have hcols := eventually_const_pow_le_exp (2 : ℝ) (2 * R.n * R.n + 2 * R.n + 2)
  have hprod := eventually_const_pow_le_exp (2 : ℝ)
    ((2 * R.n * R.n + 2 * R.n + 2) + (2 * R.n * R.n + 2 * R.n + 2))
  filter_upwards [hCE, hcols, hprod, eventually_ge_atTop 1] with q hCEq hcolsq hprodq hq1
  have hq1R : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq1
  have hqpow : ∀ j : ℕ, (1 : ℝ) ≤ (q : ℝ) ^ j := fun j => one_le_pow₀ hq1R
  have hU1 : 1 ≤ additiveWidth R.n q := one_le_additiveWidth hq1
  have hT1 : 1 ≤ stageOrder R.n q 0 := by
    rw [stageOrder_zero]
    exact Nat.one_le_pow _ _ hq1
  have hUV : ((additiveWidth R.n q * exponentWidth R.n q ^ R.n : ℕ) : ℝ) ≤ Real.exp q := by
    rw [columnCount_cast]
    exact hcolsq
  have hRC : (((stageSampleCount q 0 * stageOrder R.n q 0 ^ R.n) *
      (additiveWidth R.n q * exponentWidth R.n q ^ R.n) : ℕ) : ℝ) ≤ Real.exp q := by
    have hc : (((stageSampleCount q 0 * stageOrder R.n q 0 ^ R.n) *
        (additiveWidth R.n q * exponentWidth R.n q ^ R.n) : ℕ) : ℝ) =
        2 * (q : ℝ) ^ ((2 * R.n * R.n + 2 * R.n + 2) + (2 * R.n * R.n + 2 * R.n + 2)) := by
      rw [Nat.cast_mul, rowCount_cast, columnCount_cast, pow_add]
      ring
    rw [hc]
    exact hprodq
  have hEB0 : 0 ≤ R.auxiliaryEntryScalarBound c d (additiveWidth R.n q) (exponentWidth R.n q)
      (stageSampleCount q 0) (stageOrder R.n q 0) :=
    R.auxiliaryEntryScalarBound_nonneg c d _ _ _ _
  have hHeight := R.polynomialAuxiliaryHeight_le c d hcomp hbase
    (V := exponentWidth R.n q) (S := stageSampleCount q 0) hU1 hT1
  have hHeight0 := R.polynomialAuxiliaryHeight_nonneg c d hcomp hbase
    (additiveWidth R.n q) (exponentWidth R.n q) (stageSampleCount q 0) (stageOrder R.n q 0)
  have hHexp : R.polynomialAuxiliaryHeight c d hcomp hbase (additiveWidth R.n q)
      (exponentWidth R.n q) (stageSampleCount q 0) (stageOrder R.n q 0) ≤
      Real.exp q * Real.exp (CE * (q : ℝ) ^ (2 * R.n + 3)) := by
    refine hHeight.trans ?_
    exact mul_le_mul hRC hCEq hEB0 (Real.exp_nonneg _)
  unfold _root_.GaloisForLFunctions.RHTower.BakerGeneralProof.SolvedRelation.coefficientBudget
  calc
    GelfondSchneiderSiegel.c₁ R.CoefficientField *
        (GelfondSchneiderSiegel.c₁ R.CoefficientField *
          ((additiveWidth R.n q * exponentWidth R.n q ^ R.n : ℕ) : ℝ) *
          R.polynomialAuxiliaryHeight c d hcomp hbase (additiveWidth R.n q)
            (exponentWidth R.n q) (stageSampleCount q 0) (stageOrder R.n q 0)) ≤
        Real.exp (GelfondSchneiderSiegel.c₁ R.CoefficientField) *
          (Real.exp (GelfondSchneiderSiegel.c₁ R.CoefficientField) * Real.exp q *
            (Real.exp q * Real.exp (CE * (q : ℝ) ^ (2 * R.n + 3)))) := by
      gcongr <;> exact le_exp_self
    _ = Real.exp (GelfondSchneiderSiegel.c₁ R.CoefficientField +
          (GelfondSchneiderSiegel.c₁ R.CoefficientField + (q : ℝ) +
            ((q : ℝ) + CE * (q : ℝ) ^ (2 * R.n + 3)))) := by
      simp only [← Real.exp_add]
    _ ≤ Real.exp ((2 * GelfondSchneiderSiegel.c₁ R.CoefficientField + 2 + CE) *
          (q : ℝ) ^ (2 * R.n + 3)) := by
      refine Real.exp_le_exp.mpr ?_
      have hq : (q : ℝ) ≤ (q : ℝ) ^ (2 * R.n + 3) := by
        simpa using pow_le_pow_right₀ hq1R (show 1 ≤ 2 * R.n + 3 by omega)
      nlinarith [hqpow (2 * R.n + 3)]

end GeneralParameters

end GaloisForLFunctions.RHTower.BakerGeneralProof
