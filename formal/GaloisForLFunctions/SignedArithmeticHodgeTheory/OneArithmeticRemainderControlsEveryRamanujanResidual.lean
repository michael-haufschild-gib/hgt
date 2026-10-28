import GaloisForLFunctions.SignedArithmeticHodgeTheory.TheRamanujanCorrectionHasAnExplicitConductorCost

/-!
# One arithmetic remainder for every Ramanujan residual

The conductor dependence is explicit, while one Mertens and floor remainder
controls every horizon and every coefficient family in the literal prime matrix.
-/

noncomputable section

open Filter Topology Finset
open scoped BigOperators

namespace GaloisForLFunctions.SignedArithmeticHodgeTheory

open RenormalizedArithmeticPotentialTheory ArithmeticEffectivityTheory ArithmeticIntersectionTheory

/-- The common arithmetic error at a complementary quotient. -/
def primeMertensRemainderProfile (y : ℕ) : ℝ :=
  |mertensSum y - Real.log y + Real.eulerMascheroniConstant| + 1 / (y : ℝ)

/-- The conductor factor in the literal normalized prime-row residual. -/
def ramanujanResidualConductorCost (m : ℕ) : ℝ :=
  Real.sqrt (m.totient : ℝ) * (1 + 4 * Real.log m)

/-- The actual finite prime-matrix residual at the arithmetic adjunction energy. -/
def ramanujanPrimeResidual (m N n : ℕ) : ℝ :=
  (∑ j ∈ Icc 1 N, weilPrimeKernel n j * ramanujanPoleProfile m j) -
    (Real.log N - ramanujanAdjunctionEnergy m) * ramanujanPoleProfile m n

/-- One arithmetic budget, independent of all conductors and coefficients. -/
def primeMertensSquareBudget (N : ℕ) : ℝ :=
  ∑ n ∈ Icc 1 N, primeMertensRemainderProfile (N / n) ^ 2 / (n : ℝ)

private theorem abs_normalizedRamanujanMode_le_sqrt_totient {m : ℕ}
    (hm : 0 < m) (n : ℕ) :
    |normalizedRamanujanMode m n| ≤ Real.sqrt (m.totient : ℝ) := by
  have hφ : 0 < (m.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hm
  have hsqrt : Real.sqrt (m.totient : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hφ).ne'
  rw [normalizedRamanujanMode_eq_coefficient hm, abs_div,
    abs_of_nonneg (Real.sqrt_nonneg _)]
  calc
    _ ≤ (m.totient : ℝ) / Real.sqrt (m.totient : ℝ) :=
      div_le_div_of_nonneg_right
        (BiScaleUncertainty.SieveMoments.abs_ramanujanLagCoefficient_le_totient m n)
        (Real.sqrt_nonneg _)
    _ = _ := by
      apply (div_eq_iff hsqrt).mpr
      rw [← sq, Real.sq_sqrt hφ.le]

/-- Every conductor and row have the same Mertens/floor profile, with explicit cost. -/
theorem abs_ramanujanPrimeResidual_le {m N n : ℕ} (hm : 0 < m)
    (hn : n ∈ Icc 1 N) :
    |ramanujanPrimeResidual m N n| ≤
      ramanujanResidualConductorCost m * primeMertensRemainderProfile (N / n) /
        Real.sqrt n := by
  have hn0 : 0 < n := (mem_Icc.mp hn).1
  have hnN : n ≤ N := (mem_Icc.mp hn).2
  have hy : 0 < N / n := Nat.div_pos hnN hn0
  let e : ℕ → ℝ := fun y => mertensSum y - Real.log y + Real.eulerMascheroniConstant
  let r : ℝ := Real.log N - Real.log ((N / n : ℕ) : ℝ) - Real.log n
  have hr : 0 ≤ r ∧ r ≤ 1 / ((N / n : ℕ) : ℝ) := roundoff_le hn0 hnN
  have hid : ramanujanPrimeResidual m N n =
      ((e (N / n) - r) * normalizedRamanujanMode m n +
        (poleProfileCorrection (normalizedRamanujanMode m) (N / n) n +
          (Real.log m + tameDifferent m) * normalizedRamanujanMode m n)) * poleVector n := by
    rw [ramanujanPrimeResidual]
    simp only [ramanujanPoleProfile_eq_mul_poleVector]
    rw [sum_weilPrimeKernel_poleProfile_eq_correction (normalizedRamanujanMode m) hn0 hnN]
    dsimp only [e, r, ramanujanAdjunctionEnergy]
    ring
  have her : |e (N / n) - r| ≤ |e (N / n)| + 1 / ((N / n : ℕ) : ℝ) := by
    calc
      _ ≤ |e (N / n)| + |r| := abs_sub _ _
      _ ≤ _ := by
        rw [abs_of_nonneg hr.1]
        exact add_le_add le_rfl hr.2
  have hbracket :
      |(e (N / n) - r) * normalizedRamanujanMode m n +
        (poleProfileCorrection (normalizedRamanujanMode m) (N / n) n +
          (Real.log m + tameDifferent m) * normalizedRamanujanMode m n)| ≤
        ramanujanResidualConductorCost m * primeMertensRemainderProfile (N / n) := by
    calc
      _ ≤ |(e (N / n) - r) * normalizedRamanujanMode m n| +
          |poleProfileCorrection (normalizedRamanujanMode m) (N / n) n +
            (Real.log m + tameDifferent m) * normalizedRamanujanMode m n| := abs_add_le _ _
      _ ≤ (|e (N / n)| + 1 / ((N / n : ℕ) : ℝ)) * Real.sqrt (m.totient : ℝ) +
          4 * Real.sqrt (m.totient : ℝ) * Real.log m / ((N / n : ℕ) : ℝ) := by
        rw [abs_mul]
        exact add_le_add
          (mul_le_mul her (abs_normalizedRamanujanMode_le_sqrt_totient hm n)
            (abs_nonneg _) ((abs_nonneg _).trans her))
          (abs_normalizedRamanujan_correction_le hm hn0 hy)
      _ ≤ _ := by
        have hnonneg := mul_nonneg
          (mul_nonneg (Real.sqrt_nonneg (m.totient : ℝ)) (Real.log_natCast_nonneg m))
          (abs_nonneg (e (N / n)))
        change _ ≤ (Real.sqrt (m.totient : ℝ) * (1 + 4 * Real.log m)) *
          (|e (N / n)| + 1 / ((N / n : ℕ) : ℝ))
        nlinarith only [hnonneg]
  rw [hid, abs_mul, abs_of_nonneg (show 0 ≤ poleVector n by unfold poleVector; positivity)]
  calc
    _ ≤ (ramanujanResidualConductorCost m * primeMertensRemainderProfile (N / n)) *
        poleVector n := mul_le_mul_of_nonneg_right hbracket (by unfold poleVector; positivity)
    _ = _ := by unfold poleVector; ring

private theorem ramanujanPrimeResidual_sq_le {m N n : ℕ} (hm : 0 < m)
    (hn : n ∈ Icc 1 N) :
    ramanujanPrimeResidual m N n ^ 2 ≤
      ramanujanResidualConductorCost m ^ 2 * primeMertensRemainderProfile (N / n) ^ 2 /
        (n : ℝ) := by
  have h := abs_ramanujanPrimeResidual_le hm hn
  calc
    _ = |ramanujanPrimeResidual m N n| * |ramanujanPrimeResidual m N n| := by
      rw [← sq, sq_abs]
    _ ≤ (ramanujanResidualConductorCost m * primeMertensRemainderProfile (N / n) /
        Real.sqrt n) *
        (ramanujanResidualConductorCost m * primeMertensRemainderProfile (N / n) /
        Real.sqrt n) := mul_le_mul h h (abs_nonneg _) ((abs_nonneg _).trans h)
    _ = _ := by rw [← sq, div_pow, mul_pow, Real.sq_sqrt (Nat.cast_nonneg n)]

/-- A single arithmetic budget controls the whole growing residual operator. -/
theorem ramanujanPrimeResidual_family_sq_le (S : Finset ℕ+) (c : ℕ+ → ℝ) (N : ℕ) :
    (∑ n ∈ Icc 1 N, (∑ m ∈ S, c m * ramanujanPrimeResidual m N n) ^ 2) ≤
      (∑ m ∈ S, c m ^ 2) * (∑ m ∈ S, ramanujanResidualConductorCost m ^ 2) *
        primeMertensSquareBudget N := by
  have hc : 0 ≤ ∑ m ∈ S, c m ^ 2 := sum_nonneg fun m _ => sq_nonneg (c m)
  calc
    _ ≤ ∑ n ∈ Icc 1 N, (∑ m ∈ S, c m ^ 2) *
        ((∑ m ∈ S, ramanujanResidualConductorCost m ^ 2) *
          (primeMertensRemainderProfile (N / n) ^ 2 / (n : ℝ))) := by
      apply sum_le_sum
      intro n hn
      refine (Finset.sum_mul_sq_le_sq_mul_sq S c (fun m => ramanujanPrimeResidual m N n)).trans ?_
      apply mul_le_mul_of_nonneg_left ?_ hc
      calc
        _ ≤ ∑ m ∈ S, ramanujanResidualConductorCost m ^ 2 *
            primeMertensRemainderProfile (N / n) ^ 2 / (n : ℝ) := by
          exact sum_le_sum fun m _ =>
            ramanujanPrimeResidual_sq_le (m := (m : ℕ)) m.property hn
        _ = _ := by rw [← sum_div, ← sum_mul]; ring
    _ = _ := by
      simp only [primeMertensSquareBudget, mul_sum]
      apply sum_congr rfl
      intro n _
      ring

/-- The common remainder vanishes at large complementary quotients. -/
theorem tendsto_primeMertensRemainderProfile :
    Tendsto primeMertensRemainderProfile atTop (𝓝 0) := by
  have he : Tendsto
      (fun y : ℕ => mertensSum y - Real.log y + Real.eulerMascheroniConstant)
      atTop (𝓝 0) := by
    simpa only [neg_add_cancel] using
      tendsto_mertensSum_sub_log.add_const Real.eulerMascheroniConstant
  have hi := tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ)
  simpa only [primeMertensRemainderProfile, abs_zero, zero_add] using he.abs.add hi

/-- The same arithmetic budget is sublogarithmic, independently of the family. -/
theorem tendsto_primeMertensSquareBudget_div_log :
    Tendsto (fun N : ℕ => primeMertensSquareBudget N / Real.log N) atTop (𝓝 0) := by
  have hf : Tendsto (fun y => primeMertensRemainderProfile y ^ 2) atTop (𝓝 0) := by
    simpa only [zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using
      tendsto_primeMertensRemainderProfile.pow 2
  obtain ⟨C, hC⟩ := hf.abs.bddAbove_range
  have h := _root_.RHTower.tendsto_harmonicQuotientMean_div_log
    (fun y => primeMertensRemainderProfile y ^ 2) 0 C hf (fun y => hC ⟨y, rfl⟩)
  simpa only [primeMertensSquareBudget, _root_.RHTower.harmonicQuotientMean] using h

end GaloisForLFunctions.SignedArithmeticHodgeTheory

#print axioms GaloisForLFunctions.SignedArithmeticHodgeTheory.abs_ramanujanPrimeResidual_le
#print axioms GaloisForLFunctions.SignedArithmeticHodgeTheory.ramanujanPrimeResidual_family_sq_le
#print axioms GaloisForLFunctions.SignedArithmeticHodgeTheory.tendsto_primeMertensSquareBudget_div_log
