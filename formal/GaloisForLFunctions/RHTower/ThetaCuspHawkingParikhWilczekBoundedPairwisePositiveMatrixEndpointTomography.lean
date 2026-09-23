import GaloisForLFunctions.RHTower.ThetaCuspHawkingParikhWilczekBoundedPacketCountableTomography
import GaloisForLFunctions.HTGeometry.TwoChannelRelativeCapacityNoGo
import GaloisForLFunctions.HTGeometry.AntidiagonalRegrouping
import GaloisForLFunctions.HTGeometry.BesselOrderFactorialGrowth

/-!
# Bounded pairwise-positive PW matrix endpoint tomography

The corpus contains nonzero positive-semidefinite countable grade matrices which are invisible to
the three affine Borel moments.  Literal endpoint winding defeats the known examples.  This module
closes the entire bounded positive matrix class.

For a bounded symmetric kernel `K`, its endpoint energy is the absolutely convergent double series

`sum_(i,j) K i j q^(i+j+2)`

at the prescribed physical nodes `q_j = exp(-(j+1))`.  Regrouping by total grade gives
antidiagonal coefficients of at most linear growth.  Dividing the degree-`n` coefficient by `2^n`
reduces all-scale darkness to the existing bounded power-series tomography theorem.  Positivity is
then decisive: the even antidiagonal of total grade `2m` exposes `K m m`, and a zero diagonal of a
symmetric pairwise-positive kernel annihilates its complete row.

Hence every nonzero bounded symmetric pairwise-positive kernel is detected at some literal
physical endpoint scale.  In particular, bounded PSD and bounded Gram matrix completions cannot be
the missing PW-B balance producer.  A survivor must be indefinite, unbounded/singular, or leave
the pointwise quadratic endpoint-energy framework.

`[NEW] [PW-B ROUTE-CLASS NO-GO] [COUNTABLE MATRIX TOMOGRAPHY]
[PAIRWISE POSITIVITY] [LEAN-PROVED]`
-/

open Filter Topology
open scoped BigOperators

namespace RHTower

noncomputable section

open GaloisForLFunctions.HTGeometry

/-- Total-grade coefficient obtained by summing a countable PW matrix on one antidiagonal. -/
def pwMatrixEndpointAntidiagonalCoefficient
    (K : ℕ → ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (n + 1), K i (n - i)

/-- Dyadically rescaled antidiagonal coefficient; bounded kernels give bounded coefficients. -/
def pwMatrixEndpointScaledCoefficient
    (K : ℕ → ℕ → ℝ) (n : ℕ) : ℝ :=
  pwMatrixEndpointAntidiagonalCoefficient K n / (2 : ℝ) ^ n

/-- Antidiagonal form of the bounded countable matrix endpoint-winding energy. -/
def schwarzschildParikhWilczekBoundedMatrixEndpointEnergy
    (K : ℕ → ℕ → ℝ) (j : ℕ) : ℝ :=
  ∑' n : ℕ, pwMatrixEndpointAntidiagonalCoefficient K n *
    schwarzschildParikhWilczekEndpointTomographyNode j ^ (n + 2)

/-- Literal ordered-pair form of the bounded countable matrix endpoint-winding energy. -/
def schwarzschildParikhWilczekLiteralBoundedMatrixEndpointEnergy
    (K : ℕ → ℕ → ℝ) (j : ℕ) : ℝ :=
  ∑' p : ℕ × ℕ, K p.1 p.2 *
    schwarzschildParikhWilczekEndpointTomographyNode j ^ (p.1 + p.2 + 2)

/-- Physical endpoint node after the dyadic coefficient rescaling. -/
def pwMatrixEndpointRescaledNode (j : ℕ) : ℝ :=
  2 * schwarzschildParikhWilczekEndpointTomographyNode j

/-- A uniformly bounded matrix has at most linearly growing antidiagonal coefficients. -/
theorem abs_pwMatrixEndpointAntidiagonalCoefficient_le
    {K : ℕ → ℕ → ℝ} {B : ℝ} (hK : ∀ i j, |K i j| ≤ B) (n : ℕ) :
    |pwMatrixEndpointAntidiagonalCoefficient K n| ≤ ((n : ℝ) + 1) * B := by
  rw [pwMatrixEndpointAntidiagonalCoefficient]
  calc
    |∑ i ∈ Finset.range (n + 1), K i (n - i)| ≤
        ∑ i ∈ Finset.range (n + 1), |K i (n - i)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ Finset.range (n + 1), B := by
      exact Finset.sum_le_sum fun i _ => hK i (n - i)
    _ = ((n : ℝ) + 1) * B := by
      simp [Nat.cast_add, Nat.cast_one]

/-- Dyadic rescaling absorbs the linear antidiagonal-cardinality loss. -/
theorem abs_pwMatrixEndpointScaledCoefficient_le
    {K : ℕ → ℕ → ℝ} {B : ℝ} (hB : 0 ≤ B)
    (hK : ∀ i j, |K i j| ≤ B) (n : ℕ) :
    |pwMatrixEndpointScaledCoefficient K n| ≤ B := by
  have hcoeff := abs_pwMatrixEndpointAntidiagonalCoefficient_le hK n
  have hpowpos : 0 < (2 : ℝ) ^ n := by positivity
  have hsucc := natCast_succ_le_two_pow n
  rw [pwMatrixEndpointScaledCoefficient, abs_div, abs_pow,
    abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  apply (div_le_iff₀ hpowpos).2
  calc
    |pwMatrixEndpointAntidiagonalCoefficient K n| ≤ ((n : ℝ) + 1) * B := hcoeff
    _ ≤ B * (2 : ℝ) ^ n := by
      nlinarith

private theorem sum_nat_antidiagonal_eq_range_real
    (F : ℕ × ℕ → ℝ) (n : ℕ) :
    (∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, F p) =
      ∑ i ∈ Finset.range (n + 1), F (i, n - i) := by
  let e : ℕ ↪ ℕ × ℕ :=
    ⟨fun i => (i, n - i), fun a b h => by simpa using congrArg Prod.fst h⟩
  have heq : Finset.HasAntidiagonal.antidiagonal n =
      (Finset.range (n + 1)).map e := by
    ext p
    rw [Finset.HasAntidiagonal.mem_antidiagonal]
    simp only [Finset.mem_map, Finset.mem_range]
    constructor
    · intro hp
      refine ⟨p.1, by omega, ?_⟩
      apply Prod.ext
      · rfl
      · dsimp [e]
        omega
    · rintro ⟨i, hi, rfl⟩
      dsimp [e]
      omega
  rw [heq, Finset.sum_map]
  rfl

/-- Every rescaled physical endpoint node is positive. -/
theorem pwMatrixEndpointRescaledNode_pos (j : ℕ) :
    0 < pwMatrixEndpointRescaledNode j := by
  rw [pwMatrixEndpointRescaledNode, schwarzschildParikhWilczekEndpointTomographyNode]
  exact mul_pos (by norm_num) (Real.exp_pos _)

/-- Every rescaled physical endpoint node remains strictly inside the unit disk. -/
theorem abs_pwMatrixEndpointRescaledNode_lt_one (j : ℕ) :
    |pwMatrixEndpointRescaledNode j| < 1 := by
  rw [abs_of_pos (pwMatrixEndpointRescaledNode_pos j), pwMatrixEndpointRescaledNode,
    schwarzschildParikhWilczekEndpointTomographyNode]
  have harg : -((j : ℝ) + 1) ≤ -(1 : ℝ) := by
    have hj : 0 ≤ (j : ℝ) := Nat.cast_nonneg j
    linarith
  have hexp : 2 < Real.exp 1 := by
    have h := Real.add_one_lt_exp (by norm_num : (1 : ℝ) ≠ 0)
    norm_num at h
    exact h
  calc
    2 * Real.exp (-((j : ℝ) + 1)) ≤ 2 * Real.exp (-1) := by
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr harg) (by norm_num)
    _ = 2 / Real.exp 1 := by rw [Real.exp_neg]; ring
    _ < 1 := (div_lt_one (Real.exp_pos 1)).2 hexp

/-- Rescaled physical endpoint nodes converge to the interior accumulation point zero. -/
theorem tendsto_pwMatrixEndpointRescaledNode_zero :
    Tendsto pwMatrixEndpointRescaledNode atTop (𝓝 0) := by
  change Tendsto
    (fun j => 2 * schwarzschildParikhWilczekEndpointTomographyNode j) atTop (𝓝 0)
  simpa using
    (tendsto_const_nhds.mul tendsto_schwarzschildParikhWilczekEndpointTomographyNode_zero)

/-- Uniform boundedness gives absolute convergence of the literal ordered-pair endpoint energy. -/
theorem summable_schwarzschildParikhWilczekLiteralBoundedMatrixEndpointEnergy
    {K : ℕ → ℕ → ℝ} {B : ℝ} (hK : ∀ i j, |K i j| ≤ B) (j : ℕ) :
    Summable fun p : ℕ × ℕ => K p.1 p.2 *
      schwarzschildParikhWilczekEndpointTomographyNode j ^ (p.1 + p.2 + 2) := by
  let q := schwarzschildParikhWilczekEndpointTomographyNode j
  have hq0 : 0 < q := Real.exp_pos _
  have hq1 : q < 1 := by
    change Real.exp (-((j : ℝ) + 1)) < 1
    rw [Real.exp_lt_one_iff]
    have hj : 0 ≤ (j : ℝ) := Nat.cast_nonneg j
    linarith
  have hgeo : Summable fun n : ℕ => q ^ n :=
    summable_geometric_of_lt_one hq0.le hq1
  have hprod : Summable fun p : ℕ × ℕ => q ^ p.1 * q ^ p.2 :=
    summable_mul_of_summable_norm hgeo.norm hgeo.norm
  have hmajor : Summable fun p : ℕ × ℕ => B * q ^ (p.1 + p.2 + 2) := by
    refine (hprod.mul_left (B * q ^ (2 : ℕ))).congr fun p => ?_
    rw [pow_add, pow_add]
    ring
  refine Summable.of_norm_bounded hmajor ?_
  intro p
  rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_pos hq0]
  exact mul_le_mul_of_nonneg_right (hK p.1 p.2) (pow_nonneg hq0.le _)

/-- Antidiagonal regrouping equals the literal absolutely convergent double matrix energy. -/
theorem schwarzschildParikhWilczekBoundedMatrixEndpointEnergy_eq_literal
    {K : ℕ → ℕ → ℝ} {B : ℝ} (hK : ∀ i j, |K i j| ≤ B) (j : ℕ) :
    schwarzschildParikhWilczekBoundedMatrixEndpointEnergy K j =
      schwarzschildParikhWilczekLiteralBoundedMatrixEndpointEnergy K j := by
  let q := schwarzschildParikhWilczekEndpointTomographyNode j
  let T : ℕ × ℕ → ℝ := fun p => K p.1 p.2 * q ^ (p.1 + p.2 + 2)
  have hT : Summable T :=
    summable_schwarzschildParikhWilczekLiteralBoundedMatrixEndpointEnergy hK j
  rw [schwarzschildParikhWilczekBoundedMatrixEndpointEnergy,
    schwarzschildParikhWilczekLiteralBoundedMatrixEndpointEnergy]
  change (∑' n : ℕ, pwMatrixEndpointAntidiagonalCoefficient K n * q ^ (n + 2)) =
    ∑' p : ℕ × ℕ, T p
  rw [← tsum_sum_antidiagonal hT]
  apply tsum_congr
  intro n
  rw [pwMatrixEndpointAntidiagonalCoefficient]
  have hanti :
      (∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, K p.1 p.2) =
        ∑ i ∈ Finset.range (n + 1), K i (n - i) := by
    simpa using sum_nat_antidiagonal_eq_range_real (fun p => K p.1 p.2) n
  rw [← hanti]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro p hp
  have hpadd := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
  change K p.1 p.2 * q ^ (n + 2) = K p.1 p.2 * q ^ (p.1 + p.2 + 2)
  rw [hpadd]

/-- Matrix endpoint energy is a bounded-coefficient power series at the rescaled nodes. -/
theorem schwarzschildParikhWilczekBoundedMatrixEndpointEnergy_eq_scaled
    {K : ℕ → ℕ → ℝ} {B : ℝ} (hB : 0 ≤ B)
    (hK : ∀ i j, |K i j| ≤ B) (j : ℕ) :
    schwarzschildParikhWilczekBoundedMatrixEndpointEnergy K j =
      schwarzschildParikhWilczekEndpointTomographyNode j ^ (2 : ℕ) *
        ∑' n : ℕ, pwMatrixEndpointScaledCoefficient K n *
          pwMatrixEndpointRescaledNode j ^ n := by
  let q := schwarzschildParikhWilczekEndpointTomographyNode j
  let r := pwMatrixEndpointRescaledNode j
  have hb : ∀ n, |pwMatrixEndpointScaledCoefficient K n| ≤ B :=
    abs_pwMatrixEndpointScaledCoefficient_le hB hK
  have hsum : Summable fun n : ℕ =>
      pwMatrixEndpointScaledCoefficient K n * r ^ n :=
    GaloisForLFunctions.HTGeometry.summable_of_bounded_coeff hb
      (abs_pwMatrixEndpointRescaledNode_lt_one j)
  rw [schwarzschildParikhWilczekBoundedMatrixEndpointEnergy, ← tsum_mul_left]
  apply tsum_congr
  intro n
  rw [pwMatrixEndpointScaledCoefficient, pwMatrixEndpointRescaledNode]
  have hpow : (2 : ℝ) ^ n ≠ 0 := by positivity
  field_simp
  ring

/-- All-scale endpoint darkness kills every antidiagonal coefficient of a bounded kernel. -/
theorem pwMatrixEndpointAntidiagonalCoefficient_eq_zero_of_energy_zero
    {K : ℕ → ℕ → ℝ} {B : ℝ} (hB : 0 ≤ B)
    (hK : ∀ i j, |K i j| ≤ B)
    (hzero : ∀ j : ℕ, schwarzschildParikhWilczekBoundedMatrixEndpointEnergy K j = 0) :
    ∀ n, pwMatrixEndpointAntidiagonalCoefficient K n = 0 := by
  have hb : ∀ n, |pwMatrixEndpointScaledCoefficient K n| ≤ B :=
    abs_pwMatrixEndpointScaledCoefficient_le hB hK
  have hrzero : ∀ j : ℕ, ∑' n : ℕ,
      pwMatrixEndpointScaledCoefficient K n * pwMatrixEndpointRescaledNode j ^ n = 0 := by
    intro j
    have h := hzero j
    rw [schwarzschildParikhWilczekBoundedMatrixEndpointEnergy_eq_scaled hB hK] at h
    exact (mul_eq_zero.mp h).resolve_left
      (pow_ne_zero 2 (ne_of_gt (Real.exp_pos _)))
  have hbzero : ∀ n, pwMatrixEndpointScaledCoefficient K n = 0 :=
    boundedPowerSeries_coeff_eq_zero_of_zeroSequence hb
      pwMatrixEndpointRescaledNode_pos abs_pwMatrixEndpointRescaledNode_lt_one
      tendsto_pwMatrixEndpointRescaledNode_zero hrzero
  intro n
  calc
    pwMatrixEndpointAntidiagonalCoefficient K n =
        pwMatrixEndpointScaledCoefficient K n * (2 : ℝ) ^ n := by
      rw [pwMatrixEndpointScaledCoefficient]
      field_simp
    _ = 0 := by rw [hbzero n, zero_mul]

/-- A bounded symmetric pairwise-positive kernel dark at every endpoint scale is zero. -/
theorem bounded_symmetric_pairwisePositive_kernel_eq_zero_of_endpointEnergy_zero
    {K : ℕ → ℕ → ℝ} {B : ℝ} (hB : 0 ≤ B)
    (hK : ∀ i j, |K i j| ≤ B)
    (hSymm : ∀ i j, K i j = K j i)
    (hPositive : PairwiseNonnegativeKernel K)
    (hzero : ∀ j : ℕ, schwarzschildParikhWilczekBoundedMatrixEndpointEnergy K j = 0) :
    K = 0 := by
  have ha : ∀ n, pwMatrixEndpointAntidiagonalCoefficient K n = 0 :=
    pwMatrixEndpointAntidiagonalCoefficient_eq_zero_of_energy_zero hB hK hzero
  have hrows : ∀ m i, K m i = 0 := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      have hsum := ha (2 * m)
      rw [pwMatrixEndpointAntidiagonalCoefficient] at hsum
      have hsingle :
          (∑ i ∈ Finset.range (2 * m + 1), K i (2 * m - i)) = K m m := by
        calc
          (∑ i ∈ Finset.range (2 * m + 1), K i (2 * m - i)) =
              K m (2 * m - m) := by
            apply Finset.sum_eq_single m
            · intro i hi him
              simp only [Finset.mem_range] at hi
              by_cases hlt : i < m
              · exact ih i hlt (2 * m - i)
              · have hgt : m < i :=
                  lt_of_le_of_ne (Nat.le_of_not_gt hlt) (Ne.symm him)
                have hsub : 2 * m - i < m := by omega
                rw [hSymm]
                exact ih (2 * m - i) hsub i
            · intro hnot
              exfalso
              apply hnot
              simp
              omega
          _ = K m m := by congr 1; omega
      rw [hsingle] at hsum
      exact pairwiseNonnegativeKernel_row_eq_zero_of_symmetric_of_diagonal_eq_zero
        hPositive hSymm hsum
  funext i j
  exact hrows i j

/-- Complete antidiagonal endpoint tomography for bounded symmetric pairwise-positive matrices. -/
theorem schwarzschildParikhWilczekBoundedPairwisePositiveMatrixEndpointEnergy_eq_zero_iff
    {K : ℕ → ℕ → ℝ} {B : ℝ} (hB : 0 ≤ B)
    (hK : ∀ i j, |K i j| ≤ B)
    (hSymm : ∀ i j, K i j = K j i)
    (hPositive : PairwiseNonnegativeKernel K) :
    (∀ j : ℕ, schwarzschildParikhWilczekBoundedMatrixEndpointEnergy K j = 0) ↔
      K = 0 := by
  constructor
  · exact bounded_symmetric_pairwisePositive_kernel_eq_zero_of_endpointEnergy_zero
      hB hK hSymm hPositive
  · rintro rfl
    intro j
    simp [schwarzschildParikhWilczekBoundedMatrixEndpointEnergy,
      pwMatrixEndpointAntidiagonalCoefficient]

/-- Complete literal double-series endpoint tomography for bounded positive matrix histories. -/
theorem schwarzschildParikhWilczekLiteralBoundedPairwisePositiveMatrixEndpointEnergy_eq_zero_iff
    {K : ℕ → ℕ → ℝ} {B : ℝ} (hB : 0 ≤ B)
    (hK : ∀ i j, |K i j| ≤ B)
    (hSymm : ∀ i j, K i j = K j i)
    (hPositive : PairwiseNonnegativeKernel K) :
    (∀ j : ℕ, schwarzschildParikhWilczekLiteralBoundedMatrixEndpointEnergy K j = 0) ↔
      K = 0 := by
  constructor
  · intro hzero
    apply (schwarzschildParikhWilczekBoundedPairwisePositiveMatrixEndpointEnergy_eq_zero_iff
      hB hK hSymm hPositive).mp
    intro j
    rw [schwarzschildParikhWilczekBoundedMatrixEndpointEnergy_eq_literal hK]
    exact hzero j
  · rintro rfl
    intro j
    simp [schwarzschildParikhWilczekLiteralBoundedMatrixEndpointEnergy]

/-- **PW-B route-class kill.** Every nonzero bounded symmetric pairwise-positive countable matrix
history is detected by the literal physical endpoint channel at some prescribed scale. -/
theorem schwarzschildParikhWilczekBoundedPairwisePositiveMatrixEndpointDarkRouteKilled
    {K : ℕ → ℕ → ℝ} {B : ℝ} (hB : 0 ≤ B)
    (hK : ∀ i j, |K i j| ≤ B)
    (hSymm : ∀ i j, K i j = K j i)
    (hPositive : PairwiseNonnegativeKernel K) (hKne : K ≠ 0) :
    ∃ j : ℕ, schwarzschildParikhWilczekLiteralBoundedMatrixEndpointEnergy K j ≠ 0 := by
  by_contra h
  have hall : ∀ j : ℕ,
      schwarzschildParikhWilczekLiteralBoundedMatrixEndpointEnergy K j = 0 := by
    intro j
    by_contra hj
    exact h ⟨j, hj⟩
  exact hKne
    ((schwarzschildParikhWilczekLiteralBoundedPairwisePositiveMatrixEndpointEnergy_eq_zero_iff
      hB hK hSymm hPositive).mp hall)

end

end RHTower
