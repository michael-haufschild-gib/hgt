import GaloisForLFunctions.RHTower.Sieve.KloostermanDistinctModulusCompleteCorrelation

/-!
# Least-common-multiple completion for distinct-modulus Kloosterman columns

The product-period completion contains `gcd(q,r)` identical copies of the true common period.
This module removes that redundancy. Complete unequal-modulus correlations vanish already over
`lcm(q,r)`, and arbitrary intervals are exact lcm-period boundary remainders. The resulting
second-moment bound improves the product-period estimate by the full common-divisor factor.
-/

open scoped BigOperators ComplexConjugate
open Complex Finset

namespace RHTower.Sieve

noncomputable section

/-- Complete cross-modulus column correlation over the least common multiple period. -/
def kloostermanNaturalLcmPeriodCorrelation
    (q r : ℕ) [NeZero q] [NeZero r] (n : ZMod q) (k : ZMod r) : ℂ :=
  ∑ m ∈ Finset.range (Nat.lcm q r),
    kloostermanNaturalCrossColumnProductTerm q r n k m

/-- Cross-column products are periodic under every multiple of the common lcm period. -/
theorem kloostermanNaturalCrossColumnProductTerm_add_lcm_mul
    (q r : ℕ) [NeZero q] [NeZero r]
    (n : ZMod q) (k : ZMod r) (a j : ℕ) :
    kloostermanNaturalCrossColumnProductTerm q r n k
        (a + Nat.lcm q r * j) =
      kloostermanNaturalCrossColumnProductTerm q r n k a := by
  have hlq : ((Nat.lcm q r : ℕ) : ZMod q) = 0 := by
    rcases Nat.dvd_lcm_left q r with ⟨d, hd⟩
    rw [hd]
    push_cast
    rw [ZMod.natCast_self, zero_mul]
  have hlr : ((Nat.lcm q r : ℕ) : ZMod r) = 0 := by
    rcases Nat.dvd_lcm_right q r with ⟨d, hd⟩
    rw [hd]
    push_cast
    rw [ZMod.natCast_self, zero_mul]
  unfold kloostermanNaturalCrossColumnProductTerm
  push_cast
  simp [hlq, hlr]

/-- A product-period correlation is `gcd(q,r)` repeated least-common-multiple periods. -/
theorem kloostermanNaturalProductPeriodCorrelation_eq_gcd_mul_lcm
    (q r : ℕ) [NeZero q] [NeZero r]
    (n : ZMod q) (k : ZMod r) :
    kloostermanNaturalProductPeriodCorrelation q r n k =
      (Nat.gcd q r : ℂ) * kloostermanNaturalLcmPeriodCorrelation q r n k := by
  change (∑ m ∈ Finset.range (q * r),
      kloostermanNaturalCrossColumnProductTerm q r n k m) =
    (Nat.gcd q r : ℂ) * ∑ m ∈ Finset.range (Nat.lcm q r),
      kloostermanNaturalCrossColumnProductTerm q r n k m
  rw [← Nat.gcd_mul_lcm q r, ← Fin.sum_univ_eq_sum_range]
  let e : Fin (Nat.gcd q r) × Fin (Nat.lcm q r) ≃
      Fin (Nat.gcd q r * Nat.lcm q r) := finProdFinEquiv
  calc
    (∑ m : Fin (Nat.gcd q r * Nat.lcm q r),
        kloostermanNaturalCrossColumnProductTerm q r n k m.val) =
        ∑ p : Fin (Nat.gcd q r) × Fin (Nat.lcm q r),
          kloostermanNaturalCrossColumnProductTerm q r n k
            (p.2.val + Nat.lcm q r * p.1.val) := by
      rw [show (∑ m : Fin (Nat.gcd q r * Nat.lcm q r),
          kloostermanNaturalCrossColumnProductTerm q r n k m.val) =
          ∑ p : Fin (Nat.gcd q r) × Fin (Nat.lcm q r),
            kloostermanNaturalCrossColumnProductTerm q r n k (e p).val from
        (e.sum_comp (fun m : Fin (Nat.gcd q r * Nat.lcm q r) =>
          kloostermanNaturalCrossColumnProductTerm q r n k m.val)).symm]
      apply Fintype.sum_congr
      intro p
      simp [e, finProdFinEquiv]
    _ = ∑ _j : Fin (Nat.gcd q r), ∑ a : Fin (Nat.lcm q r),
          kloostermanNaturalCrossColumnProductTerm q r n k a.val := by
      rw [Fintype.sum_prod_type]
      apply Fintype.sum_congr
      intro j
      apply Fintype.sum_congr
      intro a
      exact kloostermanNaturalCrossColumnProductTerm_add_lcm_mul
        q r n k a.val j.val
    _ = (Nat.gcd q r : ℂ) *
        ∑ m ∈ Finset.range (Nat.lcm q r),
          kloostermanNaturalCrossColumnProductTerm q r n k m := by
      rw [← Fin.sum_univ_eq_sum_range]
      simp

/-- Complete Kloosterman columns of unequal moduli are orthogonal over their least common
multiple period. -/
theorem kloostermanNaturalLcmPeriodCorrelation_eq_zero_of_ne
    (q r : ℕ) [NeZero q] [NeZero r] (hqr : q ≠ r)
    (n : ZMod q) (k : ZMod r) :
    kloostermanNaturalLcmPeriodCorrelation q r n k = 0 := by
  have hzero := kloostermanNaturalProductPeriodCorrelation_eq_zero_of_ne
    q r hqr n k
  rw [kloostermanNaturalProductPeriodCorrelation_eq_gcd_mul_lcm] at hzero
  have hgpos : 0 < Nat.gcd q r :=
    Nat.gcd_pos_of_pos_left r (Nat.pos_of_ne_zero (NeZero.ne q))
  have hg : (Nat.gcd q r : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hgpos)
  exact (mul_eq_zero.mp hzero).resolve_left hg

/-- Least-common-multiple residue discrepancy for an incomplete cross correlation. -/
def kloostermanNaturalCrossIntervalLcmRemainder
    (M q r : ℕ) [NeZero q] [NeZero r]
    (n : ZMod q) (k : ZMod r) : ℂ :=
  ∑ s ∈ Finset.range (Nat.lcm q r),
    (kloostermanResidueDeviation M (Nat.lcm q r) s : ℂ) *
      kloostermanNaturalCrossColumnProductTerm q r n k s

private theorem natCast_mod_lcm_eq_natCast_left
    (m q r : ℕ) [NeZero q] :
    ((m % Nat.lcm q r : ℕ) : ZMod q) = (m : ZMod q) := by
  apply (ZMod.natCast_eq_natCast_iff (m % Nat.lcm q r) m q).mpr
  exact Nat.mod_mod_of_dvd m (Nat.dvd_lcm_left q r)

private theorem natCast_mod_lcm_eq_natCast_right
    (m q r : ℕ) [NeZero r] :
    ((m % Nat.lcm q r : ℕ) : ZMod r) = (m : ZMod r) := by
  apply (ZMod.natCast_eq_natCast_iff (m % Nat.lcm q r) m r).mpr
  exact Nat.mod_mod_of_dvd m (Nat.dvd_lcm_right q r)

/-- Exact grouping of a cross-modulus interval correlation by lcm-period residue. -/
theorem kloostermanNaturalCrossIntervalCorrelation_eq_lcmResidueMultiplicity
    (M q r : ℕ) [NeZero q] [NeZero r]
    (n : ZMod q) (k : ZMod r) :
    kloostermanNaturalCrossIntervalCorrelation M q r n k =
      ∑ s ∈ Finset.range (Nat.lcm q r),
        (kloostermanResidueMultiplicity M (Nat.lcm q r) s : ℂ) *
          kloostermanNaturalCrossColumnProductTerm q r n k s := by
  classical
  unfold kloostermanNaturalCrossIntervalCorrelation kloostermanResidueMultiplicity
  calc
    (∑ m ∈ Finset.Icc 1 M, kloostermanNaturalCrossColumnProductTerm q r n k m) =
        ∑ m ∈ Finset.Icc 1 M, ∑ s ∈ Finset.range (Nat.lcm q r),
          if s = m % Nat.lcm q r then
            kloostermanNaturalCrossColumnProductTerm q r n k s else 0 := by
      apply Finset.sum_congr rfl
      intro m hm
      rw [Finset.sum_ite_eq' (Finset.range (Nat.lcm q r))]
      have hp : 0 < Nat.lcm q r := Nat.lcm_pos
        (Nat.pos_of_ne_zero (NeZero.ne q)) (Nat.pos_of_ne_zero (NeZero.ne r))
      rw [if_pos (Finset.mem_range.mpr (Nat.mod_lt m hp))]
      unfold kloostermanNaturalCrossColumnProductTerm
      rw [natCast_mod_lcm_eq_natCast_left m q r,
        natCast_mod_lcm_eq_natCast_right m q r]
    _ = ∑ s ∈ Finset.range (Nat.lcm q r), ∑ m ∈ Finset.Icc 1 M,
          if s = m % Nat.lcm q r then
            kloostermanNaturalCrossColumnProductTerm q r n k s else 0 := by
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro s hs
      simp_rw [eq_comm]
      rw [← Finset.sum_filter]
      simp

/-- Exact lcm-period main term plus bounded residue discrepancy. -/
theorem kloostermanNaturalCrossIntervalCorrelation_eq_lcmComplete_add_remainder
    (M q r : ℕ) [NeZero q] [NeZero r]
    (n : ZMod q) (k : ZMod r) :
    kloostermanNaturalCrossIntervalCorrelation M q r n k =
      (((M : ℝ) / ((Nat.lcm q r : ℕ) : ℝ) : ℝ) : ℂ) *
          kloostermanNaturalLcmPeriodCorrelation q r n k +
        kloostermanNaturalCrossIntervalLcmRemainder M q r n k := by
  rw [kloostermanNaturalCrossIntervalCorrelation_eq_lcmResidueMultiplicity]
  unfold kloostermanNaturalLcmPeriodCorrelation
  unfold kloostermanNaturalCrossIntervalLcmRemainder kloostermanResidueDeviation
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro s hs
  push_cast
  ring

/-- Unequal-modulus interval correlation is exactly its lcm-period boundary remainder. -/
theorem kloostermanNaturalCrossIntervalCorrelation_eq_lcmRemainder_of_ne
    (M q r : ℕ) [NeZero q] [NeZero r] (hqr : q ≠ r)
    (n : ZMod q) (k : ZMod r) :
    kloostermanNaturalCrossIntervalCorrelation M q r n k =
      kloostermanNaturalCrossIntervalLcmRemainder M q r n k := by
  rw [kloostermanNaturalCrossIntervalCorrelation_eq_lcmComplete_add_remainder,
    kloostermanNaturalLcmPeriodCorrelation_eq_zero_of_ne q r hqr]
  simp

/-- Exact Kloosterman column energy over a common lcm period. -/
theorem sum_range_lcmPeriod_normSq_kloostermanSum
    (q r : ℕ) [NeZero q] [NeZero r] (n : ZMod q) :
    (∑ m ∈ Finset.range (Nat.lcm q r),
      ‖kloostermanSum q (m : ZMod q) n‖ ^ 2) =
      (Nat.lcm q r : ℝ) * Nat.totient q := by
  have hlpos : 0 < Nat.lcm q r := Nat.lcm_pos
    (Nat.pos_of_ne_zero (NeZero.ne q)) (Nat.pos_of_ne_zero (NeZero.ne r))
  have hqle : q ≤ Nat.lcm q r :=
    Nat.le_of_dvd hlpos (Nat.dvd_lcm_left q r)
  have hdpos : 0 < Nat.lcm q r / q :=
    Nat.div_pos hqle (Nat.pos_of_ne_zero (NeZero.ne q))
  letI : NeZero (Nat.lcm q r / q) := ⟨Nat.ne_of_gt hdpos⟩
  have henergy := sum_range_productPeriod_normSq_kloostermanSum
    q (Nat.lcm q r / q) n
  have hmul : q * (Nat.lcm q r / q) = Nat.lcm q r :=
    Nat.mul_div_cancel' (Nat.dvd_lcm_left q r)
  rw [hmul] at henergy
  calc
    (∑ m ∈ Finset.range (Nat.lcm q r),
        ‖kloostermanSum q (m : ZMod q) n‖ ^ 2) =
        ((Nat.lcm q r / q : ℕ) : ℝ) *
          ((q : ℝ) * Nat.totient q) := henergy
    _ = (Nat.lcm q r : ℝ) * Nat.totient q := by
      have hdq : ((Nat.lcm q r / q : ℕ) : ℝ) * (q : ℝ) =
          (Nat.lcm q r : ℝ) := by
        exact_mod_cast Nat.div_mul_cancel (Nat.dvd_lcm_left q r)
      rw [← mul_assoc, hdq]

/-- Lcm-period second-moment bound for the distinct-modulus boundary remainder. -/
theorem norm_kloostermanNaturalCrossIntervalLcmRemainder_le_secondMoment
    (M q r : ℕ) [NeZero q] [NeZero r]
    (n : ZMod q) (k : ZMod r) :
    ‖kloostermanNaturalCrossIntervalLcmRemainder M q r n k‖ ≤
      (Nat.lcm q r : ℝ) *
        ((Nat.totient q : ℝ) + Nat.totient r) / 2 := by
  have hp : 0 < Nat.lcm q r := Nat.lcm_pos
    (Nat.pos_of_ne_zero (NeZero.ne q)) (Nat.pos_of_ne_zero (NeZero.ne r))
  calc
    ‖kloostermanNaturalCrossIntervalLcmRemainder M q r n k‖ ≤
        ∑ s ∈ Finset.range (Nat.lcm q r),
          ‖(kloostermanResidueDeviation M (Nat.lcm q r) s : ℂ) *
            kloostermanNaturalCrossColumnProductTerm q r n k s‖ := by
      unfold kloostermanNaturalCrossIntervalLcmRemainder
      exact norm_sum_le _ _
    _ ≤ ∑ s ∈ Finset.range (Nat.lcm q r),
        ‖kloostermanSum q (s : ZMod q) n‖ *
          ‖kloostermanSum r (s : ZMod r) k‖ := by
      apply Finset.sum_le_sum
      intro s hs
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      unfold kloostermanNaturalCrossColumnProductTerm
      rw [norm_mul, norm_star]
      exact mul_le_of_le_one_left
        (mul_nonneg (norm_nonneg _) (norm_nonneg _))
        (abs_kloostermanResidueDeviation_le_one M (Nat.lcm q r) s hp
          (Finset.mem_range.mp hs))
    _ ≤ ∑ s ∈ Finset.range (Nat.lcm q r),
        (‖kloostermanSum q (s : ZMod q) n‖ ^ 2 +
          ‖kloostermanSum r (s : ZMod r) k‖ ^ 2) / 2 := by
      apply Finset.sum_le_sum
      intro s hs
      nlinarith [sq_nonneg
        (‖kloostermanSum q (s : ZMod q) n‖ -
          ‖kloostermanSum r (s : ZMod r) k‖)]
    _ = (Nat.lcm q r : ℝ) *
        ((Nat.totient q : ℝ) + Nat.totient r) / 2 := by
      have hrenergy :
          (∑ s ∈ Finset.range (Nat.lcm q r),
            ‖kloostermanSum r (s : ZMod r) k‖ ^ 2) =
            (Nat.lcm q r : ℝ) * Nat.totient r := by
        simpa [Nat.lcm_comm] using
          sum_range_lcmPeriod_normSq_kloostermanSum r q k
      rw [← Finset.sum_div]
      simp_rw [Finset.sum_add_distrib]
      rw [sum_range_lcmPeriod_normSq_kloostermanSum q r n, hrenergy]
      ring

/-- Stored-index distinct-modulus correlation is a pure lcm-period remainder. -/
theorem kloostermanCrossModulusCorrelation_Icc_eq_lcmRemainder_of_ne
    (M q r : ℕ) (hqr : q ≠ r) (n k : ℤ) :
    kloostermanCrossModulusCorrelation (Finset.Icc 1 M) q r n k =
      kloostermanNaturalCrossIntervalLcmRemainder M (q + 1) (r + 1)
        (Int.cast n) (Int.cast k) := by
  rw [kloostermanCrossModulusCorrelation_Icc_eq_natural]
  exact kloostermanNaturalCrossIntervalCorrelation_eq_lcmRemainder_of_ne
    M (q + 1) (r + 1) (Nat.succ_ne_succ_iff.mpr hqr) (Int.cast n) (Int.cast k)

/-- Factor-`gcd` improved boundary bound for stored-index distinct-modulus Gram correlations. -/
theorem norm_kloostermanCrossModulusCorrelation_Icc_le_lcmSecondMoment_of_ne
    (M q r : ℕ) (hqr : q ≠ r) (n k : ℤ) :
    ‖kloostermanCrossModulusCorrelation (Finset.Icc 1 M) q r n k‖ ≤
      (Nat.lcm (q + 1) (r + 1) : ℝ) *
        ((Nat.totient (q + 1) : ℝ) + Nat.totient (r + 1)) / 2 := by
  rw [kloostermanCrossModulusCorrelation_Icc_eq_lcmRemainder_of_ne M q r hqr n k]
  exact norm_kloostermanNaturalCrossIntervalLcmRemainder_le_secondMoment
    M (q + 1) (r + 1) (Int.cast n) (Int.cast k)

end

end RHTower.Sieve
