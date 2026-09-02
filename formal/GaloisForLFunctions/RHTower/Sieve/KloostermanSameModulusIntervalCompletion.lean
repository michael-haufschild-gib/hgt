import GaloisForLFunctions.RHTower.Sieve.KloostermanCompleteColumnRamanujan
import GaloisForLFunctions.RHTower.Sieve.ResiduePartitionCount

/-!
# Same-modulus Kloosterman interval completion

An interval sum of two equal-modulus Kloosterman columns is grouped by its physical residue.
Every residue multiplicity is its uniform real density plus a discrepancy of absolute value at
most one.  This gives an exact complete-period main term and a finite discrepancy remainder.
Cauchy--Schwarz and the exact Kloosterman second moment bound that remainder by `q * φ(q)`.

The last two theorems apply this completion directly to the equal-modulus term in the signed-kernel
Gram expansion, whose stored modulus index `q` represents the positive modulus `q + 1`.
-/

open scoped BigOperators ComplexConjugate
open Complex Finset

namespace RHTower.Sieve

noncomputable section

/-- Replace a complete `ZMod q` sum by the canonical natural representatives `0,…,q-1`. -/
theorem sum_zmod_eq_sum_range_natCast
    {R : Type*} [AddCommMonoid R] (q : ℕ) [NeZero q] (f : ZMod q → R) :
    ∑ a : ZMod q, f a = ∑ r ∈ Finset.range q, f (r : ZMod q) := by
  have hfinEquiv (r : Fin q) : ZMod.finEquiv q r = (r.val : ZMod q) := by
    cases q with
    | zero => exact (NeZero.ne 0 rfl).elim
    | succ q =>
        apply ZMod.val_injective
        change r.val = r.val % (q + 1)
        rw [Nat.mod_eq_of_lt r.isLt]
  calc
    (∑ a : ZMod q, f a) = ∑ r : Fin q, f (ZMod.finEquiv q r) :=
      ((ZMod.finEquiv q).sum_comp f).symm
    _ = ∑ r : Fin q, f (r.val : ZMod q) := by simp_rw [hfinEquiv]
    _ = ∑ r ∈ Finset.range q, f (r : ZMod q) := by
      exact Fin.sum_univ_eq_sum_range (fun r : ℕ => f (r : ZMod q)) q

/-- Product of two equal-modulus Kloosterman columns at a natural physical residue. -/
def kloostermanColumnProductTerm
    (q : ℕ) [NeZero q] (n k : ZMod q) (m : ℕ) : ℂ :=
  star (kloostermanSum q (m : ZMod q) n) * kloostermanSum q (m : ZMod q) k

/-- Equal-modulus Kloosterman column correlation on the physical interval `[1,M]`. -/
def kloostermanIntervalColumnCorrelation
    (M q : ℕ) [NeZero q] (n k : ZMod q) : ℂ :=
  ∑ m ∈ Finset.Icc 1 M, kloostermanColumnProductTerm q n k m

/-- Number of elements of `[1,M]` in residue class `r mod q`. -/
def kloostermanResidueMultiplicity (M q r : ℕ) : ℕ :=
  ((Finset.Icc 1 M).filter (fun m => m % q = r)).card

/-- Difference between a residue multiplicity and the uniform real density `M/q`. -/
def kloostermanResidueDeviation (M q r : ℕ) : ℝ :=
  (kloostermanResidueMultiplicity M q r : ℝ) - (M : ℝ) / (q : ℝ)

/-- Discrepancy remainder after extracting the complete-period main term. -/
def kloostermanIntervalColumnRemainder
    (M q : ℕ) [NeZero q] (n k : ZMod q) : ℂ :=
  ∑ r ∈ Finset.range q,
    (kloostermanResidueDeviation M q r : ℂ) * kloostermanColumnProductTerm q n k r

/-- Exact grouping of the interval correlation by physical residue multiplicity. -/
theorem kloostermanIntervalColumnCorrelation_eq_residueMultiplicity
    (M q : ℕ) [NeZero q] (n k : ZMod q) :
    kloostermanIntervalColumnCorrelation M q n k =
      ∑ r ∈ Finset.range q,
        (kloostermanResidueMultiplicity M q r : ℂ) *
          kloostermanColumnProductTerm q n k r := by
  classical
  unfold kloostermanIntervalColumnCorrelation kloostermanResidueMultiplicity
  calc
    (∑ m ∈ Finset.Icc 1 M, kloostermanColumnProductTerm q n k m) =
        ∑ m ∈ Finset.Icc 1 M, ∑ r ∈ Finset.range q,
          if r = m % q then kloostermanColumnProductTerm q n k r else 0 := by
      apply Finset.sum_congr rfl
      intro m hm
      rw [Finset.sum_ite_eq' (Finset.range q)]
      simp [Nat.mod_lt m (Nat.pos_of_ne_zero (NeZero.ne q)),
        kloostermanColumnProductTerm]
    _ = ∑ r ∈ Finset.range q, ∑ m ∈ Finset.Icc 1 M,
          if r = m % q then kloostermanColumnProductTerm q n k r else 0 := by
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro r hr
      simp_rw [eq_comm]
      rw [← Finset.sum_filter]
      simp

/-- One complete natural residue block is the complete column correlation. -/
theorem sum_range_kloostermanColumnProductTerm_eq_complete
    (q : ℕ) [NeZero q] (n k : ZMod q) :
    (∑ r ∈ Finset.range q, kloostermanColumnProductTerm q n k r) =
      kloostermanCompleteColumnCorrelation q n k := by
  unfold kloostermanColumnProductTerm kloostermanCompleteColumnCorrelation
  exact (sum_zmod_eq_sum_range_natCast q
    (fun a : ZMod q => star (kloostermanSum q a n) * kloostermanSum q a k)).symm

/-- Every interval residue discrepancy has absolute value at most one. -/
theorem abs_kloostermanResidueDeviation_le_one
    (M q r : ℕ) (hq : 0 < q) (hr : r < q) :
    |kloostermanResidueDeviation M q r| ≤ 1 := by
  unfold kloostermanResidueDeviation kloostermanResidueMultiplicity
  rw [abs_le]
  constructor
  · linarith [card_residue_class_ge hq M hr]
  · linarith [card_residue_class_le hq M r]

/-- Exact complete-period main term plus bounded-multiplicity discrepancy remainder. -/
theorem kloostermanIntervalColumnCorrelation_eq_complete_add_remainder
    (M q : ℕ) [NeZero q] (n k : ZMod q) :
    kloostermanIntervalColumnCorrelation M q n k =
      (((M : ℝ) / (q : ℝ) : ℝ) : ℂ) *
          kloostermanCompleteColumnCorrelation q n k +
        kloostermanIntervalColumnRemainder M q n k := by
  rw [kloostermanIntervalColumnCorrelation_eq_residueMultiplicity,
    show kloostermanCompleteColumnCorrelation q n k =
        ∑ r ∈ Finset.range q, kloostermanColumnProductTerm q n k r by
      exact (sum_range_kloostermanColumnProductTerm_eq_complete q n k).symm]
  unfold kloostermanIntervalColumnRemainder kloostermanResidueDeviation
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro r hr
  push_cast
  ring

/-- Completion remainder costs at most the exact complete second-moment scale `q * φ(q)`. -/
theorem norm_kloostermanIntervalColumnRemainder_le
    (M q : ℕ) [NeZero q] (n k : ZMod q) :
    ‖kloostermanIntervalColumnRemainder M q n k‖ ≤ (q : ℝ) * Nat.totient q := by
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  calc
    ‖kloostermanIntervalColumnRemainder M q n k‖ ≤
        ∑ r ∈ Finset.range q,
          ‖(kloostermanResidueDeviation M q r : ℂ) *
            kloostermanColumnProductTerm q n k r‖ := by
      unfold kloostermanIntervalColumnRemainder
      exact norm_sum_le _ _
    _ ≤ ∑ r ∈ Finset.range q,
        ‖kloostermanSum q (r : ZMod q) n‖ *
          ‖kloostermanSum q (r : ZMod q) k‖ := by
      apply Finset.sum_le_sum
      intro r hr
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      unfold kloostermanColumnProductTerm
      rw [norm_mul, norm_star]
      exact (mul_le_mul_of_nonneg_right
        (abs_kloostermanResidueDeviation_le_one M q r hq (Finset.mem_range.mp hr))
        (mul_nonneg (norm_nonneg _) (norm_nonneg _))).trans_eq (one_mul _)
    _ ≤ (q : ℝ) * Nat.totient q := by
      have hn : (∑ r ∈ Finset.range q,
          ‖kloostermanSum q (r : ZMod q) n‖ ^ 2) =
          (q : ℝ) * Nat.totient q := by
        rw [← sum_zmod_eq_sum_range_natCast q
          (fun a : ZMod q => ‖kloostermanSum q a n‖ ^ 2)]
        simp_rw [kloostermanSum_comm]
        exact sum_norm_kloostermanSum_sq q n
      have hk : (∑ r ∈ Finset.range q,
          ‖kloostermanSum q (r : ZMod q) k‖ ^ 2) =
          (q : ℝ) * Nat.totient q := by
        rw [← sum_zmod_eq_sum_range_natCast q
          (fun a : ZMod q => ‖kloostermanSum q a k‖ ^ 2)]
        simp_rw [kloostermanSum_comm]
        exact sum_norm_kloostermanSum_sq q k
      have hc := Finset.sum_mul_sq_le_sq_mul_sq (Finset.range q)
        (fun r : ℕ => ‖kloostermanSum q (r : ZMod q) n‖)
        (fun r : ℕ => ‖kloostermanSum q (r : ZMod q) k‖)
      rw [hn, hk] at hc
      have hsum : 0 ≤ ∑ r ∈ Finset.range q,
          ‖kloostermanSum q (r : ZMod q) n‖ *
            ‖kloostermanSum q (r : ZMod q) k‖ := by positivity
      have hmain : 0 ≤ (q : ℝ) * Nat.totient q := by positivity
      nlinarith

/-- Existing equal-modulus Gram correlation on `[1,M]` is the interval-column carrier above. -/
theorem kloostermanCrossModulusCorrelation_Icc_same_eq
    (M q : ℕ) (n k : ℤ) :
    kloostermanCrossModulusCorrelation (Finset.Icc 1 M) q q n k =
      kloostermanIntervalColumnCorrelation M (q + 1) (Int.cast n) (Int.cast k) := by
  rfl

/-- Exact Ramanujan main term for the equal-modulus part of the stored Gram correlation. -/
theorem kloostermanCrossModulusCorrelation_Icc_same_eq_cglRamanujan_add_remainder
    (M q : ℕ) (n k : ℤ) :
    kloostermanCrossModulusCorrelation (Finset.Icc 1 M) q q n k =
      ((((M : ℝ) / ((q + 1 : ℕ) : ℝ) : ℝ) : ℂ) *
          ((q + 1 : ℕ) : ℂ) *
            RHTower.cglRamanujanAdditiveSum
              ⟨q + 1, Nat.succ_pos q⟩
              ((Int.cast k : ZMod (q + 1)) - Int.cast n)) +
        kloostermanIntervalColumnRemainder M (q + 1) (Int.cast n) (Int.cast k) := by
  rw [kloostermanCrossModulusCorrelation_Icc_same_eq,
    kloostermanIntervalColumnCorrelation_eq_complete_add_remainder,
    kloostermanCompleteColumnCorrelation_eq_cglRamanujan]
  ring

/-- The equal-modulus Gram completion remainder has the explicit `(q+1)φ(q+1)` bound. -/
theorem norm_kloostermanCrossModulusCorrelation_Icc_same_remainder_le
    (M q : ℕ) (n k : ℤ) :
    ‖kloostermanIntervalColumnRemainder M (q + 1) (Int.cast n) (Int.cast k)‖ ≤
      ((q + 1 : ℕ) : ℝ) * Nat.totient (q + 1) := by
  exact norm_kloostermanIntervalColumnRemainder_le M (q + 1) (Int.cast n) (Int.cast k)

end

end RHTower.Sieve
