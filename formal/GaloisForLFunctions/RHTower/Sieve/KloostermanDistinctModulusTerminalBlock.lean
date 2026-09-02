import GaloisForLFunctions.RHTower.Sieve.KloostermanDistinctModulusLcmCompletion
import GaloisForLFunctions.RHTower.MertensSecondTheorem

/-!
# Terminal-block reduction for distinct-modulus Kloosterman correlations

After exact lcm-period orthogonality, every full common-period block in `[1,M]` vanishes. The
remaining correlation is the literal initial shifted block of length `M % lcm(q,r)`. This exact
support description retains information discarded by residue-discrepancy bounds.
-/

open scoped BigOperators ComplexConjugate
open Complex Finset

namespace RHTower.Sieve

noncomputable section

private theorem sum_range_mul_eq_nsmul_of_add_periodic
    {A : Type*} [AddCommMonoid A] (f : ℕ → A) (P d : ℕ)
    (hperiodic : ∀ a j : ℕ, f (a + P * j) = f a) :
    (∑ m ∈ Finset.range (d * P), f m) = d • ∑ a ∈ Finset.range P, f a := by
  rw [← Fin.sum_univ_eq_sum_range]
  let e : Fin d × Fin P ≃ Fin (d * P) := finProdFinEquiv
  calc
    (∑ m : Fin (d * P), f m.val) =
        ∑ p : Fin d × Fin P, f (p.2.val + P * p.1.val) := by
      rw [show (∑ m : Fin (d * P), f m.val) =
          ∑ p : Fin d × Fin P, f (e p).val from
        (e.sum_comp (fun m : Fin (d * P) => f m.val)).symm]
      apply Fintype.sum_congr
      intro p
      simp [e, finProdFinEquiv]
    _ = ∑ _j : Fin d, ∑ a : Fin P, f a.val := by
      rw [Fintype.sum_prod_type]
      apply Fintype.sum_congr
      intro j
      apply Fintype.sum_congr
      intro a
      exact hperiodic a.val j.val
    _ = d • ∑ a ∈ Finset.range P, f a := by
      rw [← Fin.sum_univ_eq_sum_range]
      simp

private theorem sum_range_eq_nsmul_add_mod_of_add_periodic
    {A : Type*} [AddCommMonoid A] (f : ℕ → A) (M P : ℕ)
    (hperiodic : ∀ a j : ℕ, f (a + P * j) = f a) :
    (∑ m ∈ Finset.range M, f m) =
      (M / P) • (∑ a ∈ Finset.range P, f a) +
        ∑ a ∈ Finset.range (M % P), f a := by
  conv_lhs => rw [← Nat.div_add_mod M P]
  rw [Finset.sum_range_add]
  have hblocks := sum_range_mul_eq_nsmul_of_add_periodic
    f P (M / P) hperiodic
  rw [Nat.mul_comm P (M / P), hblocks]
  apply congrArg (fun z => (M / P) • (∑ a ∈ Finset.range P, f a) + z)
  apply Finset.sum_congr rfl
  intro a ha
  rw [Nat.mul_comm (M / P) P, Nat.add_comm (P * (M / P)) a]
  exact hperiodic a (M / P)

/-- Literal terminal partial block after all complete lcm periods are removed. -/
def kloostermanNaturalCrossIntervalTerminalBlock
    (M q r : ℕ) [NeZero q] [NeZero r]
    (n : ZMod q) (k : ZMod r) : ℂ :=
  ∑ i ∈ Finset.range (M % Nat.lcm q r),
    kloostermanNaturalCrossColumnProductTerm q r n k (i + 1)

private theorem sum_range_shift_crossColumn_eq_lcmPeriod
    (q r : ℕ) [NeZero q] [NeZero r]
    (n : ZMod q) (k : ZMod r) :
    (∑ i ∈ Finset.range (Nat.lcm q r),
      kloostermanNaturalCrossColumnProductTerm q r n k (i + 1)) =
      kloostermanNaturalLcmPeriodCorrelation q r n k := by
  let f : ℕ → ℂ := kloostermanNaturalCrossColumnProductTerm q r n k
  have hperiod0 : f (Nat.lcm q r) = f 0 := by
    simpa [f] using
      kloostermanNaturalCrossColumnProductTerm_add_lcm_mul q r n k 0 1
  change (∑ i ∈ Finset.range (Nat.lcm q r), f (i + 1)) =
    ∑ i ∈ Finset.range (Nat.lcm q r), f i
  apply add_right_cancel (b := f 0)
  calc
    (∑ i ∈ Finset.range (Nat.lcm q r), f (i + 1)) + f 0 =
        ∑ i ∈ Finset.range (Nat.lcm q r + 1), f i := by
      rw [Finset.sum_range_succ']
    _ = (∑ i ∈ Finset.range (Nat.lcm q r), f i) + f (Nat.lcm q r) := by
      rw [Finset.sum_range_succ]
    _ = (∑ i ∈ Finset.range (Nat.lcm q r), f i) + f 0 := by
      rw [hperiod0]

/-- For unequal moduli, every complete lcm block erases and only the terminal block survives. -/
theorem kloostermanNaturalCrossIntervalCorrelation_eq_terminalBlock_of_ne
    (M q r : ℕ) [NeZero q] [NeZero r] (hqr : q ≠ r)
    (n : ZMod q) (k : ZMod r) :
    kloostermanNaturalCrossIntervalCorrelation M q r n k =
      kloostermanNaturalCrossIntervalTerminalBlock M q r n k := by
  unfold kloostermanNaturalCrossIntervalCorrelation
  rw [RHTower.sum_Icc_eq_sum_range_shift]
  let f : ℕ → ℂ := fun i =>
    kloostermanNaturalCrossColumnProductTerm q r n k (i + 1)
  have hperiodic : ∀ a j : ℕ,
      f (a + Nat.lcm q r * j) = f a := by
    intro a j
    change kloostermanNaturalCrossColumnProductTerm q r n k
        (a + Nat.lcm q r * j + 1) =
      kloostermanNaturalCrossColumnProductTerm q r n k (a + 1)
    rw [show a + Nat.lcm q r * j + 1 =
      (a + 1) + Nat.lcm q r * j by omega]
    exact kloostermanNaturalCrossColumnProductTerm_add_lcm_mul
      q r n k (a + 1) j
  have hdecomp := sum_range_eq_nsmul_add_mod_of_add_periodic
    f M (Nat.lcm q r) hperiodic
  have hcomplete : (∑ a ∈ Finset.range (Nat.lcm q r), f a) = 0 := by
    rw [show (∑ a ∈ Finset.range (Nat.lcm q r), f a) =
      kloostermanNaturalLcmPeriodCorrelation q r n k by
        exact sum_range_shift_crossColumn_eq_lcmPeriod q r n k]
    exact kloostermanNaturalLcmPeriodCorrelation_eq_zero_of_ne q r hqr n k
  rw [hcomplete, nsmul_zero, zero_add] at hdecomp
  exact hdecomp

/-- Elementary terminal-block bound retaining the exact residual length. -/
theorem norm_kloostermanNaturalCrossIntervalTerminalBlock_le
    (M q r : ℕ) [NeZero q] [NeZero r]
    (n : ZMod q) (k : ZMod r) :
    ‖kloostermanNaturalCrossIntervalTerminalBlock M q r n k‖ ≤
      ((M % Nat.lcm q r : ℕ) : ℝ) * Nat.totient q * Nat.totient r := by
  calc
    ‖kloostermanNaturalCrossIntervalTerminalBlock M q r n k‖ ≤
        ∑ i ∈ Finset.range (M % Nat.lcm q r),
          ‖kloostermanNaturalCrossColumnProductTerm q r n k (i + 1)‖ := by
      unfold kloostermanNaturalCrossIntervalTerminalBlock
      exact norm_sum_le _ _
    _ ≤ ∑ _i ∈ Finset.range (M % Nat.lcm q r),
        (Nat.totient q : ℝ) * Nat.totient r := by
      apply Finset.sum_le_sum
      intro i hi
      unfold kloostermanNaturalCrossColumnProductTerm
      rw [norm_mul, norm_star]
      exact mul_le_mul
        (norm_kloostermanSum_le_totient q _ _)
        (norm_kloostermanSum_le_totient r _ _)
        (norm_nonneg _) (Nat.cast_nonneg _)
    _ = ((M % Nat.lcm q r : ℕ) : ℝ) * Nat.totient q * Nat.totient r := by
      rw [Finset.sum_const, Finset.card_range]
      simp only [nsmul_eq_mul]
      ring

/-- Unequal-modulus interval bound retaining exact terminal-block length. -/
theorem norm_kloostermanNaturalCrossIntervalCorrelation_le_terminal_of_ne
    (M q r : ℕ) [NeZero q] [NeZero r] (hqr : q ≠ r)
    (n : ZMod q) (k : ZMod r) :
    ‖kloostermanNaturalCrossIntervalCorrelation M q r n k‖ ≤
      ((M % Nat.lcm q r : ℕ) : ℝ) * Nat.totient q * Nat.totient r := by
  rw [kloostermanNaturalCrossIntervalCorrelation_eq_terminalBlock_of_ne
    M q r hqr n k]
  exact norm_kloostermanNaturalCrossIntervalTerminalBlock_le M q r n k

/-- Stored-index Gram correlation equals its literal terminal common-period block. -/
theorem kloostermanCrossModulusCorrelation_Icc_eq_terminalBlock_of_ne
    (M q r : ℕ) (hqr : q ≠ r) (n k : ℤ) :
    kloostermanCrossModulusCorrelation (Finset.Icc 1 M) q r n k =
      kloostermanNaturalCrossIntervalTerminalBlock M (q + 1) (r + 1)
        (Int.cast n) (Int.cast k) := by
  rw [kloostermanCrossModulusCorrelation_Icc_eq_natural]
  exact kloostermanNaturalCrossIntervalCorrelation_eq_terminalBlock_of_ne
    M (q + 1) (r + 1) (Nat.succ_ne_succ_iff.mpr hqr) (Int.cast n) (Int.cast k)

/-- Stored-index terminal-block bound with exact residual length. -/
theorem norm_kloostermanCrossModulusCorrelation_Icc_le_terminal_of_ne
    (M q r : ℕ) (hqr : q ≠ r) (n k : ℤ) :
    ‖kloostermanCrossModulusCorrelation (Finset.Icc 1 M) q r n k‖ ≤
      ((M % Nat.lcm (q + 1) (r + 1) : ℕ) : ℝ) *
        Nat.totient (q + 1) * Nat.totient (r + 1) := by
  rw [kloostermanCrossModulusCorrelation_Icc_eq_terminalBlock_of_ne
    M q r hqr n k]
  exact norm_kloostermanNaturalCrossIntervalTerminalBlock_le
    M (q + 1) (r + 1) (Int.cast n) (Int.cast k)

end

end RHTower.Sieve
