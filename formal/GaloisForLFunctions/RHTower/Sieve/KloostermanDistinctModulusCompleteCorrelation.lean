import GaloisForLFunctions.RHTower.Sieve.KloostermanSameModulusIntervalCompletion

/-!
# Complete distinct-modulus Kloosterman column correlation

Complete Kloosterman columns of unequal positive moduli are exactly orthogonal over one product
period.  Block the physical frequency as `m = a + rj`.  The second column is constant in `j`,
while every unit frequency in the first column has a nontrivial additive character because
`q ∤ r`.  Additive-character orthogonality kills that block.  If instead `q ∣ r`, unequal moduli
give `r ∤ q`, and Hermitian symmetry reverses the argument.
-/

open scoped BigOperators ComplexConjugate
open Complex Finset

namespace RHTower.Sieve

noncomputable section

private theorem natCast_ne_zero_of_not_dvd
    (q r : ℕ) [NeZero q] (hqr : ¬ q ∣ r) : (r : ZMod q) ≠ 0 := by
  intro hr
  have hr' : (r : ZMod q) = (0 : ℕ) := by simpa using hr
  have hmod : r ≡ 0 [MOD q] :=
    ZMod.natCast_eq_natCast_iff r 0 q |>.mp hr'
  exact hqr (Nat.modEq_zero_iff_dvd.mp hmod)

private theorem neg_natCast_mul_unit_ne_zero
    (q r : ℕ) [NeZero q] (hqr : ¬ q ∣ r) (x : (ZMod q)ˣ) :
    -(r : ZMod q) * (x : ZMod q) ≠ 0 := by
  intro hx
  have hr : -(r : ZMod q) = 0 := by
    calc
      -(r : ZMod q) = (-(r : ZMod q) * (x : ZMod q)) *
          ((x⁻¹ : (ZMod q)ˣ) : ZMod q) := by simp [mul_assoc]
      _ = 0 := by rw [hx, zero_mul]
  exact natCast_ne_zero_of_not_dvd q r hqr (neg_eq_zero.mp hr)

private theorem sum_star_kloostermanSum_arithmeticProgression_eq_zero
    (q r : ℕ) [NeZero q] (hqr : ¬ q ∣ r) (a : ℕ) (n : ZMod q) :
    (∑ j : ZMod q,
      star (kloostermanSum q ((a + r * j.val : ℕ) : ZMod q) n)) = 0 := by
  simp_rw [star_kloostermanSum]
  unfold kloostermanSum kloostermanPhase
  rw [Finset.sum_comm]
  apply Fintype.sum_eq_zero
  intro x
  have hfactor (j : ZMod q) :
      ZMod.stdAddChar
          (-((a + r * j.val : ℕ) : ZMod q) * (x : ZMod q) +
            -n * ((x⁻¹ : (ZMod q)ˣ) : ZMod q)) =
        ZMod.stdAddChar
            (-(a : ZMod q) * (x : ZMod q) +
              -n * ((x⁻¹ : (ZMod q)ˣ) : ZMod q)) *
          ZMod.stdAddChar (j * (-(r : ZMod q) * (x : ZMod q))) := by
    rw [← AddChar.map_add_eq_mul]
    push_cast
    rw [show ((j.val : ℕ) : ZMod q) = j from ZMod.natCast_zmod_val j]
    congr 1
    ring
  simp_rw [hfactor]
  rw [← Finset.mul_sum, sum_stdAddChar_mul]
  rw [if_neg (neg_natCast_mul_unit_ne_zero q r hqr x)]
  simp

/-- Complete cross-modulus column correlation over the common product period. -/
def kloostermanNaturalProductPeriodCorrelation
    (q r : ℕ) [NeZero q] [NeZero r] (n : ZMod q) (k : ZMod r) : ℂ :=
  ∑ m ∈ Finset.range (q * r),
    star (kloostermanSum q (m : ZMod q) n) *
      kloostermanSum r (m : ZMod r) k

/-- A common product period vanishes when the first modulus does not divide the second. -/
theorem kloostermanNaturalProductPeriodCorrelation_eq_zero_of_not_dvd
    (q r : ℕ) [NeZero q] [NeZero r] (hqr : ¬ q ∣ r)
    (n : ZMod q) (k : ZMod r) :
    kloostermanNaturalProductPeriodCorrelation q r n k = 0 := by
  unfold kloostermanNaturalProductPeriodCorrelation
  rw [← Fin.sum_univ_eq_sum_range]
  let e : Fin q × Fin r ≃ Fin (q * r) := finProdFinEquiv
  calc
    (∑ m : Fin (q * r),
        star (kloostermanSum q (m.val : ZMod q) n) *
          kloostermanSum r (m.val : ZMod r) k) =
        ∑ p : Fin q × Fin r,
          star (kloostermanSum q ((p.2.val + r * p.1.val : ℕ) : ZMod q) n) *
            kloostermanSum r ((p.2.val + r * p.1.val : ℕ) : ZMod r) k := by
      rw [show (∑ m : Fin (q * r),
          star (kloostermanSum q (m.val : ZMod q) n) *
            kloostermanSum r (m.val : ZMod r) k) =
          ∑ p : Fin q × Fin r,
            star (kloostermanSum q ((e p).val : ZMod q) n) *
              kloostermanSum r ((e p).val : ZMod r) k from
        (e.sum_comp (fun m : Fin (q * r) =>
          star (kloostermanSum q (m.val : ZMod q) n) *
            kloostermanSum r (m.val : ZMod r) k)).symm]
      apply Fintype.sum_congr
      intro p
      simp [e, finProdFinEquiv]
    _ = ∑ a : Fin r, ∑ j : Fin q,
          star (kloostermanSum q ((a.val + r * j.val : ℕ) : ZMod q) n) *
            kloostermanSum r ((a.val + r * j.val : ℕ) : ZMod r) k := by
      rw [Fintype.sum_prod_type, Finset.sum_comm]
    _ = 0 := by
      apply Fintype.sum_eq_zero
      intro a
      have hmodr (j : Fin q) :
          ((a.val + r * j.val : ℕ) : ZMod r) = (a.val : ZMod r) := by
        push_cast
        rw [ZMod.natCast_self, zero_mul, add_zero]
      simp_rw [hmodr]
      rw [← Finset.sum_mul]
      have hfin (j : Fin q) : ZMod.finEquiv q j = (j.val : ZMod q) := by
        cases q with
        | zero => exact (NeZero.ne 0 rfl).elim
        | succ q =>
            apply ZMod.val_injective
            change j.val = j.val % (q + 1)
            rw [Nat.mod_eq_of_lt j.isLt]
      have hsum :
          (∑ j : Fin q,
            star (kloostermanSum q ((a.val + r * j.val : ℕ) : ZMod q) n)) = 0 := by
        have hsumZ :
            (∑ j : ZMod q,
              star (kloostermanSum q
                ((a.val : ZMod q) + (r : ZMod q) * j) n)) = 0 := by
          calc
            (∑ j : ZMod q,
                star (kloostermanSum q
                  ((a.val : ZMod q) + (r : ZMod q) * j) n)) =
                ∑ j : ZMod q,
                  star (kloostermanSum q
                    ((a.val + r * j.val : ℕ) : ZMod q) n) := by
              apply Fintype.sum_congr
              intro j
              push_cast
              rw [ZMod.natCast_zmod_val]
            _ = 0 :=
              sum_star_kloostermanSum_arithmeticProgression_eq_zero q r hqr a.val n
        calc
          (∑ j : Fin q,
              star (kloostermanSum q ((a.val + r * j.val : ℕ) : ZMod q) n)) =
              ∑ j : ZMod q,
                star (kloostermanSum q
                  ((a.val : ZMod q) + (r : ZMod q) * j) n) := by
            exact Fintype.sum_equiv (ZMod.finEquiv q)
              (fun j : Fin q =>
                star (kloostermanSum q ((a.val + r * j.val : ℕ) : ZMod q) n))
              (fun j : ZMod q =>
                star (kloostermanSum q
                  ((a.val : ZMod q) + (r : ZMod q) * j) n))
              (fun j => by
                push_cast
                rw [hfin j])
          _ = 0 := hsumZ
      rw [hsum]
      simp

/-- Product-period cross-correlation has the expected Hermitian symmetry. -/
theorem star_kloostermanNaturalProductPeriodCorrelation
    (q r : ℕ) [NeZero q] [NeZero r] (n : ZMod q) (k : ZMod r) :
    star (kloostermanNaturalProductPeriodCorrelation q r n k) =
      kloostermanNaturalProductPeriodCorrelation r q k n := by
  unfold kloostermanNaturalProductPeriodCorrelation
  change (starRingEnd ℂ)
      (∑ m ∈ Finset.range (q * r),
        star (kloostermanSum q (m : ZMod q) n) *
          kloostermanSum r (m : ZMod r) k) = _
  rw [map_sum]
  simpa only [Nat.mul_comm] using
    Finset.sum_congr rfl (fun m _hm => by
      rw [map_mul]
      simp
      ring)

/-- Complete Kloosterman columns of unequal moduli are orthogonal over one product period. -/
theorem kloostermanNaturalProductPeriodCorrelation_eq_zero_of_ne
    (q r : ℕ) [NeZero q] [NeZero r] (hqr : q ≠ r)
    (n : ZMod q) (k : ZMod r) :
    kloostermanNaturalProductPeriodCorrelation q r n k = 0 := by
  by_cases hdvd : q ∣ r
  · have hnot : ¬ r ∣ q := by
      intro hrev
      exact hqr (Nat.dvd_antisymm hdvd hrev)
    have hz := kloostermanNaturalProductPeriodCorrelation_eq_zero_of_not_dvd
      r q hnot k n
    have hstar := star_kloostermanNaturalProductPeriodCorrelation q r n k
    rw [hz] at hstar
    apply_fun star at hstar
    simpa using hstar
  · exact kloostermanNaturalProductPeriodCorrelation_eq_zero_of_not_dvd
      q r hdvd n k

/-- Product of two Kloosterman columns of possibly different positive moduli. -/
def kloostermanNaturalCrossColumnProductTerm
    (q r : ℕ) [NeZero q] [NeZero r]
    (n : ZMod q) (k : ZMod r) (m : ℕ) : ℂ :=
  star (kloostermanSum q (m : ZMod q) n) *
    kloostermanSum r (m : ZMod r) k

/-- Cross-modulus Kloosterman column correlation on the physical interval `[1,M]`. -/
def kloostermanNaturalCrossIntervalCorrelation
    (M q r : ℕ) [NeZero q] [NeZero r]
    (n : ZMod q) (k : ZMod r) : ℂ :=
  ∑ m ∈ Finset.Icc 1 M, kloostermanNaturalCrossColumnProductTerm q r n k m

/-- Product-period discrepancy after extracting the uniform residue density. -/
def kloostermanNaturalCrossIntervalRemainder
    (M q r : ℕ) [NeZero q] [NeZero r]
    (n : ZMod q) (k : ZMod r) : ℂ :=
  ∑ s ∈ Finset.range (q * r),
    (kloostermanResidueDeviation M (q * r) s : ℂ) *
      kloostermanNaturalCrossColumnProductTerm q r n k s

private theorem natCast_mod_mul_eq_natCast_left
    (m q r : ℕ) [NeZero q] :
    ((m % (q * r) : ℕ) : ZMod q) = (m : ZMod q) := by
  apply (ZMod.natCast_eq_natCast_iff (m % (q * r)) m q).mpr
  exact Nat.mod_mod_of_dvd m (Nat.dvd_mul_right q r)

private theorem natCast_mod_mul_eq_natCast_right
    (m q r : ℕ) [NeZero r] :
    ((m % (q * r) : ℕ) : ZMod r) = (m : ZMod r) := by
  apply (ZMod.natCast_eq_natCast_iff (m % (q * r)) m r).mpr
  exact Nat.mod_mod_of_dvd m (Nat.dvd_mul_left r q)

/-- Exact grouping of a cross-modulus interval correlation by product-period residue. -/
theorem kloostermanNaturalCrossIntervalCorrelation_eq_residueMultiplicity
    (M q r : ℕ) [NeZero q] [NeZero r]
    (n : ZMod q) (k : ZMod r) :
    kloostermanNaturalCrossIntervalCorrelation M q r n k =
      ∑ s ∈ Finset.range (q * r),
        (kloostermanResidueMultiplicity M (q * r) s : ℂ) *
          kloostermanNaturalCrossColumnProductTerm q r n k s := by
  classical
  unfold kloostermanNaturalCrossIntervalCorrelation kloostermanResidueMultiplicity
  calc
    (∑ m ∈ Finset.Icc 1 M, kloostermanNaturalCrossColumnProductTerm q r n k m) =
        ∑ m ∈ Finset.Icc 1 M, ∑ s ∈ Finset.range (q * r),
          if s = m % (q * r) then
            kloostermanNaturalCrossColumnProductTerm q r n k s else 0 := by
      apply Finset.sum_congr rfl
      intro m hm
      rw [Finset.sum_ite_eq' (Finset.range (q * r))]
      have hp : 0 < q * r := mul_pos
        (Nat.pos_of_ne_zero (NeZero.ne q)) (Nat.pos_of_ne_zero (NeZero.ne r))
      rw [if_pos (Finset.mem_range.mpr (Nat.mod_lt m hp))]
      unfold kloostermanNaturalCrossColumnProductTerm
      rw [natCast_mod_mul_eq_natCast_left m q r,
        natCast_mod_mul_eq_natCast_right m q r]
    _ = ∑ s ∈ Finset.range (q * r), ∑ m ∈ Finset.Icc 1 M,
          if s = m % (q * r) then
            kloostermanNaturalCrossColumnProductTerm q r n k s else 0 := by
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro s hs
      simp_rw [eq_comm]
      rw [← Finset.sum_filter]
      simp

/-- Exact product-period main term plus bounded residue discrepancy. -/
theorem kloostermanNaturalCrossIntervalCorrelation_eq_complete_add_remainder
    (M q r : ℕ) [NeZero q] [NeZero r]
    (n : ZMod q) (k : ZMod r) :
    kloostermanNaturalCrossIntervalCorrelation M q r n k =
      (((M : ℝ) / ((q * r : ℕ) : ℝ) : ℝ) : ℂ) *
          kloostermanNaturalProductPeriodCorrelation q r n k +
        kloostermanNaturalCrossIntervalRemainder M q r n k := by
  rw [kloostermanNaturalCrossIntervalCorrelation_eq_residueMultiplicity]
  unfold kloostermanNaturalProductPeriodCorrelation
  unfold kloostermanNaturalCrossIntervalRemainder kloostermanResidueDeviation
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro s hs
  unfold kloostermanNaturalCrossColumnProductTerm
  push_cast
  ring

/-- Unequal-modulus interval correlation is exactly its product-period boundary remainder. -/
theorem kloostermanNaturalCrossIntervalCorrelation_eq_remainder_of_ne
    (M q r : ℕ) [NeZero q] [NeZero r] (hqr : q ≠ r)
    (n : ZMod q) (k : ZMod r) :
    kloostermanNaturalCrossIntervalCorrelation M q r n k =
      kloostermanNaturalCrossIntervalRemainder M q r n k := by
  rw [kloostermanNaturalCrossIntervalCorrelation_eq_complete_add_remainder,
    kloostermanNaturalProductPeriodCorrelation_eq_zero_of_ne q r hqr]
  simp

/-- Exact repeated Kloosterman column energy over a product period. -/
theorem sum_range_productPeriod_normSq_kloostermanSum
    (q r : ℕ) [NeZero q] [NeZero r] (n : ZMod q) :
    (∑ m ∈ Finset.range (q * r), ‖kloostermanSum q (m : ZMod q) n‖ ^ 2) =
      (r : ℝ) * ((q : ℝ) * Nat.totient q) := by
  rw [Nat.mul_comm q r, ← Fin.sum_univ_eq_sum_range]
  let e : Fin r × Fin q ≃ Fin (r * q) := finProdFinEquiv
  calc
    (∑ m : Fin (r * q), ‖kloostermanSum q (m.val : ZMod q) n‖ ^ 2) =
        ∑ p : Fin r × Fin q,
          ‖kloostermanSum q ((p.2.val + q * p.1.val : ℕ) : ZMod q) n‖ ^ 2 := by
      rw [show (∑ m : Fin (r * q),
          ‖kloostermanSum q (m.val : ZMod q) n‖ ^ 2) =
          ∑ p : Fin r × Fin q,
            ‖kloostermanSum q ((e p).val : ZMod q) n‖ ^ 2 from
        (e.sum_comp (fun m : Fin (r * q) =>
          ‖kloostermanSum q (m.val : ZMod q) n‖ ^ 2)).symm]
      apply Fintype.sum_congr
      intro p
      simp [e, finProdFinEquiv]
    _ = ∑ _j : Fin r, ∑ a : Fin q,
          ‖kloostermanSum q (a.val : ZMod q) n‖ ^ 2 := by
      rw [Fintype.sum_prod_type]
      apply Fintype.sum_congr
      intro j
      apply Fintype.sum_congr
      intro a
      push_cast
      rw [ZMod.natCast_self, zero_mul, add_zero]
    _ = (r : ℝ) * ((q : ℝ) * Nat.totient q) := by
      have henergy :
          (∑ a : Fin q, ‖kloostermanSum q (a.val : ZMod q) n‖ ^ 2) =
            (q : ℝ) * Nat.totient q := by
        calc
          (∑ a : Fin q, ‖kloostermanSum q (a.val : ZMod q) n‖ ^ 2) =
              ∑ a ∈ Finset.range q,
                ‖kloostermanSum q (a : ZMod q) n‖ ^ 2 :=
            Fin.sum_univ_eq_sum_range
              (fun a : ℕ => ‖kloostermanSum q (a : ZMod q) n‖ ^ 2) q
          _ = ∑ a : ZMod q, ‖kloostermanSum q a n‖ ^ 2 :=
            (sum_zmod_eq_sum_range_natCast q
              (fun a : ZMod q => ‖kloostermanSum q a n‖ ^ 2)).symm
          _ = _ := by
            simp_rw [kloostermanSum_comm]
            exact sum_norm_kloostermanSum_sq q n
      simp_rw [henergy]
      simp

/-- Second-moment completion bound for a distinct-modulus boundary remainder. -/
theorem norm_kloostermanNaturalCrossIntervalRemainder_le_secondMoment
    (M q r : ℕ) [NeZero q] [NeZero r]
    (n : ZMod q) (k : ZMod r) :
    ‖kloostermanNaturalCrossIntervalRemainder M q r n k‖ ≤
      (q * r : ℝ) * ((Nat.totient q : ℝ) + Nat.totient r) / 2 := by
  have hp : 0 < q * r := mul_pos
    (Nat.pos_of_ne_zero (NeZero.ne q)) (Nat.pos_of_ne_zero (NeZero.ne r))
  calc
    ‖kloostermanNaturalCrossIntervalRemainder M q r n k‖ ≤
        ∑ s ∈ Finset.range (q * r),
          ‖(kloostermanResidueDeviation M (q * r) s : ℂ) *
            kloostermanNaturalCrossColumnProductTerm q r n k s‖ := by
      unfold kloostermanNaturalCrossIntervalRemainder
      exact norm_sum_le _ _
    _ ≤ ∑ s ∈ Finset.range (q * r),
        ‖kloostermanSum q (s : ZMod q) n‖ *
          ‖kloostermanSum r (s : ZMod r) k‖ := by
      apply Finset.sum_le_sum
      intro s hs
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      unfold kloostermanNaturalCrossColumnProductTerm
      rw [norm_mul, norm_star]
      exact mul_le_of_le_one_left
        (mul_nonneg (norm_nonneg _) (norm_nonneg _))
        (abs_kloostermanResidueDeviation_le_one M (q * r) s hp
          (Finset.mem_range.mp hs))
    _ ≤ ∑ s ∈ Finset.range (q * r),
        (‖kloostermanSum q (s : ZMod q) n‖ ^ 2 +
          ‖kloostermanSum r (s : ZMod r) k‖ ^ 2) / 2 := by
      apply Finset.sum_le_sum
      intro s hs
      nlinarith [sq_nonneg
        (‖kloostermanSum q (s : ZMod q) n‖ -
          ‖kloostermanSum r (s : ZMod r) k‖)]
    _ = (q * r : ℝ) * ((Nat.totient q : ℝ) + Nat.totient r) / 2 := by
      rw [← Finset.sum_div]
      simp_rw [Finset.sum_add_distrib]
      rw [sum_range_productPeriod_normSq_kloostermanSum q r n]
      rw [show (∑ s ∈ Finset.range (q * r),
          ‖kloostermanSum r (s : ZMod r) k‖ ^ 2) =
          (q : ℝ) * ((r : ℝ) * Nat.totient r) by
        simpa [Nat.mul_comm] using
          sum_range_productPeriod_normSq_kloostermanSum r q k]
      ring

/-- Elementary explicit bound for the distinct-modulus interval-completion remainder. -/
theorem norm_kloostermanNaturalCrossIntervalRemainder_le
    (M q r : ℕ) [NeZero q] [NeZero r]
    (n : ZMod q) (k : ZMod r) :
    ‖kloostermanNaturalCrossIntervalRemainder M q r n k‖ ≤
      (q * r : ℝ) * Nat.totient q * Nat.totient r := by
  have hp : 0 < q * r := mul_pos
    (Nat.pos_of_ne_zero (NeZero.ne q)) (Nat.pos_of_ne_zero (NeZero.ne r))
  calc
    ‖kloostermanNaturalCrossIntervalRemainder M q r n k‖ ≤
        ∑ s ∈ Finset.range (q * r),
          ‖(kloostermanResidueDeviation M (q * r) s : ℂ) *
            kloostermanNaturalCrossColumnProductTerm q r n k s‖ := by
      unfold kloostermanNaturalCrossIntervalRemainder
      exact norm_sum_le _ _
    _ ≤ ∑ _s ∈ Finset.range (q * r),
        (Nat.totient q : ℝ) * Nat.totient r := by
      apply Finset.sum_le_sum
      intro s hs
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      unfold kloostermanNaturalCrossColumnProductTerm
      rw [norm_mul, norm_star]
      calc
        |kloostermanResidueDeviation M (q * r) s| *
              (‖kloostermanSum q (s : ZMod q) n‖ *
                ‖kloostermanSum r (s : ZMod r) k‖) ≤
            1 * (‖kloostermanSum q (s : ZMod q) n‖ *
                ‖kloostermanSum r (s : ZMod r) k‖) := by
          gcongr
          exact abs_kloostermanResidueDeviation_le_one M (q * r) s hp
            (Finset.mem_range.mp hs)
        _ ≤ 1 * ((Nat.totient q : ℝ) * Nat.totient r) := by
          gcongr
          · exact norm_kloostermanSum_le_totient q (s : ZMod q) n
          · exact norm_kloostermanSum_le_totient r (s : ZMod r) k
        _ = _ := one_mul _
    _ = (q * r : ℝ) * Nat.totient q * Nat.totient r := by
      simp
      ring

/-- Existing stored-index correlation is the natural positive-modulus interval carrier. -/
theorem kloostermanCrossModulusCorrelation_Icc_eq_natural
    (M q r : ℕ) (n k : ℤ) :
    kloostermanCrossModulusCorrelation (Finset.Icc 1 M) q r n k =
      kloostermanNaturalCrossIntervalCorrelation M (q + 1) (r + 1)
        (Int.cast n) (Int.cast k) := by
  rfl

/-- Stored-index distinct-modulus correlation is a pure completion remainder. -/
theorem kloostermanCrossModulusCorrelation_Icc_eq_remainder_of_ne
    (M q r : ℕ) (hqr : q ≠ r) (n k : ℤ) :
    kloostermanCrossModulusCorrelation (Finset.Icc 1 M) q r n k =
      kloostermanNaturalCrossIntervalRemainder M (q + 1) (r + 1)
        (Int.cast n) (Int.cast k) := by
  rw [kloostermanCrossModulusCorrelation_Icc_eq_natural]
  exact kloostermanNaturalCrossIntervalCorrelation_eq_remainder_of_ne
    M (q + 1) (r + 1) (Nat.succ_ne_succ_iff.mpr hqr) (Int.cast n) (Int.cast k)

/-- Second-moment boundary bound for stored-index distinct-modulus Gram correlations. -/
theorem norm_kloostermanCrossModulusCorrelation_Icc_le_secondMoment_of_ne
    (M q r : ℕ) (hqr : q ≠ r) (n k : ℤ) :
    ‖kloostermanCrossModulusCorrelation (Finset.Icc 1 M) q r n k‖ ≤
      (((q + 1) * (r + 1) : ℕ) : ℝ) *
        ((Nat.totient (q + 1) : ℝ) + Nat.totient (r + 1)) / 2 := by
  rw [kloostermanCrossModulusCorrelation_Icc_eq_remainder_of_ne M q r hqr n k]
  simpa [Nat.cast_mul] using
    norm_kloostermanNaturalCrossIntervalRemainder_le_secondMoment
      M (q + 1) (r + 1) (Int.cast n) (Int.cast k)

/-- Explicit boundary bound for stored-index distinct-modulus Gram correlations. -/
theorem norm_kloostermanCrossModulusCorrelation_Icc_le_of_ne
    (M q r : ℕ) (hqr : q ≠ r) (n k : ℤ) :
    ‖kloostermanCrossModulusCorrelation (Finset.Icc 1 M) q r n k‖ ≤
      (((q + 1) * (r + 1) : ℕ) : ℝ) *
        Nat.totient (q + 1) * Nat.totient (r + 1) := by
  rw [kloostermanCrossModulusCorrelation_Icc_eq_remainder_of_ne M q r hqr n k]
  simpa [Nat.cast_mul] using
    norm_kloostermanNaturalCrossIntervalRemainder_le
      M (q + 1) (r + 1) (Int.cast n) (Int.cast k)

end

end RHTower.Sieve
