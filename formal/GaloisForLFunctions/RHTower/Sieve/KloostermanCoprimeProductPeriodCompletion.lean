import GaloisForLFunctions.RHTower.Sieve.KloostermanSameModulusIntervalCompletion

/-!
# Coprime cross-modulus Kloosterman completion

The cross-modulus term in the ordinary-index signed Kloosterman Gram is not a second spectral
bulk when its two positive moduli are coprime.  Over one product period, CRT separates the two
physical residue coordinates and each nontrivial Kloosterman column has zero first-variable mean.
Hence the complete cross block vanishes exactly.

For an arbitrary interval, grouping by residues modulo the product period gives a stronger
positive survivor: the entire cross-modulus correlation is exactly the residue-discrepancy
boundary term.  This preserves both modulus labels, both column labels, and their coefficients.
The elementary norm estimate is uniform in interval length but grows with the moduli; collective
source-weighted control of this literal boundary remains the analytic producer, not hidden bulk
Kuznetsov cancellation.
-/

open scoped BigOperators ComplexConjugate
open Complex Finset

namespace RHTower.Sieve

noncomputable section

/-- Every nontrivial Kloosterman column has zero mean in its first variable. -/
theorem sum_kloostermanSum_first_eq_zero
    (q : ℕ) [NeZero q] (hq : 1 < q) (n : ZMod q) :
    (∑ m : ZMod q, kloostermanSum q m n) = 0 := by
  letI : Nontrivial (ZMod q) := ZMod.nontrivial_iff.mpr hq.ne'
  unfold kloostermanSum kloostermanPhase
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro x _hx
  have hx0 : (x : ZMod q) ≠ 0 := Units.ne_zero x
  calc
    (∑ m : ZMod q,
        ZMod.stdAddChar (m * (x : ZMod q) +
          n * ((x⁻¹ : (ZMod q)ˣ) : ZMod q))) =
        (∑ m : ZMod q, ZMod.stdAddChar (m * (x : ZMod q))) *
          ZMod.stdAddChar (n * ((x⁻¹ : (ZMod q)ˣ) : ZMod q)) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro m _hm
      rw [AddChar.map_add_eq_mul]
    _ = 0 := by simp [sum_stdAddChar_mul, hx0]

/-- Product-period correlation after CRT separates the two residue variables. -/
def kloostermanCoprimeProductPeriodCorrelation
    (q r : ℕ) [NeZero q] [NeZero r] (n : ZMod q) (k : ZMod r) : ℂ :=
  ∑ z : ZMod q × ZMod r,
    star (kloostermanSum q z.1 n) * kloostermanSum r z.2 k

/-- Coprime nontrivial Kloosterman columns are exactly orthogonal over a product period. -/
theorem kloostermanCoprimeProductPeriodCorrelation_eq_zero
    (q r : ℕ) [NeZero q] [NeZero r] (_hq : 1 < q) (hr : 1 < r)
    (n : ZMod q) (k : ZMod r) :
    kloostermanCoprimeProductPeriodCorrelation q r n k = 0 := by
  unfold kloostermanCoprimeProductPeriodCorrelation
  rw [Fintype.sum_prod_type]
  simp_rw [← Finset.mul_sum]
  simp [sum_kloostermanSum_first_eq_zero r hr k]

/-- Product of two Kloosterman columns at one natural physical index. -/
def kloostermanCrossColumnProductTerm
    (q r : ℕ) [NeZero q] [NeZero r]
    (n : ZMod q) (k : ZMod r) (m : ℕ) : ℂ :=
  star (kloostermanSum q (m : ZMod q) n) *
    kloostermanSum r (m : ZMod r) k

/-- Cross-column correlation on the physical interval `[1,M]`. -/
def kloostermanCrossIntervalColumnCorrelation
    (M q r : ℕ) [NeZero q] [NeZero r]
    (n : ZMod q) (k : ZMod r) : ℂ :=
  ∑ m ∈ Finset.Icc 1 M, kloostermanCrossColumnProductTerm q r n k m

/-- Product-period residue discrepancy after the complete cross block is removed. -/
def kloostermanCrossIntervalColumnRemainder
    (M q r : ℕ) [NeZero q] [NeZero r]
    (n : ZMod q) (k : ZMod r) : ℂ :=
  ∑ s ∈ Finset.range (q * r),
    (kloostermanResidueDeviation M (q * r) s : ℂ) *
      kloostermanCrossColumnProductTerm q r n k s

/-- Reducing a natural index modulo the product period preserves its residue modulo the first
factor. -/
theorem natCast_mod_mul_zmod_left
    (m q r : ℕ) [NeZero q] [NeZero r] :
    ((m % (q * r) : ℕ) : ZMod q) = (m : ZMod q) := by
  have hP : ((q * r : ℕ) : ZMod q) = 0 := by simp
  calc
    ((m % (q * r) : ℕ) : ZMod q) =
        ((m % (q * r) : ℕ) : ZMod q) +
          ((q * r : ℕ) : ZMod q) * ((m / (q * r) : ℕ) : ZMod q) := by
      rw [hP, zero_mul, add_zero]
    _ = ((m % (q * r) + (q * r) * (m / (q * r)) : ℕ) : ZMod q) := by
      norm_cast
    _ = (m : ZMod q) := by rw [Nat.mod_add_div]

/-- Group incomplete cross correlation by residues modulo the product period. -/
theorem kloostermanCrossIntervalColumnCorrelation_eq_residueMultiplicity
    (M q r : ℕ) [NeZero q] [NeZero r]
    (n : ZMod q) (k : ZMod r) :
    kloostermanCrossIntervalColumnCorrelation M q r n k =
      ∑ s ∈ Finset.range (q * r),
        (kloostermanResidueMultiplicity M (q * r) s : ℂ) *
          kloostermanCrossColumnProductTerm q r n k s := by
  classical
  unfold kloostermanCrossIntervalColumnCorrelation kloostermanResidueMultiplicity
  calc
    (∑ m ∈ Finset.Icc 1 M, kloostermanCrossColumnProductTerm q r n k m) =
        ∑ m ∈ Finset.Icc 1 M, ∑ s ∈ Finset.range (q * r),
          if s = m % (q * r) then kloostermanCrossColumnProductTerm q r n k s else 0 := by
      apply Finset.sum_congr rfl
      intro m _hm
      rw [Finset.sum_ite_eq' (Finset.range (q * r))]
      have hpos : 0 < q * r := Nat.mul_pos
        (Nat.pos_of_ne_zero (NeZero.ne q)) (Nat.pos_of_ne_zero (NeZero.ne r))
      rw [if_pos (Finset.mem_range.mpr (Nat.mod_lt m hpos))]
      unfold kloostermanCrossColumnProductTerm
      apply congrArg₂ (· * ·)
      · apply congrArg star
        apply congrArg (fun z : ZMod q => kloostermanSum q z n)
        exact (natCast_mod_mul_zmod_left m q r).symm
      · apply congrArg (fun z : ZMod r => kloostermanSum r z k)
        have hright : ((m % (q * r) : ℕ) : ZMod r) = (m : ZMod r) := by
          rw [Nat.mul_comm]
          exact natCast_mod_mul_zmod_left m r q
        exact hright.symm
    _ = ∑ s ∈ Finset.range (q * r), ∑ m ∈ Finset.Icc 1 M,
          if s = m % (q * r) then kloostermanCrossColumnProductTerm q r n k s else 0 := by
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro s _hs
      simp_rw [eq_comm]
      rw [← Finset.sum_filter]
      simp

/-- Replace a natural range sum modulo `N` by the complete `ZMod N` sum. -/
theorem sum_range_natCast_zmod
    (N : ℕ) [NeZero N] (f : ZMod N → ℂ) :
    (∑ m ∈ Finset.range N, f (m : ZMod N)) = ∑ z : ZMod N, f z := by
  exact (sum_zmod_eq_sum_range_natCast N f).symm

/-- One complete coprime product block of the physical cross-column term vanishes. -/
theorem sum_range_kloostermanCrossColumnProductTerm_eq_zero
    (q r : ℕ) [NeZero q] [NeZero r]
    (hq : 1 < q) (hr : 1 < r) (hcop : Nat.Coprime q r)
    (n : ZMod q) (k : ZMod r) :
    (∑ m ∈ Finset.range (q * r),
      kloostermanCrossColumnProductTerm q r n k m) = 0 := by
  letI : NeZero (q * r) := ⟨Nat.mul_ne_zero (NeZero.ne q) (NeZero.ne r)⟩
  let e : ZMod (q * r) ≃+* ZMod q × ZMod r := ZMod.chineseRemainder hcop
  let f : ZMod (q * r) → ℂ := fun z =>
    star (kloostermanSum q (e z).1 n) * kloostermanSum r (e z).2 k
  rw [show (∑ m ∈ Finset.range (q * r),
      kloostermanCrossColumnProductTerm q r n k m) =
      ∑ m ∈ Finset.range (q * r), f (m : ZMod (q * r)) by
    apply Finset.sum_congr rfl
    intro m _hm
    simp [kloostermanCrossColumnProductTerm, f, e, ZMod.chineseRemainder]]
  rw [sum_range_natCast_zmod (q * r)]
  rw [Fintype.sum_equiv e.toEquiv f (fun z => f (e.symm z)) (fun _ => by simp)]
  simp only [f, e.apply_symm_apply]
  exact kloostermanCoprimeProductPeriodCorrelation_eq_zero q r hq hr n k

/-- For coprime nontrivial moduli, whole interval correlation equals its product-period boundary
discrepancy; there is no cross-modulus bulk term. -/
theorem kloostermanCrossIntervalColumnCorrelation_eq_remainder
    (M q r : ℕ) [NeZero q] [NeZero r]
    (hq : 1 < q) (hr : 1 < r) (hcop : Nat.Coprime q r)
    (n : ZMod q) (k : ZMod r) :
    kloostermanCrossIntervalColumnCorrelation M q r n k =
      kloostermanCrossIntervalColumnRemainder M q r n k := by
  rw [kloostermanCrossIntervalColumnCorrelation_eq_residueMultiplicity]
  have hzero := sum_range_kloostermanCrossColumnProductTerm_eq_zero
    q r hq hr hcop n k
  calc
    (∑ s ∈ Finset.range (q * r),
        (kloostermanResidueMultiplicity M (q * r) s : ℂ) *
          kloostermanCrossColumnProductTerm q r n k s) =
        ((((M : ℝ) / ((q * r : ℕ) : ℝ) : ℝ) : ℂ) *
          ∑ s ∈ Finset.range (q * r), kloostermanCrossColumnProductTerm q r n k s) +
          kloostermanCrossIntervalColumnRemainder M q r n k := by
      unfold kloostermanCrossIntervalColumnRemainder kloostermanResidueDeviation
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro s _hs
      push_cast
      ring
    _ = kloostermanCrossIntervalColumnRemainder M q r n k := by
      rw [hzero, mul_zero, zero_add]

/-- Elementary uniform boundary budget.  It is uniform in interval length but grows with both
moduli. -/
theorem norm_kloostermanCrossIntervalColumnRemainder_le
    (M q r : ℕ) [NeZero q] [NeZero r]
    (n : ZMod q) (k : ZMod r) :
    ‖kloostermanCrossIntervalColumnRemainder M q r n k‖ ≤
      (q * r : ℝ) * Nat.totient q * Nat.totient r := by
  have hqr : 0 < q * r := Nat.mul_pos
    (Nat.pos_of_ne_zero (NeZero.ne q)) (Nat.pos_of_ne_zero (NeZero.ne r))
  calc
    ‖kloostermanCrossIntervalColumnRemainder M q r n k‖ ≤
        ∑ s ∈ Finset.range (q * r),
          ‖(kloostermanResidueDeviation M (q * r) s : ℂ) *
            kloostermanCrossColumnProductTerm q r n k s‖ := by
      unfold kloostermanCrossIntervalColumnRemainder
      exact norm_sum_le _ _
    _ ≤ ∑ _s ∈ Finset.range (q * r),
        ((Nat.totient q : ℝ) * Nat.totient r) := by
      apply Finset.sum_le_sum
      intro s hs
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      unfold kloostermanCrossColumnProductTerm
      rw [norm_mul, norm_star]
      calc
        |kloostermanResidueDeviation M (q * r) s| *
            (‖kloostermanSum q (s : ZMod q) n‖ *
              ‖kloostermanSum r (s : ZMod r) k‖) ≤
            1 * ((Nat.totient q : ℝ) * Nat.totient r) := by
          gcongr
          · exact abs_kloostermanResidueDeviation_le_one M (q * r) s hqr
              (Finset.mem_range.mp hs)
          · exact norm_kloostermanSum_le_totient q _ _
          · exact norm_kloostermanSum_le_totient r _ _
        _ = _ := one_mul _
    _ = (q * r : ℝ) * Nat.totient q * Nat.totient r := by
      simp
      ring

/-- Existing ordinary-index correlation on `[1,M]` is the cross-column carrier with positive
moduli `q+1` and `r+1`. -/
theorem kloostermanCrossModulusCorrelation_Icc_eq_crossInterval
    (M q r : ℕ) (n k : ℤ) :
    kloostermanCrossModulusCorrelation (Finset.Icc 1 M) q r n k =
      kloostermanCrossIntervalColumnCorrelation M (q + 1) (r + 1)
        (Int.cast n) (Int.cast k) := by
  rfl

/-- Exact zero-bulk completion for the stored ordinary-index carrier. -/
theorem kloostermanCrossModulusCorrelation_Icc_eq_coprime_remainder
    (M q r : ℕ) (hq : 0 < q) (hr : 0 < r)
    (hcop : Nat.Coprime (q + 1) (r + 1)) (n k : ℤ) :
    kloostermanCrossModulusCorrelation (Finset.Icc 1 M) q r n k =
      kloostermanCrossIntervalColumnRemainder M (q + 1) (r + 1)
        (Int.cast n) (Int.cast k) := by
  rw [kloostermanCrossModulusCorrelation_Icc_eq_crossInterval]
  exact kloostermanCrossIntervalColumnCorrelation_eq_remainder M (q + 1) (r + 1)
    (by omega) (by omega) hcop (Int.cast n) (Int.cast k)

/-- Ordinary-index cross-modulus carrier vanishes on one complete coprime product period. -/
theorem kloostermanCrossModulusCorrelation_range_mul_eq_zero
    (q r : ℕ) (hq : 0 < q) (hr : 0 < r)
    (hcop : Nat.Coprime (q + 1) (r + 1)) (n k : ℤ) :
    kloostermanCrossModulusCorrelation (Finset.range ((q + 1) * (r + 1))) q r n k = 0 := by
  let Q := q + 1
  let R := r + 1
  have hQ : 1 < Q := by omega
  have hR : 1 < R := by omega
  letI : NeZero Q := ⟨Nat.ne_of_gt (lt_trans Nat.zero_lt_one hQ)⟩
  letI : NeZero R := ⟨Nat.ne_of_gt (lt_trans Nat.zero_lt_one hR)⟩
  letI : NeZero (Q * R) := ⟨Nat.mul_ne_zero (NeZero.ne Q) (NeZero.ne R)⟩
  let e : ZMod (Q * R) ≃+* ZMod Q × ZMod R := ZMod.chineseRemainder hcop
  let f : ZMod (Q * R) → ℂ := fun z =>
    star (kloostermanSum Q (e z).1 (Int.cast n)) *
      kloostermanSum R (e z).2 (Int.cast k)
  rw [kloostermanCrossModulusCorrelation]
  change (∑ m ∈ Finset.range (Q * R),
      star (kloostermanSum Q (Int.cast m) (Int.cast n)) *
        kloostermanSum R (Int.cast m) (Int.cast k)) = 0
  rw [show (∑ m ∈ Finset.range (Q * R),
      star (kloostermanSum Q (Int.cast m) (Int.cast n)) *
        kloostermanSum R (Int.cast m) (Int.cast k)) =
      ∑ m ∈ Finset.range (Q * R), f (m : ZMod (Q * R)) by
    apply Finset.sum_congr rfl
    intro m _hm
    simp [f, e, ZMod.chineseRemainder]]
  rw [sum_range_natCast_zmod (Q * R)]
  rw [Fintype.sum_equiv e.toEquiv f (fun z => f (e.symm z)) (fun _ => by simp)]
  simp only [f, e.apply_symm_apply]
  exact kloostermanCoprimeProductPeriodCorrelation_eq_zero Q R hQ hR _ _

end

end RHTower.Sieve
