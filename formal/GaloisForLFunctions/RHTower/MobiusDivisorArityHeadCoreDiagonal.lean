import GaloisForLFunctions.RHTower.MobiusDivisorArityHeadEmptyOrientation

/-!
# Processed-core diagonal of the arity-head charge

The literal source-pair charge separates exactly into pairs which preserve the
processed prime core and pairs which change it.  The former still have the
empty-core Möbius orientation: preservation of the core forces a literal
prime shift.  Thus every same-core term is dissipative.  The only unresolved
part of the nonempty-core charge is the explicitly isolated core-changing
covariance.
-/

noncomputable section
open Finset
namespace RHTower

private lemma primeFactors_eq_insert_of_same_processedCore
    {P : Finset ℕ} {p d e : ℕ}
    (hpD : p ∉ d.primeFactors \ P)
    (hres : e.primeFactors \ P = insert p (d.primeFactors \ P))
    (hcore : e.primeFactors ∩ P = d.primeFactors ∩ P) :
    e.primeFactors = insert p d.primeFactors := by
  have hpP : p ∉ P := by
    intro hpP
    have hpE : p ∈ e.primeFactors \ P := by
      rw [hres]
      exact mem_insert_self _ _
    exact (mem_sdiff.mp hpE).2 hpP
  ext q
  by_cases hqP : q ∈ P
  · calc
      q ∈ e.primeFactors ↔ q ∈ e.primeFactors ∩ P := by simp [hqP]
      _ ↔ q ∈ d.primeFactors ∩ P := by rw [hcore]
      _ ↔ q ∈ d.primeFactors := by simp [hqP]
      _ ↔ q ∈ insert p d.primeFactors := by
        simp only [mem_insert]
        constructor
        · exact Or.inr
        · rintro (rfl | hq)
          · exact (hpP hqP).elim
          · exact hq
  · calc
      q ∈ e.primeFactors ↔ q ∈ e.primeFactors \ P := by simp [hqP]
      _ ↔ q ∈ insert p (d.primeFactors \ P) := by rw [hres]
      _ ↔ q ∈ insert p d.primeFactors := by simp [hqP]

private lemma sameProcessedCore_adjacent_eq_prime_mul
    {M : ℕ} {P : Finset ℕ} {p d e : ℕ}
    (hd : d ∈ mobiusDivisorSelectionIndices M)
    (he : e ∈ mobiusDivisorSelectionIndices M)
    (hpD : p ∉ d.primeFactors \ P)
    (hres : e.primeFactors \ P = insert p (d.primeFactors \ P))
    (hcore : e.primeFactors ∩ P = d.primeFactors ∩ P) :
    e = p * d := by
  have hfac := primeFactors_eq_insert_of_same_processedCore hpD hres hcore
  have hpP : p ∉ P := by
    intro hpP
    have hpE : p ∈ e.primeFactors \ P := by
      rw [hres]
      exact mem_insert_self _ _
    exact (mem_sdiff.mp hpE).2 hpP
  have hpD' : p ∉ d.primeFactors := by
    intro hp
    exact hpD (mem_sdiff.mpr ⟨hp, hpP⟩)
  have hds : Squarefree d := (mem_filter.mp hd).2
  have hes : Squarefree e := (mem_filter.mp he).2
  calc
    e = ∏ q ∈ e.primeFactors, q := (Nat.prod_primeFactors_of_squarefree hes).symm
    _ = ∏ q ∈ insert p d.primeFactors, q := by rw [hfac]
    _ = p * ∏ q ∈ d.primeFactors, q := prod_insert hpD'
    _ = p * d := by rw [Nat.prod_primeFactors_of_squarefree hds]

/-- Every legal source pair preserving its processed core is a negative product
of unsigned channels. -/
theorem mobiusDivisorArityHead_sameProcessedCore_product_eq_neg_unsigned
    (M : ℕ) (P : Finset ℕ) (p d e : ℕ) (hp : p.Prime)
    (hd : d ∈ mobiusDivisorSelectionIndices M)
    (he : e ∈ mobiusDivisorSelectionIndices M)
    (hpD : p ∉ d.primeFactors \ P)
    (hres : e.primeFactors \ P = insert p (d.primeFactors \ P))
    (hcore : e.primeFactors ∩ P = d.primeFactors ∩ P) :
    mobiusDivisorDilationChannel M d * mobiusDivisorDilationChannel M e =
      -divisorUnsignedDilationChannel M d * divisorUnsignedDilationChannel M e := by
  have heq := sameProcessedCore_adjacent_eq_prime_mul hd he hpD hres hcore
  have hpP : p ∉ P := by
    intro hpP
    have hpE : p ∈ e.primeFactors \ P := by
      rw [hres]
      exact mem_insert_self _ _
    exact (mem_sdiff.mp hpE).2 hpP
  have hpD' : p ∉ d.primeFactors := by
    intro hp
    exact hpD (mem_sdiff.mpr ⟨hp, hpP⟩)
  subst e
  exact mobiusDivisorArityHead_primeShift_product_eq_neg_unsigned M p d hp hd hpD'

/-- The literal charge contribution of source pairs whose processed prime core
is unchanged. -/
def mobiusDivisorArityHeadCoreDiagonalCharge (M : ℕ) (P : Finset ℕ) (p : ℕ) : ℝ :=
  2 * ∑ d ∈ mobiusDivisorSelectionIndices M, ∑ e ∈ mobiusDivisorSelectionIndices M,
    if p ∉ d.primeFactors \ P ∧ e.primeFactors \ P = insert p (d.primeFactors \ P) ∧
        e.primeFactors ∩ P = d.primeFactors ∩ P then
      (((d.primeFactors \ P).card : ℝ) +
        if d.primeFactors \ P = ∅ then 1 else 0) *
          mobiusDivisorDilationChannel M d * mobiusDivisorDilationChannel M e
    else 0

/-- The complementary literal charge contribution, in which the processed
prime core changes.  This is the remaining CCM-FU covariance problem. -/
def mobiusDivisorArityHeadCoreChangingCharge (M : ℕ) (P : Finset ℕ) (p : ℕ) : ℝ :=
  2 * ∑ d ∈ mobiusDivisorSelectionIndices M, ∑ e ∈ mobiusDivisorSelectionIndices M,
    if p ∉ d.primeFactors \ P ∧ e.primeFactors \ P = insert p (d.primeFactors \ P) ∧
        e.primeFactors ∩ P ≠ d.primeFactors ∩ P then
      (((d.primeFactors \ P).card : ℝ) +
        if d.primeFactors \ P = ∅ then 1 else 0) *
          mobiusDivisorDilationChannel M d * mobiusDivisorDilationChannel M e
    else 0

/-- Exact decomposition: the nonempty-core charge is its dissipative
same-core diagonal plus the sole core-changing covariance. -/
theorem mobiusDivisorArityHeadCharge_eq_coreDiagonal_add_coreChanging
    (M : ℕ) (P : Finset ℕ) (p : ℕ) :
    mobiusDivisorArityHeadCharge M P p =
      mobiusDivisorArityHeadCoreDiagonalCharge M P p +
        mobiusDivisorArityHeadCoreChangingCharge M P p := by
  rw [mobiusDivisorArityHeadCharge_eq_pairs]
  unfold mobiusDivisorArityHeadCoreDiagonalCharge
    mobiusDivisorArityHeadCoreChangingCharge
  rw [← mul_add]
  congr 1
  rw [← Finset.sum_add_distrib]
  apply sum_congr rfl
  intro d hd
  rw [← Finset.sum_add_distrib]
  apply sum_congr rfl
  intro e he
  by_cases hlegal : p ∉ d.primeFactors \ P ∧
      e.primeFactors \ P = insert p (d.primeFactors \ P)
  · by_cases hcore : e.primeFactors ∩ P = d.primeFactors ∩ P <;>
      simp [hlegal, hcore]
  · have hdiag : ¬(p ∉ d.primeFactors \ P ∧
        e.primeFactors \ P = insert p (d.primeFactors \ P) ∧
          e.primeFactors ∩ P = d.primeFactors ∩ P) := by
      intro h
      exact hlegal ⟨h.1, h.2.1⟩
    have hchange : ¬(p ∉ d.primeFactors \ P ∧
        e.primeFactors \ P = insert p (d.primeFactors \ P) ∧
          e.primeFactors ∩ P ≠ d.primeFactors ∩ P) := by
      intro h
      exact hlegal ⟨h.1, h.2.1⟩
    rw [if_neg hlegal, if_neg hdiag, if_neg hchange]
    ring

/-- The same-processed-core part of every prime charge is nonpositive. -/
theorem mobiusDivisorArityHeadCoreDiagonalCharge_nonpos
    (M : ℕ) (P : Finset ℕ) {p : ℕ} (hp : p.Prime) :
    mobiusDivisorArityHeadCoreDiagonalCharge M P p ≤ 0 := by
  unfold mobiusDivisorArityHeadCoreDiagonalCharge
  apply mul_nonpos_of_nonneg_of_nonpos (by norm_num)
  apply sum_nonpos
  intro d hd
  apply sum_nonpos
  intro e he
  by_cases hlegal : p ∉ d.primeFactors \ P ∧
      e.primeFactors \ P = insert p (d.primeFactors \ P) ∧
        e.primeFactors ∩ P = d.primeFactors ∩ P
  · rw [if_pos hlegal]
    have hw : 0 ≤ ((d.primeFactors \ P).card : ℝ) +
        if d.primeFactors \ P = ∅ then 1 else 0 := by
      split_ifs <;> positivity
    have hprod := mobiusDivisorArityHead_sameProcessedCore_product_eq_neg_unsigned
      M P p d e hp hd he hlegal.1 hlegal.2.1 hlegal.2.2
    calc
      (((d.primeFactors \ P).card : ℝ) + if d.primeFactors \ P = ∅ then 1 else 0) *
          mobiusDivisorDilationChannel M d * mobiusDivisorDilationChannel M e =
          (((d.primeFactors \ P).card : ℝ) + if d.primeFactors \ P = ∅ then 1 else 0) *
            (mobiusDivisorDilationChannel M d * mobiusDivisorDilationChannel M e) := by ring
      _ = (((d.primeFactors \ P).card : ℝ) + if d.primeFactors \ P = ∅ then 1 else 0) *
            (-divisorUnsignedDilationChannel M d * divisorUnsignedDilationChannel M e) := by
              rw [hprod]
      _ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hw
        (mul_nonpos_of_nonpos_of_nonneg
          (neg_nonpos.mpr (divisorUnsignedDilationChannel_nonneg M d))
          (divisorUnsignedDilationChannel_nonneg M e))
  · rw [if_neg hlegal]

end RHTower
