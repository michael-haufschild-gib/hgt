import GaloisForLFunctions.RHTower.Sieve.MaynardCanonicalDefectExcision

/-!
# Exact removal of length-one Heath--Brown atoms

Dyadic exponent zero represents length one.  Möbius and zeta atoms at that exponent are exact
multiplicative units; the logarithm atom is exactly zero.  Thus every nonzero selected box has a
positive logarithm exponent, and all remaining exponent-zero atoms can be removed without changing
the box product, lower edge, or logarithmic slack mass.
-/

noncomputable section
namespace RHTower.Sieve

open Finset ArithmeticFunction Complex

theorem arithmeticDyadicBlock_truncatedMoebius_zero_eq_one
    (L : ℕ) (hL : 1 ≤ L) :
    arithmeticDyadicBlock (truncatedMoebius L) 0 = 1 := by
  ext n
  rcases n with _ | n
  · simp
  · by_cases hn : n = 0
    · subst n
      simp [hL]
    · have hn2 : 2 ≤ n + 1 := by omega
      have hn1 : n + 1 ≠ 1 := by omega
      have hlog : 0 < Nat.log 2 (n + 1) := Nat.log_pos (by norm_num) hn2
      rw [arithmeticDyadicBlock_apply, if_neg (ne_of_gt hlog),
        ArithmeticFunction.one_apply, if_neg hn1]

theorem arithmeticDyadicBlock_coeffTrunc_zeta_zero_eq_one
    (X : ℕ) (hX : 1 ≤ X) :
    arithmeticDyadicBlock (coeffTrunc (zeta : ArithmeticFunction ℝ) X) 0 = 1 := by
  ext n
  rcases n with _ | n
  · simp
  · by_cases hn : n = 0
    · subst n
      simp [hX]
    · have hn2 : 2 ≤ n + 1 := by omega
      have hn1 : n + 1 ≠ 1 := by omega
      have hlog : 0 < Nat.log 2 (n + 1) := Nat.log_pos (by norm_num) hn2
      rw [arithmeticDyadicBlock_apply, if_neg (ne_of_gt hlog),
        ArithmeticFunction.one_apply, if_neg hn1]

theorem arithmeticDyadicBlock_coeffTrunc_log_zero_eq_zero
    (X : ℕ) :
    arithmeticDyadicBlock (coeffTrunc ArithmeticFunction.log X) 0 = 0 := by
  ext n
  rcases n with _ | n
  · simp
  · by_cases hn : n = 0
    · subst n
      simp
    · have hn2 : 2 ≤ n + 1 := by omega
      have hlog : 0 < Nat.log 2 (n + 1) := Nat.log_pos (by norm_num) hn2
      simp [arithmeticDyadicBlock_apply, ne_of_gt hlog]

theorem LSeries_truncatedMoebiusDyadicBlock_zero_eq_one
    (L : ℕ) (hL : 1 ≤ L) (s : ℂ) :
    LSeries (complexCoeff (arithmeticDyadicBlock (truncatedMoebius L) 0)) s = 1 := by
  rw [arithmeticDyadicBlock_truncatedMoebius_zero_eq_one L hL]
  exact LSeries_complexCoeff_one s

theorem LSeries_coeffTrunc_zetaDyadicBlock_zero_eq_one
    (X : ℕ) (hX : 1 ≤ X) (s : ℂ) :
    LSeries (complexCoeff
      (arithmeticDyadicBlock (coeffTrunc (zeta : ArithmeticFunction ℝ) X) 0)) s = 1 := by
  rw [arithmeticDyadicBlock_coeffTrunc_zeta_zero_eq_one X hX]
  exact LSeries_complexCoeff_one s

theorem LSeries_coeffTrunc_logDyadicBlock_zero_eq_zero
    (X : ℕ) (s : ℂ) :
    LSeries (complexCoeff
      (arithmeticDyadicBlock (coeffTrunc ArithmeticFunction.log X) 0)) s = 0 := by
  rw [arithmeticDyadicBlock_coeffTrunc_log_zero_eq_zero X]
  have hzero : complexCoeff (0 : ArithmeticFunction ℝ) = 0 := by
    funext n
    simp [complexCoeff_apply]
  rw [hzero]
  exact congrFun LSeries_zero s

/-- Exponent-zero atoms in a box with a positive logarithm exponent are exact units. -/
theorem heathBrownBoxFactorValue_eq_one_of_exponent_eq_zero
    {L X k : ℕ} (box : HeathBrownBoxChoice L X k)
    (hL : 1 ≤ L) (hX : 1 ≤ X) (hlog : 1 ≤ box.q) (s : ℂ)
    (i : HeathBrownBoxFactorIndex k box.m)
    (hi : heathBrownBoxFactorExponent box.a box.b box.q i = 0) :
    heathBrownBoxFactorValue L X k box s i = 1 := by
  rcases i with i | i
  · change LSeries (complexCoeff
      (arithmeticDyadicBlock (truncatedMoebius L) (box.a i))) s = 1
    have hai : box.a i = 0 := by
      simpa [heathBrownBoxFactorExponent] using hi
    rw [hai]
    exact LSeries_truncatedMoebiusDyadicBlock_zero_eq_one L hL s
  · rcases i with i | i
    · change LSeries (complexCoeff
        (arithmeticDyadicBlock
          (coeffTrunc (zeta : ArithmeticFunction ℝ) X) (box.b i))) s = 1
      have hbi : box.b i = 0 := by
        simpa [heathBrownBoxFactorExponent] using hi
      rw [hbi]
      exact LSeries_coeffTrunc_zetaDyadicBlock_zero_eq_one X hX s
    · rcases i with ⟨⟩
      simp [heathBrownBoxFactorExponent] at hi
      omega

/-- A box above any positive multiplicative threshold cannot contain the zero logarithm atom. -/
theorem heathBrownBox_log_exponent_pos_of_large_core
    {L X k : ℕ} (box : HeathBrownBoxChoice L X k) {c alpha : ℝ} (s : ℂ)
    (hlarge :
      ((groupedDyadicLower
        (heathBrownBoxFactorExponent box.a box.b box.q) : ℕ) : ℝ) ^ (alpha - c) ≤
        ‖heathBrownDyadicCoreProduct L X k box.m box.a box.b box.q s‖) :
    1 ≤ box.q := by
  by_contra hnot
  have hq : box.q = 0 := by omega
  have hlogzero := LSeries_coeffTrunc_logDyadicBlock_zero_eq_zero X s
  have hcorezero :
      heathBrownDyadicCoreProduct L X k box.m box.a box.b box.q s = 0 := by
    simp [heathBrownDyadicCoreProduct, hq, hlogzero]
  have hD0 : 0 <
      ((groupedDyadicLower
        (heathBrownBoxFactorExponent box.a box.b box.q) : ℕ) : ℝ) := by
    exact_mod_cast (show 0 < groupedDyadicLower
      (heathBrownBoxFactorExponent box.a box.b box.q) by
        exact lt_of_lt_of_le Nat.zero_lt_one
          (one_le_groupedDyadicLower
            (heathBrownBoxFactorExponent box.a box.b box.q)))
  have hthreshold : 0 <
      ((groupedDyadicLower
        (heathBrownBoxFactorExponent box.a box.b box.q) : ℕ) : ℝ) ^ (alpha - c) :=
    Real.rpow_pos_of_pos hD0 _
  rw [hcorezero, norm_zero] at hlarge
  linarith

/-- Positive-length atoms of a literal box. -/
abbrev PositiveHeathBrownBoxFactorIndex
    {L X k : ℕ} (box : HeathBrownBoxChoice L X k) :=
  {i : HeathBrownBoxFactorIndex k box.m //
    1 ≤ heathBrownBoxFactorExponent box.a box.b box.q i}

/-- Removing exponent-zero atoms leaves the multiplicative lower edge unchanged. -/
theorem prod_positive_heathBrownBoxFactorLength_eq_groupedLower
    {L X k : ℕ} (box : HeathBrownBoxChoice L X k) :
    (∏ i : PositiveHeathBrownBoxFactorIndex box,
      2 ^ heathBrownBoxFactorExponent box.a box.b box.q i) =
      groupedDyadicLower (heathBrownBoxFactorExponent box.a box.b box.q) := by
  classical
  let u : Finset (HeathBrownBoxFactorIndex k box.m) :=
    Finset.univ.filter fun i =>
      1 ≤ heathBrownBoxFactorExponent box.a box.b box.q i
  have hu (i : HeathBrownBoxFactorIndex k box.m) : i ∈ u ↔
      1 ≤ heathBrownBoxFactorExponent box.a box.b box.q i := by
    simp [u]
  have hreindex := Finset.prod_subtype
    (F := Subtype.fintype fun i : HeathBrownBoxFactorIndex k box.m =>
      1 ≤ heathBrownBoxFactorExponent box.a box.b box.q i) u hu
    (fun i => 2 ^ heathBrownBoxFactorExponent box.a box.b box.q i)
  calc
    (∏ i : PositiveHeathBrownBoxFactorIndex box, 2 ^
        heathBrownBoxFactorExponent box.a box.b box.q i) =
        ∏ i ∈ u, 2 ^ heathBrownBoxFactorExponent box.a box.b box.q i := by
          simpa [PositiveHeathBrownBoxFactorIndex] using hreindex.symm
    _ = ∏ i : HeathBrownBoxFactorIndex k box.m,
        2 ^ heathBrownBoxFactorExponent box.a box.b box.q i := by
      apply Finset.prod_subset (Finset.filter_subset _ _)
      intro i _hi hiu
      have hqi : heathBrownBoxFactorExponent box.a box.b box.q i = 0 := by
        have : ¬ 1 ≤ heathBrownBoxFactorExponent box.a box.b box.q i := by
          simpa [u] using hiu
        omega
      simp [hqi]
    _ = groupedDyadicLower
        (heathBrownBoxFactorExponent box.a box.b box.q) := by
      simp [groupedDyadicLower]

/-- Removing exponent-zero atoms leaves the exact complex box product unchanged. -/
theorem prod_positive_heathBrownBoxFactorValue_eq_core
    {L X k : ℕ} (box : HeathBrownBoxChoice L X k)
    (hL : 1 ≤ L) (hX : 1 ≤ X) (hlog : 1 ≤ box.q) (s : ℂ) :
    (∏ i : PositiveHeathBrownBoxFactorIndex box,
      heathBrownBoxFactorValue L X k box s i) =
      heathBrownDyadicCoreProduct L X k box.m box.a box.b box.q s := by
  classical
  let u : Finset (HeathBrownBoxFactorIndex k box.m) :=
    Finset.univ.filter fun i =>
      1 ≤ heathBrownBoxFactorExponent box.a box.b box.q i
  have hu (i : HeathBrownBoxFactorIndex k box.m) : i ∈ u ↔
      1 ≤ heathBrownBoxFactorExponent box.a box.b box.q i := by
    simp [u]
  have hreindex := Finset.prod_subtype
    (F := Subtype.fintype fun i : HeathBrownBoxFactorIndex k box.m =>
      1 ≤ heathBrownBoxFactorExponent box.a box.b box.q i) u hu
    (heathBrownBoxFactorValue L X k box s)
  calc
    (∏ i : PositiveHeathBrownBoxFactorIndex box,
        heathBrownBoxFactorValue L X k box s i) =
        ∏ i ∈ u, heathBrownBoxFactorValue L X k box s i := by
          simpa [PositiveHeathBrownBoxFactorIndex] using hreindex.symm
    _ = ∏ i : HeathBrownBoxFactorIndex k box.m,
        heathBrownBoxFactorValue L X k box s i := by
      apply Finset.prod_subset (Finset.filter_subset _ _)
      intro i _hi hiu
      have hqi : heathBrownBoxFactorExponent box.a box.b box.q i = 0 := by
        have : ¬ 1 ≤ heathBrownBoxFactorExponent box.a box.b box.q i := by
          simpa [u] using hiu
        omega
      exact heathBrownBoxFactorValue_eq_one_of_exponent_eq_zero
        box hL hX hlog s i hqi
    _ = heathBrownDyadicCoreProduct L X k box.m box.a box.b box.q s := by
      simpa [heathBrownBoxFactorValue] using heathBrownBoxFactorProduct_eq_core
        L X k box.m box.a box.b box.q s

end RHTower.Sieve
