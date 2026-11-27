import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TameKummerCharacters

/-! For a valuation above a rational prime, the value of every nonzero element
algebraic over the rationals has a positive power equal to an integral power
of the value of that prime. -/

noncomputable section

open Polynomial

namespace GlobalTheory.TameKummer

variable {K : Type} [Field K] [CharZero K] (A : ValuationSubring K) {p : ℕ} [Fact p.Prime]

omit [CharZero K] in
private theorem valuation_natCast_eq_pow (hp : A.valuation (p : K) < 1)
    {n : ℕ} (hn : n ≠ 0) :
    ∃ m : ℕ, A.valuation (n : K) = A.valuation (p : K) ^ m := by
  have hp' : p.Prime := Fact.out
  obtain ⟨m, a, ha, hna⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn p hp'.ne_one
  have hcop : p.Coprime a := hp'.coprime_iff_not_dvd.mpr ha
  have hu : A.valuation (a : K) = 1 := le_antisymm
    ((A.valuation_le_one_iff _).mpr (natCast_mem A a))
    (le_of_not_gt (natCast_valuation_not_lt_one A hp hcop))
  refine ⟨m, ?_⟩
  rw [hna, Nat.cast_mul, Nat.cast_pow, map_mul, map_pow, hu, mul_one]

/-- A vanished polynomial has two terms of maximal valuation. Comparing those
terms expresses the value of its root in terms of the underlying rational prime. -/
theorem exists_pow_valuation_eq_zpow (hp : A.valuation (p : K) < 1)
    {x : K} (hx : x ≠ 0) (hAlg : IsAlgebraic ℤ x) :
    ∃ (m : ℕ) (k : ℤ), m ≠ 0 ∧ A.valuation x ^ m = A.valuation (p : K) ^ k := by
  obtain ⟨f, hf, hfx⟩ := hAlg
  have hcoeff (a : ℤ) (ha : a ≠ 0) : ∃ m : ℕ, A.valuation (a : K) = A.valuation (p : K) ^ m := by
    obtain ⟨m, hm⟩ := valuation_natCast_eq_pow A hp (Int.natAbs_ne_zero.mpr ha)
    refine ⟨m, ?_⟩
    rw [← hm]
    rcases Int.natAbs_eq a with he | he
    · conv_lhs => rw [he]
      simp
    · conv_lhs => rw [he]
      simp
  have hvx : A.valuation x ≠ 0 := by simpa using hx
  have hvp : A.valuation (p : K) ≠ 0 := by simpa using (Fact.out : p.Prime).ne_zero
  let t (i : ℕ) : K := (f.coeff i : K) * x ^ i
  have hsum : ∑ i ∈ f.support, t i = 0 := by
    rw [← hfx, aeval_def, eval₂_eq_sum, sum_def]
    simp [t]
  obtain ⟨i, hi, hmax⟩ := f.support.exists_max_image (fun j => A.valuation (t j))
    (support_nonempty.mpr hf)
  have hti : A.valuation (t i) ≠ 0 := by
    simp [t, mem_support_iff.mp hi, hx]
  obtain ⟨j, hj, hji, he⟩ : ∃ j ∈ f.support, j ≠ i ∧ A.valuation (t j) = A.valuation (t i) := by
    by_contra h
    have hlt : A.valuation (∑ j ∈ f.support.erase i, t j) < A.valuation (t i) :=
      Valuation.map_sum_lt _ hti fun j hj =>
        lt_of_le_of_ne (hmax j (Finset.mem_of_mem_erase hj))
          (fun he => h ⟨j, Finset.mem_of_mem_erase hj, Finset.ne_of_mem_erase hj, he⟩)
    rw [← Finset.add_sum_erase _ _ hi, add_eq_zero_iff_eq_neg] at hsum
    rw [hsum, Valuation.map_neg] at hlt
    exact lt_irrefl _ hlt
  have hcompare {i j : ℕ} (hi : i ∈ f.support) (hj : j ∈ f.support)
      (hij : i < j) (he : A.valuation (t j) = A.valuation (t i)) :
      ∃ (m : ℕ) (k : ℤ), m ≠ 0 ∧ A.valuation x ^ m = A.valuation (p : K) ^ k := by
    obtain ⟨a, ha⟩ := hcoeff _ (mem_support_iff.mp hi)
    obtain ⟨b, hb⟩ := hcoeff _ (mem_support_iff.mp hj)
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_lt hij
    refine ⟨m + 1, (a : ℤ) - b, Nat.succ_ne_zero _, ?_⟩
    simp only [t, map_mul, map_pow, ha, hb] at he
    rw [zpow_sub₀ hvp, zpow_natCast, zpow_natCast, eq_div_iff (pow_ne_zero _ hvp)]
    apply mul_right_cancel₀ (pow_ne_zero i hvx)
    rw [← he, add_assoc, pow_add (A.valuation x) i]
    ac_rfl
  rcases lt_or_gt_of_ne hji with h | h
  · exact hcompare hj hi h he.symm
  · exact hcompare hi hj h he

end GlobalTheory.TameKummer
