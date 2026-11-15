import Mathlib.RingTheory.Valuation.Basic
import Mathlib.Algebra.Order.GroupWithZero.Canonical
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Linarith


/-!
# Integral coordinates in uniformizer power expansions

In a sum `∑ i < N, cᵢ^N π^i`, with a uniformizer `π`, nonzero terms
have distinct valuation classes modulo `N`. Thus cancellation cannot
conceal a pole in any coefficient. This applies in particular to
Frobenius power expansions in positive characteristic.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri

/-- Distinct representatives below `N` cannot differ by an integer multiple of `N`. -/
theorem integer_powerCoordinate_unique (N : ℕ) (i j : Fin N) (a b : ℤ)
    (h : (N : ℤ) * a - i.val = (N : ℤ) * b - j.val) : i = j := by
  have hi0 : (0 : ℤ) ≤ i.val := Nat.cast_nonneg _
  have hj0 : (0 : ℤ) ≤ j.val := Nat.cast_nonneg _
  have hiN : (i.val : ℤ) < N := by exact_mod_cast i.isLt
  have hjN : (j.val : ℤ) < N := by exact_mod_cast j.isLt
  have hN : (0 : ℤ) ≤ N := Nat.cast_nonneg _
  rcases lt_trichotomy a b with hab | rfl | hba
  · have hmul := mul_le_mul_of_nonneg_left (show a + 1 ≤ b by omega) hN
    exfalso
    nlinarith only [h, hmul, hi0, hjN]
  · apply Fin.ext
    exact_mod_cast (show (i.val : ℤ) = j.val by linarith only [h])
  · have hmul := mul_le_mul_of_nonneg_left (show b + 1 ≤ a by omega) hN
    exfalso
    nlinarith only [h, hmul, hj0, hiN]

/-- The exponent of a power-coordinate term records its index modulo the power. -/
theorem valuation_powerCoordinate {L : Type*} [Field L]
    (v : Valuation L (WithZero (Multiplicative ℤ))) (π : L)
    (hπ : v π = WithZero.exp (-1 : ℤ)) (N : ℕ) (c : Fin N → L)
    (i : Fin N) (hi : v (c i) ≠ 0) :
    v (c i ^ N * π ^ i.val) = WithZero.exp ((N : ℤ) * WithZero.log (v (c i)) - i.val) := by
  rw [map_mul, map_pow, map_pow, hπ, ← WithZero.exp_log hi,
    ← WithZero.exp_nsmul, ← WithZero.exp_nsmul, ← WithZero.exp_add]
  congr 1
  simp only [nsmul_eq_mul, WithZero.log_exp]
  ring

/-- With distinct nonzero term values, any bound on a finite sum bounds every term. -/
theorem valuation_terms_le_of_separated {L ι : Type*} [Field L] [DecidableEq ι]
    (v : Valuation L (WithZero (Multiplicative ℤ))) (s : Finset ι) (f : ι → L)
    (hsep : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → v (f i) = v (f j) → v (f i) = 0)
    (a : WithZero (Multiplicative ℤ))
    (hsum : v (∑ i ∈ s, f i) ≤ a) : ∀ i ∈ s, v (f i) ≤ a := by
  intro i hi
  by_contra hbad
  have hfi : a < v (f i) := lt_of_not_ge hbad
  obtain ⟨j, hj, hmax⟩ := Finset.exists_max_image s (fun j => v (f j)) ⟨i, hi⟩
  have hfj : a < v (f j) := lt_of_lt_of_le hfi (hmax i hi)
  have hfj0 : v (f j) ≠ 0 := ne_of_gt (lt_of_le_of_lt zero_le hfj)
  have hstrict : ∀ k ∈ s \ {j}, v (f k) < v (f j) := by
    intro k hk
    have hkj : k ≠ j := by
      simpa only [Finset.mem_singleton] using (Finset.mem_sdiff.mp hk).2
    rcases lt_or_eq_of_le (hmax k (Finset.mem_sdiff.mp hk).1) with hlt | heq
    · exact hlt
    · exact (hfj0 (heq.symm.trans
        (hsep k (Finset.mem_sdiff.mp hk).1 j hj hkj heq))).elim
  rw [v.map_sum_eq_of_lt hj hstrict] at hsum
  exact (not_lt_of_ge hsum) hfj

/-- In a separated finite sum, integrality of the sum forces integrality of every term. -/
theorem valuation_terms_le_one_of_separated {L ι : Type*} [Field L] [DecidableEq ι]
    (v : Valuation L (WithZero (Multiplicative ℤ))) (s : Finset ι) (f : ι → L)
    (hsep : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → v (f i) = v (f j) → v (f i) = 0)
    (hsum : v (∑ i ∈ s, f i) ≤ 1) : ∀ i ∈ s, v (f i) ≤ 1 :=
  valuation_terms_le_of_separated v s f hsep 1 hsum

/-- An integral uniformizer power expansion has integral coefficients, independently of characteristic. -/
theorem valuation_powerCoordinates_le_one {L : Type*} [Field L]
    (v : Valuation L (WithZero (Multiplicative ℤ))) (π : L)
    (hπ : v π = WithZero.exp (-1 : ℤ)) (N : ℕ) (c : Fin N → L)
    (hsum : v (∑ i : Fin N, c i ^ N * π ^ i.val) ≤ 1) :
    ∀ i, v (c i) ≤ 1 := by
  classical
  let f : Fin N → L := fun j => c j ^ N * π ^ j.val
  have hsep : ∀ i ∈ Finset.univ, ∀ j ∈ Finset.univ,
      i ≠ j → v (f i) = v (f j) → v (f i) = 0 := by
    intro i _ j _ hij heq
    have hN : N ≠ 0 := Nat.ne_zero_of_lt i.isLt
    by_cases hci : v (c i) = 0
    · simp only [f, map_mul, map_pow, hci, zero_pow hN, zero_mul]
    · exfalso
      have hfi0 : v (f i) ≠ 0 := by
        rw [valuation_powerCoordinate v π hπ N c i hci]
        exact WithZero.exp_ne_zero
      have hcj : v (c j) ≠ 0 := by
        intro h
        apply hfi0
        rw [heq]
        simp only [f, map_mul, map_pow, h, zero_pow hN, zero_mul]
      rw [valuation_powerCoordinate v π hπ N c i hci,
        valuation_powerCoordinate v π hπ N c j hcj] at heq
      have hle := heq.le
      have hge := heq.ge
      rw [WithZero.exp_le_exp] at hle hge
      exact hij (integer_powerCoordinate_unique N i j _ _ (le_antisymm hle hge))
  have hterms := valuation_terms_le_one_of_separated v Finset.univ f hsep hsum
  intro i
  by_contra hbad
  have hi : 1 < v (c i) := lt_of_not_ge hbad
  have hci : v (c i) ≠ 0 := ne_of_gt (lt_trans zero_lt_one hi)
  have hlog : 1 ≤ WithZero.log (v (c i)) := by
    rw [← WithZero.exp_log hci, ← WithZero.exp_zero, WithZero.exp_lt_exp] at hi
    omega
  have hiN : (i.val : ℤ) < N := by exact_mod_cast i.isLt
  have hfi : 1 < v (f i) := by
    rw [valuation_powerCoordinate v π hπ N c i hci, ← WithZero.exp_zero, WithZero.exp_lt_exp]
    have hmul := mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg N : (0 : ℤ) ≤ N)
    nlinarith only [hmul, hiN]
  exact (not_lt_of_ge (hterms i (Finset.mem_univ i))) hfi

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
