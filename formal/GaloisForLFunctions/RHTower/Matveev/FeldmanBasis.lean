import GaloisForLFunctions.RHTower.Matveev.FeldmanBinomial
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.Polynomial.Degree.Operations

/-!
# The consecutive-product polynomials are an integer basis

A family containing one monic polynomial of each degree is a `ℤ`-basis of the integer polynomials:
subtracting the right multiple of the top member drops the degree, so every polynomial reduces in
finitely many steps.  Applying this to the consecutive products `(X+1)⋯(X+k)` turns any power `X^k`
into an integer combination of them.

That is the change of basis an auxiliary construction needs.  Vanishing conditions written in the
consecutive-product basis are *equivalent* to the same conditions written in the power basis — no
information is lost — while the matrix entries are smaller by the full factorial, since the
Fel'dman value is the consecutive product divided by `k!`.
-/

noncomputable section

namespace GaloisForLFunctions.RHTower.Matveev

open Finset Polynomial

/-- The integer polynomial `(X+1)(X+2)⋯(X+k)`. -/
def consecutivePoly (k : ℕ) : Polynomial ℤ :=
  ∏ j ∈ range k, (X + C ((j : ℤ) + 1))

@[simp] theorem consecutivePoly_zero : consecutivePoly 0 = 1 := by
  simp [consecutivePoly]

theorem consecutivePoly_monic (k : ℕ) : (consecutivePoly k).Monic :=
  monic_prod_of_monic _ _ fun _ _ => monic_X_add_C _

theorem consecutivePoly_natDegree (k : ℕ) : (consecutivePoly k).natDegree = k := by
  have h : (consecutivePoly k).natDegree
      = ∑ j ∈ range k, ((X + C ((j : ℤ) + 1)).natDegree) := by
    rw [consecutivePoly]
    exact natDegree_prod _ _ fun j _ => (monic_X_add_C ((j : ℤ) + 1)).ne_zero
  rw [h]
  simp only [natDegree_X_add_C, Finset.sum_const, card_range, smul_eq_mul, mul_one]

theorem consecutivePoly_eval (k : ℕ) (z : ℤ) :
    (consecutivePoly k).eval z = consecutiveProd k z := by
  rw [consecutivePoly, consecutiveProd, eval_prod]
  refine Finset.prod_congr rfl fun j _ => ?_
  simp [add_assoc]

/-- **Triangularity.**  Every integer polynomial of degree at most `n` is an integer combination of
the consecutive-product polynomials of degree at most `n`. -/
theorem exists_intCombination : ∀ (n : ℕ) (p : Polynomial ℤ), p.natDegree ≤ n →
    ∃ c : ℕ → ℤ, p = ∑ j ∈ range (n + 1), C (c j) * consecutivePoly j
  | 0, p, hp => by
      refine ⟨fun _ => p.coeff 0, ?_⟩
      rw [Finset.sum_range_one, consecutivePoly_zero, mul_one]
      exact eq_C_of_natDegree_le_zero hp
  | n + 1, p, hp => by
    by_cases hlow : p.natDegree ≤ n
    · obtain ⟨c, hc⟩ := exists_intCombination n p hlow
      refine ⟨fun j => if j ≤ n then c j else 0, ?_⟩
      rw [Finset.sum_range_succ]
      dsimp only
      rw [if_neg (by omega : ¬ n + 1 ≤ n), map_zero, zero_mul, add_zero, hc]
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [if_pos (by have := Finset.mem_range.mp hj; omega)]
    · have hdeg : p.natDegree = n + 1 := le_antisymm hp (by omega)
      set a : ℤ := p.coeff (n + 1) with ha
      set P : Polynomial ℤ := consecutivePoly (n + 1) with hP
      have hPdeg : P.natDegree = n + 1 := consecutivePoly_natDegree (n + 1)
      have hPtop : P.coeff (n + 1) = 1 := by
        have := (consecutivePoly_monic (n + 1)).coeff_natDegree
        rwa [hPdeg] at this
      have hq : (p - C a * P).natDegree ≤ n := by
        refine natDegree_le_iff_coeff_eq_zero.mpr fun m hm => ?_
        rw [coeff_sub, coeff_C_mul]
        rcases eq_or_lt_of_le (Nat.succ_le_of_lt (by exact_mod_cast hm) :
            n + 1 ≤ m) with hmeq | hmlt
        · rw [← hmeq, hPtop, ← ha]
          ring
        · rw [coeff_eq_zero_of_natDegree_lt (by omega : p.natDegree < m),
            coeff_eq_zero_of_natDegree_lt (by omega : P.natDegree < m)]
          ring
      obtain ⟨c, hc⟩ := exists_intCombination n (p - C a * P) hq
      refine ⟨fun j => if j ≤ n then c j else a, ?_⟩
      rw [Finset.sum_range_succ]
      dsimp only
      rw [if_neg (by omega : ¬ n + 1 ≤ n)]
      have hsum : ∑ j ∈ range (n + 1), C (if j ≤ n then c j else a) * consecutivePoly j
          = ∑ j ∈ range (n + 1), C (c j) * consecutivePoly j := by
        refine Finset.sum_congr rfl fun j hj => ?_
        rw [if_pos (by have := Finset.mem_range.mp hj; omega)]
      rw [hsum, ← hc, ← hP]
      ring

/-- **Powers in the consecutive-product basis.**  Every power is an integer combination. -/
theorem exists_pow_intCombination (k : ℕ) :
    ∃ c : ℕ → ℤ, (X : Polynomial ℤ) ^ k = ∑ j ∈ range (k + 1), C (c j) * consecutivePoly j :=
  exists_intCombination k (X ^ k) (by simp)

/-- The value form: every integer power is an integer combination of consecutive products. -/
theorem exists_pow_intCombination_eval (k : ℕ) :
    ∃ c : ℕ → ℤ, ∀ z : ℤ, z ^ k = ∑ j ∈ range (k + 1), c j * consecutiveProd j z := by
  obtain ⟨c, hc⟩ := exists_pow_intCombination k
  refine ⟨c, fun z => ?_⟩
  have h := congrArg (fun q : Polynomial ℤ => q.eval z) hc
  simp only [eval_pow, eval_X, eval_finsetSum, eval_mul, eval_C] at h
  rw [h]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [consecutivePoly_eval]

end GaloisForLFunctions.RHTower.Matveev
