import GaloisForLFunctions.RenormalizedIntersectionTheory.TheWirsingBoundForFlipTwins
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.MertensTheoremInResidueClasses

/-!
# The residue-class twins are separated

Flip the primes of one unit class `r mod q`. Both the flipped and the unflipped primes have divergent
reciprocal sums, so neither the finite-flip nor the summable-flip mechanisms apply. Mertens' theorem
in residue classes (`RenormalizedArithmeticPotentialTheory.exists_abs_classMertensSum_sub_le`) gives
the flipped primes the relative logarithmic density `1/φ(q)`
(`exists_abs_primeSetLogMass_residueClassPrimes_sub_le`), and the Wirsing bound applies:

* `|Σ_{n ≤ N} ω(n)/n| ≪ (log N)^{b − 1}` for every `b ≥ 1`, `b > 2 − 2/φ(q)`
  (`exists_abs_gaugeHarmonicSum_residueClassFlip_le`);
* for `φ(q) < 4` (`q = 3, 4, 6`, and `q = 1, 2`) the twin has margin `0` and the atomic Hodge index
  separates it from `ζ` (`hodgeSeparates_residueClassFlip`); in particular the twins flipping the
  primes `≡ 1 (mod 4)` or the primes `≡ 3 (mod 4)`.
-/

open Finset
open scoped ArithmeticFunction.vonMangoldt
open GaloisForLFunctions.SelectiveMultiscaleArithmeticPositivity (gaugeHarmonicSum)
open GaloisForLFunctions.ArithmeticCountingPositivity (primeSetFlip)
open GaloisForLFunctions.RenormalizedArithmeticPotentialTheory (classMertensSum
  exists_abs_classMertensSum_sub_le)

noncomputable section

namespace GaloisForLFunctions.RenormalizedIntersectionTheory

/-- The primes in the residue class `r mod q`. -/
def residueClassPrimes (q : ℕ) (r : ZMod q) : Set ℕ := {p | p.Prime ∧ (p : ZMod q) = r}

/-- **The flipped primes have relative logarithmic density `1/φ(q)`.** -/
theorem exists_abs_primeSetLogMass_residueClassPrimes_sub_le {q : ℕ} [NeZero q] {r : ZMod q}
    (hr : IsUnit r) :
    ∃ C : ℝ, ∀ n, 1 ≤ n →
      |primeSetLogMass (residueClassPrimes q r) n - (q.totient : ℝ)⁻¹ * Real.log n| ≤ C := by
  classical
  obtain ⟨C, hC⟩ := exists_abs_classMertensSum_sub_le hr
  refine ⟨C + (2 * (Real.log 4 + 4) + (8 + RHTower.Mertens.mertensTail)), fun n hn => ?_⟩
  set g : ℕ → ℝ := fun t => if (t : ZMod q) = r then Λ t / t else 0
  have hsplit := sum_filter_add_sum_filter_not (Icc 1 n) Nat.Prime g
  -- the prime terms are the logarithmic mass of the class
  have hprime : ∑ t ∈ Icc 1 n with t.Prime, g t = primeSetLogMass (residueClassPrimes q r) n := by
    rw [primeSetLogMass, primeSetCutoff_eq_filter, sum_filter (s := (Icc 1 n).filter Nat.Prime)]
    refine sum_congr rfl fun t ht => ?_
    have hp := (mem_filter.mp ht).2
    have hmem : t ∈ residueClassPrimes q r ↔ (t : ZMod q) = r := ⟨fun h => h.2, fun h => ⟨hp, h⟩⟩
    by_cases h : (t : ZMod q) = r
    · simp only [g, if_pos h, if_pos (hmem.mpr h), ArithmeticFunction.vonMangoldt_apply_prime hp]
    · simp only [g, if_neg h, if_neg (mt hmem.mp h)]
  -- the proper prime powers cost `O(1)`
  have hg0 : ∀ t, 0 ≤ g t := fun t => by
    simp only [g]; split_ifs
    · exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg t)
    · exact le_rfl
  have hgle : ∀ t, g t ≤ Λ t / t := fun t => by
    simp only [g]; split_ifs
    · exact le_rfl
    · exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg t)
  have hnp0 : 0 ≤ ∑ t ∈ Icc 1 n with ¬ t.Prime, g t := sum_nonneg fun t _ => hg0 t
  have hnp1 : ∑ t ∈ Icc 1 n with ¬ t.Prime, g t ≤
      2 * (Real.log 4 + 4) + (8 + RHTower.Mertens.mertensTail) :=
    (sum_le_sum fun t _ => hgle t).trans (sum_vonMangoldt_nonprime_le hn)
  have hcl : classMertensSum q r n = ∑ t ∈ Icc 1 n, g t := rfl
  have h := hC n hn
  rw [hcl, ← hsplit, hprime, div_eq_inv_mul] at h
  rw [abs_le] at h ⊢
  constructor <;> linarith [h.1, h.2]

/-- **The Wirsing bound for residue-class twins.** -/
theorem exists_abs_gaugeHarmonicSum_residueClassFlip_le {q : ℕ} [NeZero q] {r : ZMod q}
    (hr : IsUnit r)
    {b : ℝ} (hb1 : 1 ≤ b) (hb : |2 - 2 * (q.totient : ℝ)⁻¹| < b) :
    ∃ A, 0 ≤ A ∧ ∀ N, 3 ≤ N →
      |gaugeHarmonicSum (primeSetFlip (residueClassPrimes q r)) N| ≤ A * Real.log N ^ (b - 1) := by
  obtain ⟨C, hC⟩ := exists_abs_primeSetLogMass_residueClassPrimes_sub_le hr
  exact exists_abs_gaugeHarmonicSum_primeSetFlip_le _ hC hb1 hb

/-- **Residue-class twins of totient below `4` are separated by the atomic Hodge index.** -/
theorem hodgeSeparates_residueClassFlip {q : ℕ} [NeZero q] (hq : q.totient < 4) {r : ZMod q}
    (hr : IsUnit r) : HodgeSeparates (primeSetFlip (residueClassPrimes q r)) := by
  obtain ⟨C, hC⟩ := exists_abs_primeSetLogMass_residueClassPrimes_sub_le hr
  have hφ0 : 0 < q.totient := Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne q))
  have hφ : (q.totient : ℝ) ≤ 3 := by exact_mod_cast Nat.le_of_lt_succ hq
  have hφ1 : (1 : ℝ) ≤ q.totient := by exact_mod_cast hφ0
  refine hodgeSeparates_primeSetFlip_of_primeSetLogMass _ ?_ hC
  rw [lt_inv_comm₀ (by norm_num) (by linarith)]
  linarith

/-- **The twin flipping the primes `≡ 1 (mod 4)` is separated.** -/
theorem hodgeSeparates_primeSetFlip_one_mod_four :
    HodgeSeparates (primeSetFlip {p | p.Prime ∧ p % 4 = 1}) := by
  have hset : {p | p.Prime ∧ p % 4 = 1} = residueClassPrimes 4 1 := by
    ext p
    simp only [residueClassPrimes, Set.mem_setOf_eq]
    rw [show (1 : ZMod 4) = ((1 : ℕ) : ZMod 4) from Nat.cast_one.symm,
      ZMod.natCast_eq_natCast_iff']
  rw [hset]
  exact hodgeSeparates_residueClassFlip (by decide) isUnit_one

/-- **The twin flipping the primes `≡ 3 (mod 4)` is separated.** -/
theorem hodgeSeparates_primeSetFlip_three_mod_four :
    HodgeSeparates (primeSetFlip {p | p.Prime ∧ p % 4 = 3}) := by
  have hset : {p | p.Prime ∧ p % 4 = 3} = residueClassPrimes 4 3 := by
    ext p
    simp only [residueClassPrimes, Set.mem_setOf_eq]
    rw [show (3 : ZMod 4) = ((3 : ℕ) : ZMod 4) by norm_num, ZMod.natCast_eq_natCast_iff']
  rw [hset]
  exact hodgeSeparates_residueClassFlip (by decide) (IsUnit.of_mul_eq_one (3 : ZMod 4) (by decide))

end GaloisForLFunctions.RenormalizedIntersectionTheory
