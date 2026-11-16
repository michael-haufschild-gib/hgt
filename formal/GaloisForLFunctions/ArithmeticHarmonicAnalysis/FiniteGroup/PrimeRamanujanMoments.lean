import GaloisForLFunctions.ArithmeticHarmonicAnalysis.FiniteGroup.RamanujanTupleMoments

/-!
# Exact prime Ramanujan moments

The prime spectrum has one value `p - 1` and `p - 1` copies of `-1`.
Its moments count closed unit walks, and its third moment is the exact
triangle count `p(p - 1)(p - 2)`, including the binary prime.
-/

open Finset
open scoped BigOperators

namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis
noncomputable section

/-- The prime reduced-residue spectrum, including characteristic two. -/
theorem prime_ramanujan_value (p : ℕ) [Fact p.Prime] (g : ZMod p) :
    _root_.RHTower.cglRamanujanAdditiveSum
      ⟨p, (Fact.out : p.Prime).pos⟩ g =
      if g = 0 then (p : ℂ) - 1 else -1 := by
  classical
  have hset : (univ : Finset (ZMod p)).filter IsUnit = univ.erase 0 := by
    ext x
    simp [isUnit_iff_ne_zero]
  rw [_root_.RHTower.cglRamanujanAdditiveSum, hset]
  have hsplit := sum_erase_add (s := (univ : Finset (ZMod p)))
    (f := fun u => ZMod.stdAddChar (u * g)) (mem_univ 0)
  rw [_root_.RHTower.Sieve.sum_stdAddChar_mul] at hsplit
  simp only [zero_mul, AddChar.map_zero_eq_one] at hsplit
  split_ifs at hsplit ⊢ <;> linear_combination hsplit

/-- Every prime moment has a closed formula, with no restriction on its degree. -/
theorem sum_prime_ramanujan_pow (p : ℕ) [Fact p.Prime] (k : ℕ) :
    (∑ g : ZMod p, _root_.RHTower.cglRamanujanAdditiveSum
      ⟨p, (Fact.out : p.Prime).pos⟩ g ^ k) =
      ((p : ℂ) - 1) ^ k + ((p : ℂ) - 1) * (-1) ^ k := by
  classical
  have hsplit := sum_erase_add (s := (univ : Finset (ZMod p)))
    (f := fun g => _root_.RHTower.cglRamanujanAdditiveSum
      ⟨p, (Fact.out : p.Prime).pos⟩ g ^ k) (mem_univ 0)
  have he : (∑ g ∈ (univ : Finset (ZMod p)).erase 0,
      _root_.RHTower.cglRamanujanAdditiveSum
        ⟨p, (Fact.out : p.Prime).pos⟩ g ^ k) =
        ((p : ℂ) - 1) * (-1) ^ k := by
    rw [sum_congr rfl (fun g hg => by
      rw [prime_ramanujan_value, if_neg (mem_erase.mp hg).1]),
      sum_const, nsmul_eq_mul, card_erase_of_mem (mem_univ 0),
      card_univ, ZMod.card, Nat.cast_sub (Fact.out : p.Prime).one_le, Nat.cast_one]
  rw [he, prime_ramanujan_value, if_pos rfl] at hsplit
  exact hsplit.symm.trans (add_comm _ _)

/-- Closed walks of every length have the exact prime spectral count. -/
theorem prime_unitTupleCount (p : ℕ) [Fact p.Prime] (k : ℕ) :
    (p : ℂ) * unitTupleCount p (fun _ : Fin k => 1) 0 =
      ((p : ℂ) - 1) ^ k + ((p : ℂ) - 1) * (-1) ^ k := by
  rw [← sum_ramanujan_pow]
  exact sum_prime_ramanujan_pow p k

/-- The cubic spectral moment counts oriented triangles of the unitary Cayley graph. -/
theorem sum_prime_ramanujan_cube (p : ℕ) [Fact p.Prime] :
    (∑ g : ZMod p, _root_.RHTower.cglRamanujanAdditiveSum
      ⟨p, (Fact.out : p.Prime).pos⟩ g ^ 3) =
      (p : ℂ) * (p - 1) * (p - 2) := by
  rw [sum_prime_ramanujan_pow]
  ring

/-- The quartic spectral moment gives the exact additive energy of prime units. -/
theorem sum_prime_ramanujan_four (p : ℕ) [Fact p.Prime] :
    (∑ g : ZMod p, _root_.RHTower.cglRamanujanAdditiveSum
      ⟨p, (Fact.out : p.Prime).pos⟩ g ^ 4) =
      (p : ℂ) * (p - 1) * (p ^ 2 - 3 * p + 3) := by
  rw [sum_prime_ramanujan_pow]
  ring

#print axioms prime_ramanujan_value
#print axioms sum_prime_ramanujan_pow
#print axioms prime_unitTupleCount
#print axioms sum_prime_ramanujan_cube
#print axioms sum_prime_ramanujan_four

end
end GaloisForLFunctions.ArithmeticHarmonicAnalysis
