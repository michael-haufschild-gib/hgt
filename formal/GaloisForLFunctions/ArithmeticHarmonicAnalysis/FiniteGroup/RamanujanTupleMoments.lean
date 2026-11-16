import GaloisForLFunctions.RHTower.Sieve.StadlmannReciprocalPhaseApplications

/-!
# Ramanujan moments and additive unit tuples

Expanding a product of reduced-residue character sums turns its Fourier
coefficient into an exact count of unit tuples with prescribed weighted sum.
This includes every raw moment, including odd moments and composite moduli.
-/

open Finset
open scoped BigOperators Classical

namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis
noncomputable section

private theorem character_sum {ι : Type*} (q : ℕ) [NeZero q]
    (s : Finset ι) (f : ι → ZMod q) :
    ZMod.stdAddChar (∑ i ∈ s, f i) = ∏ i ∈ s, ZMod.stdAddChar (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      rw [sum_insert hi, prod_insert hi, AddChar.map_add_eq_mul, ih]

/-- The exact number of unit tuples with a prescribed weighted additive sum. -/
def unitTupleCount (q : ℕ) [NeZero q] {ι : Type*} [Fintype ι]
    (r : ι → ZMod q) (t : ZMod q) : ℕ :=
  ((univ : Finset (ι → (ZMod q)ˣ)).filter
    (fun u => ∑ i, r i * (u i : ZMod q) = t)).card

/-- Every mixed Ramanujan Fourier coefficient counts a literal unit-tuple fiber. -/
theorem sum_ramanujan_product_character (q : ℕ) [NeZero q]
    {ι : Type*} [Fintype ι] (r : ι → ZMod q) (t : ZMod q) :
    (∑ g : ZMod q,
      (∏ i, _root_.RHTower.cglRamanujanAdditiveSum
        ⟨q, Nat.pos_of_ne_zero (NeZero.ne q)⟩ (g * r i)) *
        ZMod.stdAddChar (-(g * t))) =
      (q : ℂ) * unitTupleCount q r t := by
  classical
  have hsum (g : ZMod q) (i : ι) :
      _root_.RHTower.cglRamanujanAdditiveSum
        ⟨q, Nat.pos_of_ne_zero (NeZero.ne q)⟩ (g * r i) =
        ∑ u : (ZMod q)ˣ, ZMod.stdAddChar ((g * r i) * (u : ZMod q)) := by
    rw [← _root_.RHTower.Sieve.stadlmannReciprocalPhaseSum_eq_cglRamanujan,
      _root_.RHTower.Sieve.stadlmannReciprocalPhaseSum_eq_direct]
  simp_rw [hsum, Fintype.prod_sum, sum_mul]
  rw [sum_comm]
  have hterm (u : ι → (ZMod q)ˣ) (g : ZMod q) :
      (∏ i, ZMod.stdAddChar ((g * r i) * (u i : ZMod q))) *
        ZMod.stdAddChar (-(g * t)) =
        ZMod.stdAddChar (g * ((∑ i, r i * (u i : ZMod q)) - t)) := by
    rw [← character_sum, ← AddChar.map_add_eq_mul]
    congr 1
    simp only [mul_assoc, ← mul_sum]
    ring
  simp_rw [hterm, _root_.RHTower.Sieve.sum_stdAddChar_mul,
    sub_eq_zero]
  simp only [Nat.cast_ite, Nat.cast_zero]
  rw [unitTupleCount, ← sum_filter, sum_const, nsmul_eq_mul, mul_comm]

/-- Every raw moment is the modulus times the number of zero-sum unit tuples. -/
theorem sum_ramanujan_pow (q : ℕ) [NeZero q] (k : ℕ) :
    (∑ g : ZMod q, _root_.RHTower.cglRamanujanAdditiveSum
      ⟨q, Nat.pos_of_ne_zero (NeZero.ne q)⟩ g ^ k) =
      (q : ℂ) * unitTupleCount q (fun _ : Fin k => 1) 0 := by
  simpa only [mul_one, mul_zero, neg_zero, AddChar.map_zero_eq_one,
    prod_const, card_univ, Fintype.card_fin] using
    sum_ramanujan_product_character q (fun _ : Fin k => 1) 0

/-- Odd as well as even complete Ramanujan moments are nonnegative integers. -/
theorem ramanujan_moment_is_nat (q : ℕ) [NeZero q] (k : ℕ) :
    ∃ n : ℕ, (∑ g : ZMod q, _root_.RHTower.cglRamanujanAdditiveSum
      ⟨q, Nat.pos_of_ne_zero (NeZero.ne q)⟩ g ^ k) = (q * n : ℕ) := by
  exact ⟨unitTupleCount q (fun _ : Fin k => 1) 0,
    (sum_ramanujan_pow q k).trans (Nat.cast_mul _ _).symm⟩

/-- Reciprocal phases have the same exact moments at every composite modulus. -/
theorem sum_stadlmannReciprocalPhaseSum_pow (q : ℕ) [NeZero q] (k : ℕ) :
    (∑ g : ZMod q, _root_.RHTower.Sieve.stadlmannReciprocalPhaseSum q g ^ k) =
      (q : ℂ) * unitTupleCount q (fun _ : Fin k => 1) 0 := by
  simp_rw [_root_.RHTower.Sieve.stadlmannReciprocalPhaseSum_eq_cglRamanujan]
  exact sum_ramanujan_pow q k

/-- The zero-axis Kloosterman spectrum counts unit walks of every length. -/
theorem sum_kloostermanSum_zero_pow (q : ℕ) [NeZero q] (k : ℕ) :
    (∑ g : ZMod q, _root_.RHTower.Sieve.kloostermanSum q 0 g ^ k) =
      (q : ℂ) * unitTupleCount q (fun _ : Fin k => 1) 0 := by
  simp_rw [← _root_.RHTower.Sieve.stadlmannReciprocalPhaseSum_eq_kloosterman]
  exact sum_stadlmannReciprocalPhaseSum_pow q k

#print axioms sum_ramanujan_product_character
#print axioms sum_ramanujan_pow
#print axioms ramanujan_moment_is_nat
#print axioms sum_stadlmannReciprocalPhaseSum_pow
#print axioms sum_kloostermanSum_zero_pow

end
end GaloisForLFunctions.ArithmeticHarmonicAnalysis
