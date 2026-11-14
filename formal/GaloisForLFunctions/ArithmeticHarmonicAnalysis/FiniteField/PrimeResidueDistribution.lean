import GaloisForLFunctions.ArithmeticHarmonicAnalysis.FiniteField.PrimeResidueMoments
import GaloisForLFunctions.RHTower.Sieve.KloostermanSameModulusIntervalCompletion
import Mathlib.Data.ZMod.QuotientRing

/-!
# Complete-period distributions on prime residues

Chinese remaindering identifies a complete squarefree period with the product
of its prime-field coordinates. The resulting factorization works in every
commutative ring, in particular for complex characteristic-function tests.
-/

open Finset
open GaloisForLFunctions.BezoutValuationIncidence

namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis
noncomputable section

private instance primeFieldFact (p : Nat.Primes) : Fact p.val.Prime := ⟨p.property⟩

/-- Complete-period averages factor for arbitrary ring-valued local residue tests. -/
theorem sum_primeResidue_product {R : Type*} [CommRing R] (S : Finset Nat.Primes)
    (f : (p : Nat.Primes) → ZMod p.val → R) :
    ∑ n ∈ range (primeSetProduct S), ∏ p ∈ S, f p (n : ZMod p.val) =
      ∏ p ∈ S, ∑ a : ZMod p.val, f p a := by
  classical
  letI : NeZero (primeSetProduct S) := ⟨(primeSetProduct_pos S).ne'⟩
  letI (p : S) : NeZero p.val.val := ⟨p.val.property.ne_zero⟩
  have hcop : Pairwise (fun p q : S => Nat.Coprime p.val.val q.val.val) := by
    intro p q hpq
    apply (Nat.coprime_primes p.val.property q.val.property).mpr
    exact fun h => hpq (Subtype.ext (Subtype.ext h))
  have hP : primeSetProduct S = ∏ p : S, p.val.val := by
    simp only [primeSetProduct, Finset.prod_coe_sort]
  have e : ZMod (primeSetProduct S) ≃+* ((p : S) → ZMod p.val.val) :=
    (ZMod.ringEquivCongr hP).trans (ZMod.prodEquivPi (fun p : S => p.val.val) hcop)
  have he (n : ℕ) (p : S) : e (n : ZMod (primeSetProduct S)) p =
      (n : ZMod p.val.val) := by
    rw [map_natCast]
    rfl
  calc
    _ = ∑ n ∈ range (primeSetProduct S),
        ∏ p : S, f p.val (e (n : ZMod (primeSetProduct S)) p) := by
      apply sum_congr rfl
      intro n _
      simp only [he]
      exact (Finset.prod_coe_sort S (fun p : Nat.Primes => f p (n : ZMod p.val))).symm
    _ = ∑ a : ZMod (primeSetProduct S), ∏ p : S, f p.val (e a p) :=
      (RHTower.Sieve.sum_zmod_eq_sum_range_natCast (primeSetProduct S)
        (fun a : ZMod (primeSetProduct S) => ∏ p : S, f p.val (e a p))).symm
    _ = ∑ x : ((p : S) → ZMod p.val.val), ∏ p : S, f p.val (x p) :=
      e.toEquiv.sum_comp (fun x : ((p : S) → ZMod p.val.val) => ∏ p : S, f p.val (x p))
    _ = ∏ p : S, ∑ a : ZMod p.val.val, f p.val a :=
      (Fintype.prod_sum (fun (p : S) (a : ZMod p.val.val) => f p.val a)).symm
    _ = _ := Finset.prod_coe_sort S (fun p : Nat.Primes => ∑ a : ZMod p.val, f p a)

#print axioms sum_primeResidue_product

end
end GaloisForLFunctions.ArithmeticHarmonicAnalysis
