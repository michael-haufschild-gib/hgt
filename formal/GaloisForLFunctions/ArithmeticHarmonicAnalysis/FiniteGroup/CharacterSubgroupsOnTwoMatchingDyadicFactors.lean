import GaloisForLFunctions.ArithmeticHarmonicAnalysis.FiniteGroup.SignsAndPrincipalUnitsAtTwo
import GaloisForLFunctions.ArithmeticHarmonicAnalysis.FiniteGroup.CyclicSubgroupsFromPowerFibres
import Mathlib.NumberTheory.MulChar.Duality
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-!
# Cyclic character subgroups with two equal dyadic factors

For q=2^s with q+1 prime and s positive, the factors from the two moduli
4q and q+1 have a common cyclic part of order q. Beyond order two, the
number of cyclic character subgroups at order 2^j is exactly 3·2^j up
to j=s. The modulus 1088 gives a counterexample to the substitution of
the printed ranks in Step 2 of Dahan's Lemma 6.5.
-/

noncomputable section
open Finset
open scoped Classical
namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis.DyadicExample
open DyadicUnits CyclicCensus

abbrev Q (r : ℕ) := 2^(r+1)
abbrev Modulus (r : ℕ) := 2^(r+1+2)*(Q r+1)
abbrev Characters (r : ℕ) := MulChar (ZMod (Modulus r)) ℂ
noncomputable local instance (r : ℕ) : Fintype (Characters r) := Fintype.ofFinite _

private def primeEquiv (r : ℕ) (hp : (Q r+1).Prime) :
    (ZMod (Q r+1))ˣ ≃* Cycle (Q r) := by
  letI := ZMod.isCyclic_units_prime hp
  apply mulEquivOfCyclicCardEq
  change Nat.card (ZMod (Q r+1))ˣ = Nat.card (ZMod (Q r))
  rw [Nat.card_eq_fintype_card,ZMod.card_units_eq_totient,Nat.totient_prime hp,Nat.card_zmod]
  omega

/-- CRT and finite duality give three cyclic factors of orders 2,q,q. -/
def characterFactors (r : ℕ) (hp : (Q r+1).Prime) :
    Characters r ≃* (Cycle 2 × Cycle (Q r)) × Cycle (Q r) := by
  have h : Nat.Coprime 2 (Q r+1) := by
    apply Nat.prime_two.coprime_iff_not_dvd.mpr
    unfold Q
    rw [pow_succ]
    omega
  let e := Units.mapEquiv (ZMod.chineseRemainder (h.pow_left (r+1+2))).toMulEquiv
  exact (MulChar.mulEquiv_units (ZMod (Modulus r)) ℂ).some.trans
    (e.trans (MulEquiv.prodUnits.trans (MulEquiv.prodCongr (decomposition (r+1)) (primeEquiv r hp))))

theorem character_torsion (r : ℕ) (hp : (Q r+1).Prime) (n : ℕ) :
    torsionCount (Characters r) n = Nat.gcd 2 n * (Nat.gcd (Q r) n)^2 := by
  rw [torsionCount_congr (characterFactors r hp),torsionCount_prod,torsionCount_prod,
    torsionCount_cycle,torsionCount_cycle]
  ring

private theorem within_depth (r j : ℕ) (hp : (Q r+1).Prime) (hj : j≤r) :
    torsionCount (Characters r) (2^(j+1)) = 2*(2^(j+1))^2 := by
  rw [character_torsion r hp,Nat.gcd_eq_left (dvd_pow_self 2 (Nat.succ_ne_zero _)),
    Nat.gcd_eq_right (pow_dvd_pow 2 (Nat.succ_le_succ hj))]

private theorem order_one (r : ℕ) :
    (ofOrder (Characters r) 1).card=1 := by
  have h := generators (Characters r) 1
  simpa [orderOf_eq_one_iff] using h.symm

/-- Three independent signs give exactly seven cyclic subgroups of order two. -/
theorem order_two (r : ℕ) (hp : (Q r+1).Prime) : (ofOrder (Characters r) 2).card=7 := by
  have h := prime_layer (Characters r) Nat.prime_two 0
  change torsionCount _ (2^(0+1))=torsionCount _ (2^0)+_ at h
  rw [within_depth r 0 hp (Nat.zero_le _),character_torsion r hp] at h
  norm_num [Nat.totient_prime Nat.prime_two] at h
  omega

/-- At each higher available depth, forty-eight at order sixteen is the
specialization of the exact law 3·2^j. -/
theorem higher_order (r j : ℕ) (hp : (Q r+1).Prime) (hj : j+1≤r) :
    (ofOrder (Characters r) (2^(j+2))).card = 3*2^(j+2) := by
  have h := prime_layer (Characters r) Nat.prime_two (j+1)
  change torsionCount _ (2^(j+2))=torsionCount _ (2^(j+1))+_ at h
  rw [within_depth r (j+1) hp hj,within_depth r j hp (by omega),
    Nat.totient_prime_pow_succ Nat.prime_two] at h
  simp only [Nat.reduceSub,mul_one] at h
  apply Nat.eq_of_mul_eq_mul_right (pow_pos (by norm_num : 0<2) (j+1))
  apply Nat.add_left_cancel (n := 2*(2^(j+1))^2)
  rw [← h,pow_succ 2 (j+1)]
  ring

private theorem kills_cycle (m : ℕ) [NeZero m] (x : Cycle m) : x^m=1 := by
  have h : Nat.card (Cycle m)=m := Nat.card_zmod _
  rw [← h,pow_card_eq_one']

private theorem exponent_kills (r : ℕ) (hp : (Q r+1).Prime) (x : Characters r) : x^(Q r)=1 := by
  let e := characterFactors r hp
  apply e.injective
  rw [map_pow,map_one]
  apply Prod.ext
  · apply Prod.ext
    · change (e x).1.1 ^ (2^(r+1))=1
      rw [pow_succ',pow_mul,kills_cycle,one_pow]
    · exact kills_cycle _ _
  · exact kills_cycle _ _

/-- Exact total obtained by summing the order strata of the character group. -/
theorem total (r : ℕ) (hp : (Q r+1).Prime) :
    (cyclicSubgroups (Characters r)).card + 4 = 6*Q r := by
  rw [total_over_exponent (Characters r) (Q r) (pow_pos (by norm_num) _) (exponent_kills r hp),
    Nat.sum_divisors_prime_pow Nat.prime_two]
  have partialSum (k : ℕ) (hk : k≤r) :
      (∑ i ∈ range (k+2), (ofOrder (Characters r) (2^i)).card)+4=6*2^(k+1) := by
    induction k with
    | zero =>
      simp only [sum_range_succ,sum_range_zero,zero_add,pow_zero,pow_one,order_one,order_two r hp]
      norm_num
    | succ k ih =>
      rw [sum_range_succ,higher_order r k hp hk]
      have he := ih (by omega)
      rw [pow_succ 2 (k+1)]
      omega
  exact partialSum r le_rfl

/-- For (u,a)=(16,17) the printed layer ranks give the bound forty.
Already the top-order stratum has forty-eight cyclic character subgroups. -/
theorem modulus_1088 :
    (ofOrder (Characters 3) 16).card=48 ∧ (cyclicSubgroups (Characters 3)).card=92 ∧
      40 < (ofOrder (Characters 3) 16).card := by
  have hp : (Q 3+1).Prime := by change Nat.Prime 17; norm_num
  have h := higher_order 3 2 hp (by norm_num)
  have hh := total 3 hp
  norm_num [Q] at h hh
  omega

end GaloisForLFunctions.ArithmeticHarmonicAnalysis.DyadicExample

#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.DyadicExample.character_torsion
#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.DyadicExample.order_two
#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.DyadicExample.higher_order
#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.DyadicExample.total
#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.DyadicExample.modulus_1088
#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.DyadicExample.characterFactors
