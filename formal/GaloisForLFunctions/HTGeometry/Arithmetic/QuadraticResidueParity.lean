import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.Algebra.CharP.Two

/-!
# Additive parity of quadratic residue symbols

Encoding `1` by zero and `-1` by one turns multiplication of signs into
addition in `𝔽₂`. This transports quadratic reciprocity and products of
Legendre symbols into binary linear identities. Values outside the sign
group are irrelevant to these identities.
-/

namespace GaloisForLFunctions.HTGeometry.Arithmetic

/-- Additive encoding of an integer sign, with `1 ↦ 0` and `-1 ↦ 1`. -/
def signParity (a : ℤ) : ZMod 2 := if a = 1 then 0 else 1

@[simp] theorem signParity_one : signParity 1 = 0 := by simp [signParity]

@[simp] theorem signParity_neg_one : signParity (-1) = 1 := by simp [signParity]

/-- Multiplication of integer signs becomes addition of binary parities. -/
theorem signParity_mul {a b : ℤ} (ha : a = 1 ∨ a = -1) (hb : b = 1 ∨ b = -1) :
    signParity (a * b) = signParity a + signParity b := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
    simp [signParity, CharTwo.add_self_eq_zero]

private theorem neg_one_pow_is_sign (n : ℕ) :
    (-1 : ℤ) ^ n = 1 ∨ (-1 : ℤ) ^ n = -1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ]
    rcases ih with h | h
    · right
      rw [h, one_mul]
    · left
      rw [h, neg_one_mul, neg_neg]

/-- The parity of `(-1)^n` is the reduction of its exponent modulo two. -/
theorem signParity_neg_one_pow (n : ℕ) : signParity ((-1 : ℤ) ^ n) = (n : ZMod 2) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, signParity_mul (neg_one_pow_is_sign n) (Or.inr rfl), ih,
      signParity_neg_one, Nat.cast_succ]

private theorem mul_is_sign {a b : ℤ} (ha : a = 1 ∨ a = -1) (hb : b = 1 ∨ b = -1) :
    a * b = 1 ∨ a * b = -1 := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> simp

/-- Finite products of signs remain signs, and their parities add. -/
theorem signParity_prod {ι : Type*} (s : Finset ι) (a : ι → ℤ)
    (ha : ∀ i ∈ s, a i = 1 ∨ a i = -1) :
    signParity (∏ i ∈ s, a i) = ∑ i ∈ s, signParity (a i) := by
  classical
  have h : ((∏ i ∈ s, a i) = 1 ∨ (∏ i ∈ s, a i) = -1) ∧
      signParity (∏ i ∈ s, a i) = ∑ i ∈ s, signParity (a i) := by
    induction s using Finset.induction with
    | empty => simp
    | insert i s hi ih =>
      obtain ⟨hprod, hparity⟩ := ih (fun j hj => ha j (Finset.mem_insert_of_mem hj))
      have hiSign := ha i (Finset.mem_insert_self _ _)
      rw [Finset.prod_insert hi, Finset.sum_insert hi]
      exact ⟨mul_is_sign hiSign hprod, by rw [signParity_mul hiSign hprod, hparity]⟩
  exact h.2

/-- Additive Legendre symbol. Only nonzero residue classes are used in
the multiplicativity and reciprocity laws. -/
def quadraticResidueParity (p : ℕ) [Fact p.Prime] (a : ℤ) : ZMod 2 :=
  signParity (legendreSym p a)

/-- The parity of the symbol of `-1` records the half-prime exponent. -/
theorem quadraticResidueParity_neg_one {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) :
    quadraticResidueParity p (-1) = ((p / 2 : ℕ) : ZMod 2) := by
  rw [quadraticResidueParity, legendreSym.at_neg_one hp,
    ZMod.χ₄_eq_neg_one_pow ((Nat.Prime.mod_two_eq_one_iff_ne_two Fact.out).mpr hp),
    signParity_neg_one_pow]

/-- Products of prime Legendre symbols are the Jacobi symbol of the
product modulus. Repeated primes are allowed. -/
theorem legendreSym_prod_eq_jacobi {ι : Type*} (s : Finset ι) (p : ι → ℕ)
    [∀ i, Fact (p i).Prime] (a : ℤ) :
    (∏ i ∈ s, legendreSym (p i) a) = jacobiSym a (∏ i ∈ s, p i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert i s hi ih =>
    have hp : p i ≠ 0 := (Fact.out : (p i).Prime).ne_zero
    have hs : (∏ j ∈ s, p j) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr (fun j _ => (Fact.out : (p j).Prime).ne_zero)
    rw [Finset.prod_insert hi, Finset.prod_insert hi, jacobiSym.mul_right' a hp hs,
      jacobiSym.legendreSym.to_jacobiSym, ih]

/-- Additive residue-symbol sums are the parity of the product-modulus
Jacobi symbol. -/
theorem quadraticResidueParity_sum {ι : Type*} (s : Finset ι) (p : ι → ℕ)
    [∀ i, Fact (p i).Prime] (a : ℤ) (ha : ∀ i ∈ s, (a : ZMod (p i)) ≠ 0) :
    (∑ i ∈ s, quadraticResidueParity (p i) a) =
      signParity (jacobiSym a (∏ i ∈ s, p i)) := by
  rw [← legendreSym_prod_eq_jacobi s p a,
    signParity_prod s _ (fun i hi => legendreSym.eq_one_or_neg_one (p i) (ha i hi))]
  rfl

/-- The additive form of quadratic reciprocity for distinct odd primes. -/
theorem quadraticResidueParity_reciprocity {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (hp : p ≠ 2) (hq : q ≠ 2) (hpq : p ≠ q) :
    quadraticResidueParity q p + quadraticResidueParity p q =
      ((p / 2 : ℕ) : ZMod 2) * ((q / 2 : ℕ) : ZMod 2) := by
  have hp0 : ((p : ℤ) : ZMod q) ≠ 0 := by
    rw [Int.cast_natCast, Ne, ZMod.natCast_eq_zero_iff]
    exact fun h => hpq ((Nat.prime_dvd_prime_iff_eq (Fact.out : q.Prime)
      (Fact.out : p.Prime)).mp h).symm
  have hq0 : ((q : ℤ) : ZMod p) ≠ 0 := by
    rw [Int.cast_natCast, Ne, ZMod.natCast_eq_zero_iff]
    exact fun h => hpq ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime)
      (Fact.out : q.Prime)).mp h)
  have h := congrArg signParity (legendreSym.quadratic_reciprocity hp hq hpq)
  rw [signParity_mul (legendreSym.eq_one_or_neg_one q hp0)
    (legendreSym.eq_one_or_neg_one p hq0), signParity_neg_one_pow, Nat.cast_mul] at h
  exact h

/-- Reciprocity expressed using the two `-1` symbols. -/
theorem quadraticResidueParity_reciprocity_neg_one {p q : ℕ}
    [Fact p.Prime] [Fact q.Prime] (hp : p ≠ 2) (hq : q ≠ 2) (hpq : p ≠ q) :
    quadraticResidueParity q p + quadraticResidueParity p q =
      quadraticResidueParity p (-1) * quadraticResidueParity q (-1) := by
  rw [quadraticResidueParity_neg_one hp, quadraticResidueParity_neg_one hq]
  exact quadraticResidueParity_reciprocity hp hq hpq

#print axioms quadraticResidueParity_reciprocity
#print axioms quadraticResidueParity_sum

end GaloisForLFunctions.HTGeometry.Arithmetic
