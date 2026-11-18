import GaloisForLFunctions.BezoutValuationIncidence.Divisors.UnitFractionWitnessFibers
import Mathlib.NumberTheory.Divisors
import Mathlib.SetTheory.Cardinal.Finite

/-!
# Counting the symmetric unit-fraction parameters

Dahan's quadratic factorization (arXiv:2611.08717, Theorem 2.1) gives more
than a divisibility test for one known shape. For fixed K,n,c,d, all ordered
pairs (a,b) are in bijection with divisors of Kc²dn+1 congruent to -1 modulo
Kcd. Exchanging a and b corresponds to complementary divisors.
-/

namespace GaloisForLFunctions.BezoutValuationIncidence.UnitFractions.Shapes
open Finset

private def index (R a : ℕ+) := (R : ℕ)*a-1
private theorem index_succ (R a : ℕ+) : index R a+1 = (R : ℕ)*a :=
  Nat.sub_add_cancel (Nat.mul_pos R.pos a.pos)

private def decode (R : ℕ+) (x : ℕ) (h : (R : ℕ) ∣ x+1) : ℕ+ :=
  ⟨(x+1)/R,Nat.div_pos (Nat.le_of_dvd (Nat.succ_pos _) h) R.pos⟩

private theorem index_decode (R : ℕ+) (x : ℕ) (h : (R : ℕ) ∣ x+1) :
    index R (decode R x h) = x := by
  have he := index_succ R (decode R x h)
  change _ = (R : ℕ)*((x+1)/R) at he
  rw [Nat.mul_div_cancel' h] at he
  omega

private theorem decode_index (R a : ℕ+) (h : (R : ℕ) ∣ index R a+1) :
    decode R (index R a) h=a := by
  apply PNat.eq
  change (index R a+1)/R = _
  rw [index_succ,Nat.mul_div_cancel_left _ R.pos]

/-- Integer whose divisors parametrize the shape fiber. -/
def target (R c n : ℕ+) : ℕ := (R : ℕ)*c*n+1

/-- The residue filter needs to be imposed on only one of the two divisors. -/
theorem complement_class (R c n : ℕ+) (x y : ℕ) (hxy : x*y=target R c n) :
    (R : ℕ) ∣ x+1 ↔ (R : ℕ) ∣ y+1 := by
  have H (i j : ℕ) (hij : i*j=target R c n) (h : (R : ℕ) ∣ i+1) : (R : ℕ) ∣ j+1 := by
    have h₁ := dvd_mul_of_dvd_left h j
    have h₂ : (R : ℕ) ∣ (R : ℕ)*c*n := ⟨(c : ℕ)*n,by ring⟩
    have hh := Nat.dvd_sub h₁ h₂
    rw [add_mul,one_mul,hij] at hh
    unfold target at hh
    simpa only [Nat.add_assoc,Nat.add_sub_cancel_left,Nat.add_comm 1 j] using hh
  exact ⟨H x y hxy,H y x ((Nat.mul_comm y x).trans hxy)⟩

/-- Actual polynomial equation over positive denominators equals an exact product over naturals. -/
theorem product_iff (K n a b c d : ℕ+) :
    index (K*c*d) a * index (K*c*d) b = target (K*c*d) c n ↔ TypeII K n a b c d := by
  rw [← symmetric_factors_iff]
  have he (x : ℕ+) : (index (K*c*d) x : ℤ) = (K : ℤ)*c*d*x-1 := by
    have hh := congrArg (fun t : ℕ => (t : ℤ)) (index_succ (K*c*d) x)
    push_cast at hh
    linarith only [hh]
  have ht : (target (K*c*d) c n : ℤ) = (K : ℤ)*c^2*d*n+1 := by
    simp only [target,Nat.cast_add,Nat.cast_mul,Nat.cast_one,PNat.mul_coe]
    ring
  rw [← he a,← he b,← ht,← Int.natCast_mul,Int.natCast_inj]

/-- Congruent positive divisors, with their ordinary positive complementary divisors. -/
def divisors (R c n : ℕ+) : Finset ℕ :=
  (target R c n).divisors.filter (fun x => (R : ℕ) ∣ x+1)

private theorem pair_spec (R c n : ℕ+) {x : ℕ} (hx : x ∈ divisors R c n) :
    x*(target R c n / x)=target R c n ∧ (R : ℕ) ∣ x+1 ∧
      (R : ℕ) ∣ target R c n / x+1 := by
  obtain ⟨hd,hm⟩ := mem_filter.mp hx
  have h := Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hd)
  exact ⟨h,hm,(complement_class _ _ _ _ _ h).1 hm⟩

/-- A bijection preserving the actual two positive shape parameters. -/
def divisorEquiv (K n c d : ℕ+) :
    {ab : ℕ+ × ℕ+ // TypeII K n ab.1 ab.2 c d} ≃ ↥(divisors (K*c*d) c n) where
  toFun ab := by
    have h := (product_iff _ _ _ _ _ _).2 ab.property
    exact ⟨_,mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨⟨_,h.symm⟩,Nat.succ_ne_zero _⟩,
      by rw [index_succ]; exact dvd_mul_right _ _⟩⟩
  invFun x := by
    have h := pair_spec _ _ _ x.property
    exact ⟨(decode _ _ h.2.1,decode _ _ h.2.2),(product_iff _ _ _ _ _ _).1
      (by rw [index_decode,index_decode]; exact h.1)⟩
  left_inv ab := by
    apply Subtype.ext
    have h := (product_iff _ _ _ _ _ _).2 ab.property
    have hx : 0 < index (K*c*d) ab.val.1 := Nat.pos_of_dvd_of_pos ⟨_,h.symm⟩ (Nat.succ_pos _)
    have he : target (K*c*d) c n / index (K*c*d) ab.val.1 = index (K*c*d) ab.val.2 := by
      rw [← h,Nat.mul_div_cancel_left _ hx]
    apply Prod.ext
    · exact decode_index _ _ (by rw [index_succ]; exact dvd_mul_right _ _)
    · apply PNat.eq
      change (target (K*c*d) c n / index (K*c*d) ab.val.1 + 1) / ((K*c*d : ℕ+) : ℕ) = _
      rw [he,index_succ,Nat.mul_div_cancel_left _ (K*c*d).pos]
  right_inv x := Subtype.ext (index_decode _ _ (pair_spec _ _ _ x.property).2.1)

/-- The cardinality counts exactly the ordered shapes yielding the three
displayed unit fractions; repeated denominator values are allowed. -/
theorem count_representations (K n c d : ℕ+) :
    Nat.card {ab : ℕ+ × ℕ+ // Represents K n (ab.1*ab.2*d) (ab.1*c*d*n) (ab.2*c*d*n)} =
      (divisors (K*c*d) c n).card := by
  simp_rw [structured_iff]
  simpa using Nat.card_congr (divisorEquiv K n c d)

/-- A symmetric shape occurs precisely at a congruent square root of the divisor target. -/
theorem diagonal_iff (K n c d : ℕ+) :
    (∃ a, TypeII K n a a c d) ↔
      ∃ x : ℕ, x^2=target (K*c*d) c n ∧ ((K*c*d : ℕ+) : ℕ) ∣ x+1 := by
  constructor
  · rintro ⟨a,ha⟩
    refine ⟨index (K*c*d) a,by simpa only [pow_two] using (product_iff _ _ _ _ _ _).2 ha,?_⟩
    rw [index_succ]
    exact dvd_mul_right _ _
  · rintro ⟨x,hx,hr⟩
    refine ⟨decode _ _ hr,(product_iff _ _ _ _ _ _).1 ?_⟩
    simpa only [index_decode,← pow_two] using hx

end GaloisForLFunctions.BezoutValuationIncidence.UnitFractions.Shapes

#print axioms GaloisForLFunctions.BezoutValuationIncidence.UnitFractions.Shapes.complement_class
#print axioms GaloisForLFunctions.BezoutValuationIncidence.UnitFractions.Shapes.product_iff
#print axioms GaloisForLFunctions.BezoutValuationIncidence.UnitFractions.Shapes.divisorEquiv
#print axioms GaloisForLFunctions.BezoutValuationIncidence.UnitFractions.Shapes.count_representations
#print axioms GaloisForLFunctions.BezoutValuationIncidence.UnitFractions.Shapes.diagonal_iff
