import GaloisForLFunctions.BezoutValuationIncidence.Divisors.CompositeWitnessParametrization
import Mathlib.Tactic.LinearCombination

/-!
# Divisor fibers for three unit fractions

Trybushnyi's Lemma 2.1 (arXiv:2611.14167) reconstructs three denominators
from a linear divisibility event. Dahan's Theorem 2.1 (arXiv:2611.08717)
factors the same equation in two different ways when the numerator is four.
Both factorizations work for an arbitrary positive numerator. The witnesses
below keep their actual denominators, so rescaling and comparing fibers
do not require primality or ordering conventions.
-/

namespace GaloisForLFunctions.BezoutValuationIncidence.UnitFractions

/-- Equality of a positive rational with the sum of three specified unit fractions. -/
def Represents (K n x y z : ℕ+) : Prop :=
  (K : ℚ) / (n : ℕ) = 1 / (x : ℚ) + 1 / (y : ℚ) + 1 / (z : ℚ)

private theorem cast_ne (m : ℕ+) : (m : ℚ) ≠ 0 := by
  exact_mod_cast m.pos.ne'

/-- Clearing the denominators detects representations over the naturals exactly. -/
theorem represents_iff (K n x y z : ℕ+) :
    Represents K n x y z ↔
      (K : ℕ) * x * y * z = (n : ℕ) * (x * y + x * z + y * z : ℕ) := by
  unfold Represents
  field_simp [cast_ne]
  constructor <;> intro h
  · exact_mod_cast (by linear_combination h :
      (K : ℚ) * x * y * z = (n : ℚ) * ((x : ℚ)*y + (x : ℚ)*z + (y : ℚ)*z))
  · have h' : (K : ℚ) * x * y * z = (n : ℚ) * ((x : ℚ)*y + (x : ℚ)*z + (y : ℚ)*z) := by
      exact_mod_cast h
    linear_combination h'

/-- Scaling every denominator both preserves and reflects a representation. -/
theorem scale_iff (K n x y z s : ℕ+) :
    Represents K (s*n) (s*x) (s*y) (s*z) ↔ Represents K n x y z := by
  unfold Represents
  simp only [PNat.mul_coe, Nat.cast_mul]
  field_simp [cast_ne]

/-- Any exception forces exceptions at every divisor of its denominator. -/
theorem exceptions_descend (K m s : ℕ+) :
    (¬ ∃ x y z, Represents K (s*m) x y z) →
      ¬ ∃ x y z, Represents K m x y z := by
  rintro he ⟨x, y, z, h⟩
  exact he ⟨s*x, s*y, s*z, (scale_iff K m x y z s).2 h⟩

/-- The equation common to the linear congruence and the two quadratic factorizations. -/
def TypeII (K n a b c d : ℕ+) : Prop :=
  (K : ℕ) * a * b * c * d = (a : ℕ) + b + c * n

/-- For these three structured denominators the witness equation is necessary and sufficient. -/
theorem structured_iff (K n a b c d : ℕ+) :
    Represents K n (a*b*d) (a*c*d*n) (b*c*d*n) ↔ TypeII K n a b c d := by
  unfold Represents TypeII
  simp only [PNat.mul_coe, Nat.cast_mul]
  have hal := cast_ne a
  have hbl := cast_ne b
  have hcl := cast_ne c
  have hdl := cast_ne d
  have hnl := cast_ne n
  field_simp
  constructor <;> intro h
  · exact_mod_cast (by linear_combination h :
      (K : ℚ)*a*b*c*d = (a : ℚ)+b+(c : ℚ)*n)
  · have hr : (K : ℚ)*a*b*c*d = (a : ℚ)+b+(c : ℚ)*n := by exact_mod_cast h
    linear_combination hr

/-- The linear event recovers the unique missing denominator parameter. -/
theorem event_iff_existsUnique (K n a c d : ℕ+) :
    ((K : ℕ)*a*c*d - 1) ∣ (n : ℕ)*c+a ↔ ∃! b : ℕ+, TypeII K n a b c d := by
  have hpos : 0 < (K : ℕ)*a*c*d := by positivity
  have hu : (K : ℕ)*a*c*d - 1 + 1 = (K : ℕ)*a*c*d := by omega
  have equiv (b : ℕ+) : TypeII K n a b c d ↔
      (n : ℕ)*c+a = ((K : ℕ)*a*c*d - 1)*b := by
    unfold TypeII
    have he := congrArg (fun k : ℕ => k*(b : ℕ)) hu
    constructor <;> intro h <;> nlinarith only [he,h]
  constructor
  · rintro ⟨b,hb⟩
    have hsum : 0 < (n : ℕ)*c+a := by positivity
    have hbpos : 0 < b := by
      by_contra! h
      simp [Nat.eq_zero_of_le_zero h] at hb
    have hum : 0 < (K : ℕ)*a*c*d - 1 := by
      by_contra! h
      simp [Nat.eq_zero_of_le_zero h] at hb
    refine ⟨⟨b,hbpos⟩, (equiv _).2 hb, ?_⟩
    intro e he
    exact Subtype.ext (Nat.eq_of_mul_eq_mul_left hum (((equiv e).1 he).symm.trans hb))
  · rintro ⟨b,hb,_⟩
    exact ⟨b, (equiv b).1 hb⟩

/-- Dahan's symmetric factorization detects the same witnesses for every numerator. -/
theorem symmetric_factors_iff (K n a b c d : ℕ+) :
    (((K : ℤ)*c*d*a - 1) * ((K : ℤ)*c*d*b - 1) =
      (K : ℤ)*c^2*d*n + 1) ↔ TypeII K n a b c d := by
  have hnz : (K : ℤ)*c*d ≠ 0 := by positivity
  have hid : ((K : ℤ)*c*d*a-1)*((K : ℤ)*c*d*b-1)-((K : ℤ)*c^2*d*n+1) =
      ((K : ℤ)*c*d)*((K : ℤ)*a*b*c*d - (a+b+c*n)) := by ring
  rw [← sub_eq_zero, hid, mul_eq_zero, or_iff_right hnz, sub_eq_zero]
  unfold TypeII
  exact_mod_cast Iff.rfl

/-- Fixing one divisor instead of the modulator produces the complementary factorization. -/
theorem complementary_factors_iff (K n a b c d : ℕ+) :
    (((K : ℤ)*a*c*d - 1) * ((K : ℤ)*a*b*d - n) =
      (n : ℤ) + K*d*a^2) ↔ TypeII K n a b c d := by
  have hnz : (K : ℤ)*a*d ≠ 0 := by positivity
  have hid : ((K : ℤ)*a*c*d-1)*((K : ℤ)*a*b*d-n)-((n : ℤ)+K*d*a^2) =
      ((K : ℤ)*a*d)*((K : ℤ)*a*b*c*d - (a+b+c*n)) := by ring
  rw [← sub_eq_zero, hid, mul_eq_zero, or_iff_right hnz, sub_eq_zero]
  unfold TypeII
  exact_mod_cast Iff.rfl

/-- The corpus's composite modulus is the linear-event modulus for numerator four.
An event identifies a unique complementary parameter in either quadratic factorization. -/
theorem composite_fiber (c u a v n : ℕ+) :
    compositeWitnessModulus c u a v ∣ (a : ℕ)*n+u ↔
      ∃! b : ℕ+, Represents 4 n (u*b*(c*v)) (u*a*(c*v)*n) (b*a*(c*v)*n) := by
  simp_rw [structured_iff]
  rw [← event_iff_existsUnique]
  unfold compositeWitnessModulus
  simp only [PNat.mul_coe]
  change 4 * (c : ℕ)*u*a*v - 1 ∣ (a : ℕ)*n+u ↔
    4*(u : ℕ)*a*(c*v : ℕ)-1 ∣ (n : ℕ)*a+u
  ring_nf

end GaloisForLFunctions.BezoutValuationIncidence.UnitFractions

#print axioms GaloisForLFunctions.BezoutValuationIncidence.UnitFractions.represents_iff
#print axioms GaloisForLFunctions.BezoutValuationIncidence.UnitFractions.scale_iff
#print axioms GaloisForLFunctions.BezoutValuationIncidence.UnitFractions.exceptions_descend
#print axioms GaloisForLFunctions.BezoutValuationIncidence.UnitFractions.structured_iff
#print axioms GaloisForLFunctions.BezoutValuationIncidence.UnitFractions.event_iff_existsUnique
#print axioms GaloisForLFunctions.BezoutValuationIncidence.UnitFractions.symmetric_factors_iff
#print axioms GaloisForLFunctions.BezoutValuationIncidence.UnitFractions.complementary_factors_iff
#print axioms GaloisForLFunctions.BezoutValuationIncidence.UnitFractions.composite_fiber
