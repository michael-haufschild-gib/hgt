import GaloisForLFunctions.ArithmeticHarmonicAnalysis.FiniteField.ChebyshevCharacteristicReduction
import GaloisForLFunctions.HTGeometry.Polynomial.DicksonCoefficients
import Mathlib.FieldTheory.Finite.Basic

/-!
# Deck translations and reflection on Chebyshev Artin–Schreier curves

The affine points of `y^p - y = D_m(x)` admit the translations `y ↦ y+b`
for `b ∈ 𝔽_p` and the reflection `(x,y) ↦ (-x,(-1)^m y)`.
Reflection centralizes translations in even degree and inverts them in odd
degree, the parity mechanism in §7 of Kazemifard–Tafazolian,
*Automorphisms of Kummer and Artin–Schreier curves defined by Chebyshev
polynomials*. Frobenius degree reduction intertwines these deck translations.
Reduction also intertwines reflection, so it preserves the action generated
by both kinds of symmetry. These are explicit actions on affine points; no assertion of completeness
of the automorphism group is needed.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis
open Polynomial
variable {A : Type*} [CommRing A] (p : ℕ) [Fact p.Prime] [CharP A p]

private theorem primeScalar_pow (b : ZMod p) :
    (ZMod.castHom (dvd_refl p) A b) ^ p = ZMod.castHom (dvd_refl p) A b := by
  rw [← map_pow, ZMod.pow_card]

/-- Prime-field translation preserves the equation and has inverse translation by `-b`. -/
def chebyshevArtinSchreierDeck (m : ℕ) (b : ZMod p) :
    Equiv.Perm (chebyshevArtinSchreierPoints (A := A) p m) where
  toFun xy := ⟨(xy.1.1, xy.1.2 + ZMod.castHom (dvd_refl p) A b), by
    change (_ + _) ^ p - (_ + _) = _
    rw [add_pow_char, primeScalar_pow]
    linear_combination xy.2⟩
  invFun xy := ⟨(xy.1.1, xy.1.2 - ZMod.castHom (dvd_refl p) A b), by
    change (_ - _) ^ p - (_ - _) = _
    rw [sub_pow_char, primeScalar_pow]
    linear_combination xy.2⟩
  left_inv xy := Subtype.ext (Prod.ext rfl (add_sub_cancel_right _ _))
  right_inv xy := Subtype.ext (Prod.ext rfl (sub_add_cancel _ _))

private theorem parityScalar_sq (m : ℕ) : ((-1 : A) ^ m) ^ 2 = 1 := by
  rw [← pow_mul, Nat.mul_comm m 2, pow_mul, neg_one_sq, one_pow]

private theorem parityScalar_pow (m : ℕ) : ((-1 : A) ^ m) ^ p = (-1 : A) ^ m := by
  change frobenius A p ((-1 : A) ^ m) = _
  rw [map_pow, map_neg, map_one]

/-- Chebyshev parity lifts reflection of the base to an involution of the affine curve. -/
def chebyshevArtinSchreierReflection (m : ℕ) :
    Equiv.Perm (chebyshevArtinSchreierPoints (A := A) p m) :=
  have hpres : ∀ xy : chebyshevArtinSchreierPoints (A := A) p m,
      ((-1 : A) ^ m * xy.1.2) ^ p - (-1 : A) ^ m * xy.1.2 =
        (dickson 1 (1 : A) m).eval (-xy.1.1) := by
    intro xy
    have hpoly := congrArg (eval xy.1.1) (HTGeometry.dickson_comp_neg_X (R := A) m)
    simp only [eval_comp, eval_neg, eval_X, eval_mul, eval_C] at hpoly
    rw [mul_pow, parityScalar_pow, ← mul_sub, xy.2, hpoly]
  { toFun := fun xy => ⟨(-xy.1.1, (-1 : A) ^ m * xy.1.2), hpres xy⟩
    invFun := fun xy => ⟨(-xy.1.1, (-1 : A) ^ m * xy.1.2), hpres xy⟩
    left_inv := fun xy => by
      apply Subtype.ext
      apply Prod.ext
      · exact neg_neg _
      · change (-1 : A) ^ m * ((-1 : A) ^ m * xy.1.2) = xy.1.2
        rw [← mul_assoc, ← pow_two, parityScalar_sq, one_mul]
    right_inv := fun xy => by
      apply Subtype.ext
      apply Prod.ext
      · exact neg_neg _
      · change (-1 : A) ^ m * ((-1 : A) ^ m * xy.1.2) = xy.1.2
        rw [← mul_assoc, ← pow_two, parityScalar_sq, one_mul] }

/-- Reflection conjugates a translation by the degree-parity sign. -/
theorem chebyshevArtinSchreierReflection_deck (m : ℕ) (b : ZMod p)
    (xy : chebyshevArtinSchreierPoints (A := A) p m) :
    chebyshevArtinSchreierReflection p m (chebyshevArtinSchreierDeck p m b xy) =
      chebyshevArtinSchreierDeck p m ((-1 : ZMod p) ^ m * b)
        (chebyshevArtinSchreierReflection p m xy) := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · change (-1 : A) ^ m * (xy.1.2 + _) = (-1 : A) ^ m * xy.1.2 + _
    rw [map_mul, map_pow, map_neg, map_one, mul_add]

/-- Removing characteristic powers preserves the full prime-field translation action. -/
theorem chebyshevArtinSchreierReduction_deck (s m : ℕ) (b : ZMod p)
    (xy : chebyshevArtinSchreierPoints (A := A) p (p ^ s * m)) :
    chebyshevArtinSchreierReduction p s m
        (chebyshevArtinSchreierDeck p (p ^ s * m) b xy) =
      chebyshevArtinSchreierDeck p m b (chebyshevArtinSchreierReduction p s m xy) := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · change xy.1.2 + ZMod.castHom (dvd_refl p) A b -
        frobeniusTraceSum p 1 s ((dickson 1 (1 : A) m).eval xy.1.1) =
      xy.1.2 - frobeniusTraceSum p 1 s ((dickson 1 (1 : A) m).eval xy.1.1) +
        ZMod.castHom (dvd_refl p) A b
    ring

/-- Even degree gives commuting reflection and deck translation. -/
theorem chebyshevArtinSchreierReflection_deck_even (k : ℕ) (b : ZMod p)
    (xy : chebyshevArtinSchreierPoints (A := A) p (2 * k)) :
    chebyshevArtinSchreierReflection p (2 * k) (chebyshevArtinSchreierDeck p (2 * k) b xy) =
      chebyshevArtinSchreierDeck p (2 * k) b
        (chebyshevArtinSchreierReflection p (2 * k) xy) := by
  simpa only [pow_mul, neg_one_sq, one_pow, one_mul] using
    chebyshevArtinSchreierReflection_deck p (2 * k) b xy

/-- Odd degree gives the dihedral inversion relation. -/
theorem chebyshevArtinSchreierReflection_deck_odd (k : ℕ) (b : ZMod p)
    (xy : chebyshevArtinSchreierPoints (A := A) p (2 * k + 1)) :
    chebyshevArtinSchreierReflection p (2 * k + 1)
        (chebyshevArtinSchreierDeck p (2 * k + 1) b xy) =
      chebyshevArtinSchreierDeck p (2 * k + 1) (-b)
        (chebyshevArtinSchreierReflection p (2 * k + 1) xy) := by
  simpa only [pow_add, pow_mul, neg_one_sq, one_pow, pow_one, one_mul,
    neg_one_mul] using chebyshevArtinSchreierReflection_deck p (2 * k + 1) b xy

private theorem parityScalar_primePower (s m : ℕ) :
    ((-1 : A) ^ m) ^ (p ^ s) = (-1 : A) ^ m := by
  change iterateFrobenius A p s ((-1 : A) ^ m) = _
  rw [map_pow, map_neg, map_one]

private theorem trace_parityScalar_mul (s m : ℕ) (f : A) :
    frobeniusTraceSum p 1 s ((-1 : A) ^ m * f) =
      (-1 : A) ^ m * frobeniusTraceSum p 1 s f := by
  simp only [frobeniusTraceSum, mul_pow, parityScalar_primePower, Finset.mul_sum]

/-- Characteristic reduction also intertwines reflection, including in characteristic two. -/
theorem chebyshevArtinSchreierReduction_reflection (s m : ℕ)
    (xy : chebyshevArtinSchreierPoints (A := A) p (p ^ s * m)) :
    chebyshevArtinSchreierReduction p s m
        (chebyshevArtinSchreierReflection p (p ^ s * m) xy) =
      chebyshevArtinSchreierReflection p m (chebyshevArtinSchreierReduction p s m xy) := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · change (-1 : A) ^ (p ^ s * m) * xy.1.2 -
        frobeniusTraceSum p 1 s ((dickson 1 (1 : A) m).eval (-xy.1.1)) =
      (-1 : A) ^ m *
        (xy.1.2 - frobeniusTraceSum p 1 s ((dickson 1 (1 : A) m).eval xy.1.1))
    have hpoly := congrArg (eval xy.1.1) (HTGeometry.dickson_comp_neg_X (R := A) m)
    simp only [eval_comp, eval_neg, eval_X, eval_mul, eval_C] at hpoly
    have hparity : (-1 : A) ^ (p ^ s * m) = (-1 : A) ^ m := by
      rw [Nat.mul_comm (p ^ s) m, pow_mul, parityScalar_primePower]
    rw [hparity, hpoly, trace_parityScalar_mul, mul_sub]

end GaloisForLFunctions.ArithmeticHarmonicAnalysis


#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.chebyshevArtinSchreierReflection_deck_even
#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.chebyshevArtinSchreierReflection_deck_odd
#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.chebyshevArtinSchreierReduction_deck
#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.chebyshevArtinSchreierReduction_reflection
