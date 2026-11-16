import GaloisForLFunctions.HTGeometry.DifferentialIndependence

/-!
# Quadratic primitives of odd differential products

The quadratic primitive in §2 of Yang–Zhao–Yang–Liao,
*On the periodicity of meromorphic functions of the form ff⁽ᵏ⁾*
(arXiv:2611.18185), is expressed recursively by integration by parts.
Doubling it removes division by two, so the identity holds over every
commutative differential ring, including positive characteristic.
-/

namespace GaloisForLFunctions.RepresentationLifting

open scoped Differential

variable {A : Type*} [CommRing A] [Differential A]

/-- Twice the quadratic primitive of `u * u⁽²ⁿ⁺¹⁾`; the recursion cancels interior jets. -/
def doubledOddPrimitive : ℕ → A → A
  | 0, u => u * u
  | n + 1, u => 2 * u * differentialJet (2 * n + 2) u - doubledOddPrimitive n u′

/-- Every odd self-product is a total derivative after multiplication by two. -/
theorem deriv_doubledOddPrimitive (n : ℕ) (u : A) :
    (doubledOddPrimitive n u)′ = 2 * u * differentialJet (2 * n + 1) u := by
  induction n generalizing u with
  | zero =>
      simp only [doubledOddPrimitive, Nat.mul_zero, Nat.zero_add,
        differentialJet_succ, differentialJet_zero, Derivation.leibniz, smul_eq_mul]
      ring
  | succ n ih =>
      rw [doubledOddPrimitive, map_sub, ih]
      have hjet : differentialJet (2 * n + 1) u′ = differentialJet (2 * n + 2) u := by
        rw [show 2 * n + 2 = (2 * n + 1) + 1 by omega, differentialJet_add]
        rfl
      rw [hjet]
      have htwo : (2 : A)′ = 0 := Derivation.map_natCast Differential.deriv 2
      simp only [Derivation.leibniz, smul_eq_mul, htwo, mul_zero, add_zero]
      rw [← differentialJet_succ]
      rw [show 2 * (n + 1) + 1 = (2 * n + 2) + 1 by omega]
      ring

/-- Global sign cannot be recovered from any of these quadratic primitives. -/
theorem doubledOddPrimitive_neg (n : ℕ) (u : A) :
    doubledOddPrimitive n (-u) = doubledOddPrimitive n u := by
  have hjet (m : ℕ) (a : A) : differentialJet m (-a) = -differentialJet m a := by
    induction m with
    | zero => rfl
    | succ m ih => rw [differentialJet_succ, differentialJet_succ, ih, map_neg]
  induction n generalizing u with
  | zero => simp only [doubledOddPrimitive, neg_mul_neg]
  | succ n ih =>
      rw [doubledOddPrimitive, doubledOddPrimitive, hjet, map_neg, ih]
      ring

/-- Differential ring homomorphisms transport the primitive at every order. -/
theorem map_doubledOddPrimitive {B : Type*} [CommRing B] [Differential B]
    (f : A →+* B) (hf : ∀ a, f a′ = (f a)′) (n : ℕ) (u : A) :
    f (doubledOddPrimitive n u) = doubledOddPrimitive n (f u) := by
  have hjet (m : ℕ) (a : A) : f (differentialJet m a) = differentialJet m (f a) := by
    induction m with
    | zero => rfl
    | succ m ih => rw [differentialJet_succ, differentialJet_succ, hf, ih]
  induction n generalizing u with
  | zero => exact map_mul f u u
  | succ n ih =>
      simp only [doubledOddPrimitive, map_sub, map_mul, map_ofNat, hjet, ih, hf]

/-- Differentiation of the transported primitive commutes with the differential homomorphism. -/
theorem deriv_map_doubledOddPrimitive {B : Type*} [CommRing B] [Differential B]
    (f : A →+* B) (hf : ∀ a, f a′ = (f a)′) (n : ℕ) (u : A) :
    (f (doubledOddPrimitive n u))′ =
      2 * f u * f (differentialJet (2 * n + 1) u) := by
  rw [← hf, deriv_doubledOddPrimitive]
  simp only [map_mul, map_ofNat]

/-- A symmetry defect of the primitive differentiates to the defect of the odd product. -/
theorem deriv_doubledOddPrimitive_defect (f : A →+* A)
    (hf : ∀ a, f a′ = (f a)′) (n : ℕ) (u : A) :
    (f (doubledOddPrimitive n u) - doubledOddPrimitive n u)′ =
      2 * (f u * f (differentialJet (2 * n + 1) u) -
        u * differentialJet (2 * n + 1) u) := by
  rw [map_sub, deriv_map_doubledOddPrimitive f hf, deriv_doubledOddPrimitive]
  ring

/-- Polarization gives a primitive for the symmetric mixed odd product. -/
theorem deriv_doubledOddPrimitive_polarization (n : ℕ) (u v : A) :
    (doubledOddPrimitive n (u + v) - doubledOddPrimitive n u -
      doubledOddPrimitive n v)′ =
      2 * (u * differentialJet (2 * n + 1) v +
        v * differentialJet (2 * n + 1) u) := by
  have hadd (m : ℕ) : differentialJet m (u + v) = differentialJet m u + differentialJet m v := by
    induction m with
    | zero => rfl
    | succ m ih =>
        rw [differentialJet_succ, differentialJet_succ, differentialJet_succ, ih, map_add]
  rw [map_sub, map_sub, deriv_doubledOddPrimitive, deriv_doubledOddPrimitive,
    deriv_doubledOddPrimitive, hadd]
  ring

section Field

variable {F : Type*} [Field F] [CharZero F] [Differential F]

/-- The normalized quadratic primitive in characteristic zero. -/
def oddPrimitive (n : ℕ) (u : F) : F := doubledOddPrimitive n u / 2

/-- Every odd differential self-product has an explicit primitive in the same differential field. -/
theorem deriv_oddPrimitive (n : ℕ) (u : F) :
    (oddPrimitive n u)′ = u * differentialJet (2 * n + 1) u := by
  unfold oddPrimitive
  have htwoDeriv : (2 : F)′ = 0 := Derivation.map_natCast Differential.deriv 2
  rw [Derivation.leibniz_div_const Differential.deriv _ (2 : F) htwoDeriv,
    smul_eq_mul, deriv_doubledOddPrimitive]
  have htwo : (2 : F) ≠ 0 := two_ne_zero
  field_simp

omit [CharZero F] in
/-- The normalized primitive is also unchanged by global sign. -/
theorem oddPrimitive_neg (n : ℕ) (u : F) : oddPrimitive n (-u) = oddPrimitive n u := by
  rw [oddPrimitive, doubledOddPrimitive_neg, oddPrimitive]

end Field

#print axioms deriv_doubledOddPrimitive
#print axioms doubledOddPrimitive_neg
#print axioms map_doubledOddPrimitive
#print axioms deriv_doubledOddPrimitive_polarization
#print axioms deriv_doubledOddPrimitive_defect
#print axioms deriv_oddPrimitive

end GaloisForLFunctions.RepresentationLifting
