import GaloisForLFunctions.ArithmeticHarmonicAnalysis.FiniteField.FrobeniusTracePolynomials
import Mathlib.RingTheory.Polynomial.Dickson

/-!
# Characteristic reduction of Chebyshev equations

Multiplying a normalized Chebyshev index by a power of the characteristic
raises the polynomial to that power. The Frobenius trace gives an explicit
translation between the corresponding Artin–Schreier equations, over every
commutative ring of prime characteristic.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis
open Polynomial

variable {A : Type*} [CommRing A] (p : ℕ) [Fact p.Prime] [CharP A p]

/-- The normalized Chebyshev polynomial at a prime-power index is a monomial. -/
theorem dickson_primePower (s : ℕ) :
    dickson 1 (1 : A) (p ^ s) = X ^ (p ^ s) := by
  induction s with
  | zero => simp only [pow_zero, dickson_one, pow_one]
  | succ s ih =>
    rw [pow_succ, Nat.mul_comm (p ^ s) p, dickson_one_one_mul,
      dickson_one_one_charP, Polynomial.pow_comp, Polynomial.X_comp, ih, ← pow_mul,
      Nat.mul_comm]

/-- Removing powers of the characteristic is a polynomial identity, including at index zero. -/
theorem dickson_characteristic_reduction (s m : ℕ) :
    dickson 1 (1 : A) (p ^ s * m) = dickson 1 (1 : A) m ^ (p ^ s) := by
  rw [dickson_one_one_mul, dickson_primePower, Polynomial.pow_comp, Polynomial.X_comp]

/-- The trace translation identifies the complete equation defects. -/
theorem artinSchreier_trace_translation (s : ℕ) (f y : A) :
    (y - frobeniusTraceSum p 1 s f) ^ p -
        (y - frobeniusTraceSum p 1 s f) - f =
      y ^ p - y - f ^ (p ^ s) := by
  have ht := frobeniusTraceSum_sub_pow p 1 s f
  simp only [pow_one, one_mul] at ht
  rw [sub_pow_char]
  linear_combination ht

/-- Frobenius changes of the right-hand side preserve the full solution set. -/
def artinSchreierFrobeniusEquiv (s : ℕ) (f : A) :
    {y : A // y ^ p - y = f ^ (p ^ s)} ≃ {z : A // z ^ p - z = f} where
  toFun y := ⟨y.1 - frobeniusTraceSum p 1 s f, by
    have h := artinSchreier_trace_translation p s f y.1
    rw [y.2, sub_self] at h
    exact sub_eq_zero.mp h⟩
  invFun z := ⟨z.1 + frobeniusTraceSum p 1 s f, by
    have h := artinSchreier_trace_translation p s f
      (z.1 + frobeniusTraceSum p 1 s f)
    rw [add_sub_cancel_right, z.2, sub_self] at h
    exact sub_eq_zero.mp h.symm⟩
  left_inv y := Subtype.ext (sub_add_cancel _ _)
  right_inv z := Subtype.ext (add_sub_cancel_right _ _)

/-- Chebyshev Artin–Schreier affine points, with no smoothness assumption. -/
def chebyshevArtinSchreierPoints (m : ℕ) :=
  {xy : A × A // xy.2 ^ p - xy.2 = (dickson 1 (1 : A) m).eval xy.1}

/-- The degree reduction is an explicit equivalence fixing the first coordinate. -/
def chebyshevArtinSchreierReduction (s m : ℕ) :
    chebyshevArtinSchreierPoints (A := A) p (p ^ s * m) ≃
      chebyshevArtinSchreierPoints (A := A) p m where
  toFun xy := ⟨(xy.1.1,
      xy.1.2 - frobeniusTraceSum p 1 s ((dickson 1 (1 : A) m).eval xy.1.1)), by
    have hxy := xy.2
    simp only [dickson_characteristic_reduction, eval_pow] at hxy
    exact (artinSchreierFrobeniusEquiv p s _ ⟨xy.1.2, hxy⟩).2⟩
  invFun xy := ⟨(xy.1.1,
      xy.1.2 + frobeniusTraceSum p 1 s ((dickson 1 (1 : A) m).eval xy.1.1)), by
    change _ = (dickson 1 (1 : A) (p ^ s * m)).eval xy.1.1
    rw [dickson_characteristic_reduction, eval_pow]
    exact ((artinSchreierFrobeniusEquiv p s _).symm ⟨xy.1.2, xy.2⟩).2⟩
  left_inv xy := by apply Subtype.ext; exact Prod.ext rfl (sub_add_cancel _ _)
  right_inv xy := by apply Subtype.ext; exact Prod.ext rfl (add_sub_cancel_right _ _)

/-- The characteristic reduction leaves the base coordinate unchanged. -/
theorem chebyshevArtinSchreierReduction_fst (s m : ℕ)
    (xy : chebyshevArtinSchreierPoints (A := A) p (p ^ s * m)) :
    (chebyshevArtinSchreierReduction p s m xy).1.1 = xy.1.1 := rfl

end GaloisForLFunctions.ArithmeticHarmonicAnalysis
