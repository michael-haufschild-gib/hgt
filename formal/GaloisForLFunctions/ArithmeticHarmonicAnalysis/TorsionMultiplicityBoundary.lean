import GaloisForLFunctions.HTGeometry.RationalOrderComposition
import Mathlib.FieldTheory.Separable
import Mathlib.RingTheory.Nullstellensatz
import Mathlib.Analysis.Fourier.ZMod

/-!
# The sharp integer boundary for torsion multiplicity

The integer polynomial `(X^q - 1)^r` has degree `qr` and multiplicity
exactly `r` at every `q`th root of unity. Reading exponent `j` as the
integer `2^j` puts its largest arithmetic frequency at `2^(qr)`.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis

open Polynomial

/-- The sharp boundary auxiliary in the prime-two coordinate. -/
def torsionBoundaryPolynomial (q r : ℕ) : ℂ[X] := (X ^ q - C 1) ^ r

/-- The boundary auxiliary has integer coefficients. -/
theorem torsionBoundaryPolynomial_integral (q r : ℕ) :
    Polynomial.map (Int.castRingHom ℂ) (((X : ℤ[X]) ^ q - 1) ^ r) =
      torsionBoundaryPolynomial q r := by
  simp only [torsionBoundaryPolynomial, Polynomial.map_pow, Polynomial.map_sub,
    Polynomial.map_X, Polynomial.map_one, C_1]

theorem torsionBoundaryPolynomial_monic (q r : ℕ) [NeZero q] :
    (torsionBoundaryPolynomial q r).Monic :=
  (monic_X_pow_sub_C (1 : ℂ) (NeZero.ne q)).pow r

/-- The top prime-two exponent is exactly `qr`, hence the top integer is `2^(qr)`. -/
theorem torsionBoundaryPolynomial_natDegree (q r : ℕ) [NeZero q] :
    (torsionBoundaryPolynomial q r).natDegree = q * r := by
  rw [torsionBoundaryPolynomial, (monic_X_pow_sub_C (1 : ℂ) (NeZero.ne q)).natDegree_pow,
    natDegree_X_pow_sub_C, Nat.mul_comm]

theorem torsionBoundaryPolynomial_top_coefficient (q r : ℕ) [NeZero q] :
    (torsionBoundaryPolynomial q r).coeff (q * r) = 1 := by
  rw [← torsionBoundaryPolynomial_natDegree q r]
  exact (torsionBoundaryPolynomial_monic q r).coeff_natDegree

/-- Exponent `j` in the prime-two coordinate represents the positive integer `2^j`. -/
def torsionBoundaryArithmeticSupport (q r : ℕ) : Finset ℕ :=
  (torsionBoundaryPolynomial q r).support.image fun j => 2 ^ j

/-- The boundary auxiliary reaches exactly the predicted integer support threshold. -/
theorem torsionBoundaryArithmeticSupport_max (q r : ℕ) [NeZero q] :
    2 ^ (q * r) ∈ torsionBoundaryArithmeticSupport q r ∧
      ∀ n ∈ torsionBoundaryArithmeticSupport q r, n ≤ 2 ^ (q * r) := by
  constructor
  · apply Finset.mem_image.mpr
    refine ⟨q * r, ?_, rfl⟩
    rw [Polynomial.mem_support_iff, torsionBoundaryPolynomial_top_coefficient]
    exact one_ne_zero
  · intro n hn
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hn
    apply Nat.pow_le_pow_right (by omega : 0 < (2 : ℕ))
    rw [← torsionBoundaryPolynomial_natDegree q r]
    exact Polynomial.le_natDegree_of_ne_zero (Polynomial.mem_support_iff.mp hj)

/-- Every `q`th root of unity has exactly multiplicity `r` in the boundary auxiliary. -/
theorem torsionBoundaryPolynomial_rootMultiplicity (q r : ℕ) [NeZero q]
    (z : ℂ) (hz : z ^ q = 1) :
    (torsionBoundaryPolynomial q r).rootMultiplicity z = r := by
  have hmon := monic_X_pow_sub_C (1 : ℂ) (NeZero.ne q)
  have hsep : (X ^ q - C (1 : ℂ)).Separable := by
    apply separable_X_pow_sub_C_unit (1 : ℂˣ)
    exact isUnit_iff_ne_zero.mpr (by exact_mod_cast NeZero.ne q)
  have hroot : (X ^ q - C (1 : ℂ)).IsRoot z := by
    simp only [IsRoot.def, eval_sub, eval_pow, eval_X, eval_C, hz, sub_self]
  have hm : (X ^ q - C (1 : ℂ)).rootMultiplicity z = 1 :=
    Nat.le_antisymm (rootMultiplicity_le_one_of_separable hsep z)
      ((rootMultiplicity_pos hmon.ne_zero).mpr hroot)
  rw [torsionBoundaryPolynomial, HTGeometry.rootMultiplicity_pow hmon.ne_zero, hm, mul_one]

/-- The standard torsion-grid coordinate is a `q`th root of unity. -/
theorem stdAddChar_pow_order (q : ℕ) [NeZero q] (t : ZMod q) :
    ZMod.stdAddChar t ^ q = 1 := by
  rw [← AddChar.map_nsmul_eq_pow, nsmul_eq_mul, ZMod.natCast_self, zero_mul,
    AddChar.map_zero_eq_one]

/-- The same boundary polynomial has full multivariate point multiplicity at every torsion point. -/
theorem torsionBoundary_mem_pointIdeal_pow {ι : Type*} (q r : ℕ) [NeZero q]
    (i : ι) (t : ι → ZMod q) :
    ((MvPolynomial.X i : MvPolynomial ι ℂ) ^ q - 1) ^ r ∈
      MvPolynomial.vanishingIdeal ℂ {fun j => ZMod.stdAddChar (t j)} ^ r := by
  apply Ideal.pow_mem_pow
  rw [MvPolynomial.mem_vanishingIdeal_singleton_iff, MvPolynomial.aeval_eq_eval]
  simp only [map_sub, map_pow, MvPolynomial.eval_X, map_one,
    stdAddChar_pow_order, sub_self]

end GaloisForLFunctions.ArithmeticHarmonicAnalysis
