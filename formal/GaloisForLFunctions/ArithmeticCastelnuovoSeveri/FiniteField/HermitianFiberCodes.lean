import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FiniteField.KummerConstructedPointCount
import GaloisForLFunctions.ArithmeticHarmonicAnalysis.Codes.FiberPullbackCodes

/-!
# Divisible codes from Hermitian and Frobenius fibers

Over the field with `Q²` elements, the Hermitian first-coordinate projection,
the quadratic trace, and the Frobenius difference have fibers of size `Q`
or zero. Pullback of arbitrary functions therefore gives explicit codes whose
weights are divisible by the characteristic and whose pairings vanish for
every field endomorphism. In particular they are both Euclidean and Hermitian
self-orthogonal. The cardinality inputs are proved for the actual finite fields
and actual curve points.
-/

noncomputable section
open scoped Classical

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri

open ArithmeticHarmonicAnalysis.Codes

variable (p : ℕ) [Fact p.Prime]

local instance squareCodeFintype (s : ℕ) : Fintype (SquareConstantField p s) :=
  Fintype.ofFinite _

local instance hermitianCodeFintype (s : ℕ) : Fintype (HermitianAffinePoints p s) :=
  Fintype.ofFinite _

/-- Projection of actual Hermitian affine points to their first coordinate. -/
def hermitianFirstCoordinate (s : ℕ) : HermitianAffinePoints p s → SquareConstantField p s :=
  fun t => t.val.1

/-- Every fiber of the Hermitian projection has exactly `Q` points. -/
theorem hermitianFirstCoordinate_fiber_card (s : ℕ) (x : SquareConstantField p s) :
    Nat.card {t // hermitianFirstCoordinate p s t = x} = p ^ (s + 1) := by
  let e : {t // hermitianFirstCoordinate p s t = x} ≃
      {y : SquareConstantField p s | y ^ p ^ (s + 1) + y = x ^ (p ^ (s + 1) + 1)} :=
    { toFun := fun t => ⟨t.val.val.2,
        t.val.property.trans (congrArg (fun a => a ^ (p ^ (s + 1) + 1)) t.property)⟩
      invFun := fun y => ⟨⟨(x, y.val), y.property⟩, rfl⟩
      left_inv := fun t => Subtype.ext (Subtype.ext (Prod.ext t.property.symm rfl))
      right_inv := fun _ => rfl }
  exact (Nat.card_congr e).trans (squareFieldTrace_fiber_card_of_fixed p s _
    (squareConstantField_norm_fixed p s x))

/-- Evaluation of arbitrary functions of the first coordinate on all Hermitian affine points. -/
def hermitianCoordinateCode (s : ℕ) :
    Submodule (SquareConstantField p s) (HermitianAffinePoints p s → SquareConstantField p s) :=
  fiberCode (hermitianFirstCoordinate p s)

/-- The Hermitian projection reaches every element of the square field. -/
theorem hermitianFirstCoordinate_surjective (s : ℕ) :
    Function.Surjective (hermitianFirstCoordinate p s) := by
  intro x
  obtain ⟨y, hy⟩ := (squareFieldTrace_exists_iff p s _).mpr
    (squareConstantField_norm_fixed p s x)
  exact ⟨⟨(x, y), hy⟩, rfl⟩

/-- The length-`Q³` Hermitian coordinate code has dimension `Q²`. -/
theorem hermitianCoordinateCode_finrank (s : ℕ) :
    Module.finrank (SquareConstantField p s) (hermitianCoordinateCode p s) =
      p ^ (2 * (s + 1)) := by
  rw [hermitianCoordinateCode, fiberCode_finrank _ (hermitianFirstCoordinate_surjective p s),
    ← Nat.card_eq_fintype_card, squareConstantField_card]

/-- All Hermitian first-coordinate evaluation words have characteristic-divisible weight. -/
theorem hermitianCoordinateCode_divisible (s : ℕ) :
    Divisible p (hermitianCoordinateCode p s) := by
  apply fiberCode_divisible p
  intro x
  rw [hermitianFirstCoordinate_fiber_card]
  exact dvd_pow_self p (Nat.succ_ne_zero s)

/-- The actual Hermitian evaluation code is orthogonal for every field twist. -/
theorem hermitianCoordinateCode_selfOrthogonal (s : ℕ)
    (σ : SquareConstantField p s →+* SquareConstantField p s) :
    SelfOrthogonal σ (hermitianCoordinateCode p s) := by
  apply fiberCode_selfOrthogonal p
  intro x
  rw [hermitianFirstCoordinate_fiber_card]
  exact dvd_pow_self p (Nat.succ_ne_zero s)

/-- Heng–Xie's criterion applies to the concrete Hermitian coordinate code:
the nontrivial middle Frobenius supplies its Hermitian pairing. -/
theorem hermitianCoordinateCode_hermitian (s : ℕ) :
    SelfOrthogonal (iterateFrobenius (SquareConstantField p s) p (s + 1))
      (hermitianCoordinateCode p s) := by
  apply divisible_selfOrthogonal p _ ?_ _
    (one_mem_fiberCode _) (hermitianCoordinateCode_divisible p s)
  intro h
  obtain ⟨x, hx⟩ := squareConstantField_exists_not_fixed p s
  exact hx (DFunLike.congr_fun h x)

/-- Words on the square field obtained by pullback along its quadratic trace. -/
def squareTraceCode (s : ℕ) :
    Submodule (SquareConstantField p s) (SquareConstantField p s → SquareConstantField p s) :=
  fiberCode (squareFieldTrace p s)

/-- The trace code has divisible weights, including in characteristic two. -/
theorem squareTraceCode_divisible (s : ℕ) : Divisible p (squareTraceCode p s) := by
  apply fiberCode_divisible p
  apply additive_fiber_card_dvd p (squareFieldTrace p s)
  rw [squareFieldTrace_kernel_card]
  exact dvd_pow_self p (Nat.succ_ne_zero s)

/-- Trace-fiber words are orthogonal for all twists simultaneously. -/
theorem squareTraceCode_selfOrthogonal (s : ℕ)
    (σ : SquareConstantField p s →+* SquareConstantField p s) :
    SelfOrthogonal σ (squareTraceCode p s) := by
  apply fiberCode_selfOrthogonal p
  apply additive_fiber_card_dvd p (squareFieldTrace p s)
  rw [squareFieldTrace_kernel_card]
  exact dvd_pow_self p (Nat.succ_ne_zero s)

/-- The additive Frobenius difference on the square field. -/
def squareFrobeniusDifference (s : ℕ) : SquareConstantField p s →+ SquareConstantField p s :=
  AddMonoidHom.id _ - (iterateFrobenius (SquareConstantField p s) p (s + 1)).toAddMonoidHom

/-- The difference kernel is exactly the middle fixed field. -/
def squareDifferenceKernelEquivFixed (s : ℕ) :
    (squareFrobeniusDifference p s).ker ≃ squareFrobeniusFixedField p s where
  toFun x := ⟨x.val, (sub_eq_zero.mp (show x.val - x.val ^ p ^ (s + 1) = 0 from
    x.property)).symm⟩
  invFun x := ⟨x.val, sub_eq_zero.mpr (show x.val ^ p ^ (s + 1) = x.val from
    x.property).symm⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The difference kernel has cardinality `Q`. -/
theorem squareFrobeniusDifference_kernel_card (s : ℕ) :
    Nat.card (squareFrobeniusDifference p s).ker = p ^ (s + 1) :=
  (Nat.card_congr (squareDifferenceKernelEquivFixed p s)).trans
    (squareFrobeniusFixedField_card p s)

/-- Words constant on additive cosets of the middle field. -/
def squareDifferenceCode (s : ℕ) :
    Submodule (SquareConstantField p s) (SquareConstantField p s → SquareConstantField p s) :=
  fiberCode (squareFrobeniusDifference p s)

/-- The Frobenius-difference code has characteristic-divisible weights. -/
theorem squareDifferenceCode_divisible (s : ℕ) : Divisible p (squareDifferenceCode p s) := by
  apply fiberCode_divisible p
  apply additive_fiber_card_dvd p (squareFrobeniusDifference p s)
  rw [squareFrobeniusDifference_kernel_card]
  exact dvd_pow_self p (Nat.succ_ne_zero s)

/-- Frobenius-difference words are orthogonal for every field endomorphism. -/
theorem squareDifferenceCode_selfOrthogonal (s : ℕ)
    (σ : SquareConstantField p s →+* SquareConstantField p s) :
    SelfOrthogonal σ (squareDifferenceCode p s) := by
  apply fiberCode_selfOrthogonal p
  apply additive_fiber_card_dvd p (squareFrobeniusDifference p s)
  rw [squareFrobeniusDifference_kernel_card]
  exact dvd_pow_self p (Nat.succ_ne_zero s)

#print axioms hermitianCoordinateCode_selfOrthogonal
#print axioms hermitianCoordinateCode_hermitian
#print axioms hermitianCoordinateCode_divisible
#print axioms hermitianCoordinateCode_finrank
#print axioms squareTraceCode_selfOrthogonal
#print axioms squareTraceCode_divisible
#print axioms squareDifferenceCode_selfOrthogonal
#print axioms squareDifferenceCode_divisible

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
