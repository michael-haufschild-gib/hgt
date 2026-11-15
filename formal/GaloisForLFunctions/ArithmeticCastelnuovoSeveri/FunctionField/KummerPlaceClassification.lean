import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerInfinityPlaceCenter
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerInfinityFunctionOrders
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.AdicPlaceEmbedding
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.RationalValuationResidues

/-!
# Intrinsic places of prime-power Kummer fields

A place is a proper valuation ring containing the constants. The finite
normalization primes embed into these places, and their image together
with the distinct infinity place exhausts every constant-field place.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open Polynomial IsDedekindDomain ArithmeticHarmonicAnalysis

/-- A place of a function field is a proper valuation ring containing its constant field. -/
def ConstantFieldPlaces (K L : Type*) [Field K] [Field L] [Algebra K L] :=
  {W : ValuationSubring L // W ≠ ⊤ ∧ ∀ a : K, algebraMap K L a ∈ W}

variable (p : ℕ) [Fact p.Prime] (s : ℕ) (c : (SquareConstantField p s)ˣ) (d r : ℕ)

/-- The polynomial coordinate is not integral at the infinity place. -/
theorem squareKummerInfinity_coordinate_notMem :
    algebraMap (SquareConstantField p s)[X]
      (SquareKummerField p s c (p ^ (d + 1) - 2) (kummerExponent (p ^ (d + 1)) r)) X ∉
      (squareKummerInfinityValuation p s c d r).valuationSubring := by
  intro h
  change squareKummerInfinityValuation p s c d r _ ≤ 1 at h
  rw [squareKummerInfinityValuation_coordinate, ← WithZero.exp_zero, WithZero.exp_le_exp] at h
  omega

/-- The valuation at infinity is a proper valuation ring containing every constant. -/
def squareKummerInfinityConstantPlace :
    ConstantFieldPlaces (SquareConstantField p s)
      (SquareKummerField p s c (p ^ (d + 1) - 2) (kummerExponent (p ^ (d + 1)) r)) := by
  refine ⟨(squareKummerInfinityValuation p s c d r).valuationSubring, ?_, ?_⟩
  · intro h
    apply squareKummerInfinity_coordinate_notMem p s c d r
    rw [h]
    trivial
  · intro a
    change (squareKummerInfinityPlace p s c d r).valuation _
      (kummerInfinityFieldEquiv c (p ^ (d + 1) - 2) (kummerExponent (p ^ (d + 1)) r)
        (p ^ (s + 1)) (algebraMap (SquareConstantField p s) _ a)) ≤ 1
    rw [AlgEquiv.commutes]
    exact heightOne_constants_mem (squareKummerInfinityPlace p s c d r) a

/-- Finite normalization places define constant-field places of the original function field. -/
def squareKummerFiniteConstantPlace
    (w : HeightOneSpectrum (SquareKummerNormalization p s c (p ^ (d + 1) - 2)
      (kummerExponent (p ^ (d + 1)) r))) :
    ConstantFieldPlaces (SquareConstantField p s)
      (SquareKummerField p s c (p ^ (d + 1) - 2) (kummerExponent (p ^ (d + 1)) r)) :=
  ⟨(w.valuation _).valuationSubring, heightOne_valuationSubring_ne_top w,
    heightOne_constants_mem w⟩

/-- The affine normalization and the unique infinity place cover every constant-field valuation ring. -/
theorem squareKummer_constantPlace_cases
    (W : ConstantFieldPlaces (SquareConstantField p s)
      (SquareKummerField p s c (p ^ (d + 1) - 2) (kummerExponent (p ^ (d + 1)) r))) :
    (∃ w, squareKummerFiniteConstantPlace p s c d r w = W) ∨
      squareKummerInfinityConstantPlace p s c d r = W := by
  by_cases hX : algebraMap (SquareConstantField p s)[X]
      (SquareKummerField p s c (p ^ (d + 1) - 2) (kummerExponent (p ^ (d + 1)) r)) X ∈ W.val
  · obtain ⟨w, hw⟩ := squareKummer_finitePlace_of_coordinate_mem p s c _ _ W.val W.property.1 W.property.2 hX
    exact Or.inl ⟨w, Subtype.ext hw⟩
  · right
    apply Subtype.ext
    exact (squareKummer_infinityPlace_of_coordinate_notMem p s c d r W.val W.property.1 W.property.2 hX).symm

/-- Distinct finite primes give distinct constant-field places. -/
theorem squareKummerFiniteConstantPlace_injective :
    Function.Injective (squareKummerFiniteConstantPlace p s c d r) := by
  intro v w h
  exact heightOne_valuationSubring_injective (congrArg Subtype.val h)

/-- Infinity is distinct from every finite normalization place. -/
theorem squareKummerFiniteConstantPlace_ne_infinity
    (w : HeightOneSpectrum (SquareKummerNormalization p s c (p ^ (d + 1) - 2)
      (kummerExponent (p ^ (d + 1)) r))) :
    squareKummerFiniteConstantPlace p s c d r w ≠ squareKummerInfinityConstantPlace p s c d r := by
  intro h
  have hX : algebraMap (SquareConstantField p s)[X]
      (SquareKummerField p s c (p ^ (d + 1) - 2) (kummerExponent (p ^ (d + 1)) r)) X ∈
        (squareKummerFiniteConstantPlace p s c d r w).val := by
    rw [IsScalarTower.algebraMap_apply (SquareConstantField p s)[X]
      (SquareKummerNormalization p s c (p ^ (d + 1) - 2) (kummerExponent (p ^ (d + 1)) r))]
    exact GaloisForLFunctions.HTGeometry.algebraMap_mem_valuationSubringAtPlace _ w _
  rw [h] at hX
  exact squareKummerInfinity_coordinate_notMem p s c d r hX

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
