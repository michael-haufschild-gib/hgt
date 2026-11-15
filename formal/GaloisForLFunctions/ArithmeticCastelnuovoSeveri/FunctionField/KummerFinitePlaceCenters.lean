import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerNormalization
import GaloisForLFunctions.HTGeometry.ValuationInertiaRamificationIndex


/-!
# Finite places from valuation centers

A valuation ring containing constants and the polynomial coordinate
contains the integral closure. The Dedekind center dictionary identifies
every such proper valuation ring with a finite normalization prime.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open Polynomial IsDedekindDomain
open GaloisForLFunctions.HTGeometry.ValuationInertia

/-- A valuation ring containing the constants and the coordinate contains every polynomial. -/
theorem polynomial_algebraMap_mem_valuationSubring
    {K L : Type*} [Field K] [Field L] [Algebra K L] [Algebra K[X] L]
    [IsScalarTower K K[X] L] (W : ValuationSubring L)
    (hK : ∀ a : K, algebraMap K L a ∈ W)
    (hX : algebraMap K[X] L X ∈ W) (f : K[X]) : algebraMap K[X] L f ∈ W := by
  induction f using Polynomial.induction_on' with
  | add f g hf hg =>
      rw [map_add]
      exact add_mem hf hg
  | monomial n a =>
      rw [← C_mul_X_pow_eq_monomial, map_mul, map_pow]
      apply mul_mem _ (pow_mem hX n)
      have h := hK a
      rw [IsScalarTower.algebraMap_apply K K[X] L] at h
      exact h

/-- Every proper valuation ring containing constants and the affine coordinate is a finite normalization place. -/
theorem squareKummer_finitePlace_of_coordinate_mem
    (p : ℕ) [Fact p.Prime] (s : ℕ) (c : (SquareConstantField p s)ˣ) (b R : ℕ)
    (W : ValuationSubring (SquareKummerField p s c b R)) (hW : W ≠ ⊤)
    (hK : ∀ a : SquareConstantField p s, algebraMap (SquareConstantField p s)
      (SquareKummerField p s c b R) a ∈ W)
    (hX : algebraMap (SquareConstantField p s)[X] (SquareKummerField p s c b R) X ∈ W) :
    ∃ w : HeightOneSpectrum (SquareKummerNormalization p s c b R),
      (w.valuation (SquareKummerField p s c b R)).valuationSubring = W := by
  have hA := polynomial_algebraMap_mem_valuationSubring W hK hX
  have hB : ∀ x : SquareKummerNormalization p s c b R,
      algebraMap (SquareKummerNormalization p s c b R) (SquareKummerField p s c b R) x ∈ W :=
    integralClosure_mem_of_base_mem W hA
  refine ⟨centerHeightOne W hB hW, ?_⟩
  have h := valuationSubringAtPrime_eq W hB hW
  rw [HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring] at h
  exact h

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
