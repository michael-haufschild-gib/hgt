import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerInfinityFunctionOrders
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.RationalPlaceValuations
import GaloisForLFunctions.HTGeometry.PlaceUnivFactor


/-!
# Polynomial pole orders at Kummer infinity

The leading-term valuation theorem applies to the image of the constant
field in the infinity chart. Thus a nonzero polynomial in the original
coordinate has pole order equal to its degree times the covering degree.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open Polynomial IsDedekindDomain ArithmeticHarmonicAnalysis
open GaloisForLFunctions.HTGeometry

/-- Polynomial evaluation at a pole has valuation given exactly by its degree. -/
theorem heightOne_aeval_valuation
    {K B L : Type*} [Field K] [CommRing B] [IsDedekindDomain B]
    [Algebra K B] [Field L] [Algebra B L] [IsFractionRing B L] [Algebra K L]
    [IsScalarTower K B L] (w : HeightOneSpectrum B) (x : L)
    (hx : 1 < w.valuation L x) (f : K[X]) (hf : f ≠ 0) :
    w.valuation L (aeval x f) = (w.valuation L x) ^ f.natDegree := by
  let F := (algebraMap K L).fieldRange
  have hF : PlaceTrivialOn w F := by
    rintro _ ⟨a, rfl⟩ ha
    apply heightOne_valuation_constant w a
    intro h
    apply ha
    rw [h, map_zero]
  have hcoeff : CoeffsIn F (f.map (algebraMap K L)) := by
    intro i
    rw [coeff_map]
    exact ⟨f.coeff i, rfl⟩
  have h := valuation_eval_eq w hF hcoeff hx (Polynomial.map_ne_zero hf)
  simpa only [Polynomial.eval_map, Polynomial.aeval_def, Polynomial.natDegree_map] using h

/-- A nonzero coordinate polynomial has pole order `(Q+1) deg(f)` at the actual infinity place. -/
theorem squareKummerInfinityValuation_polynomial
    (p : ℕ) [Fact p.Prime] (s : ℕ) (c : (SquareConstantField p s)ˣ) (d r : ℕ)
    (f : (SquareConstantField p s)[X]) (hf : f ≠ 0) :
    squareKummerInfinityValuation p s c d r
      (algebraMap (SquareConstantField p s)[X]
        (SquareKummerField p s c (p ^ (d + 1) - 2) (kummerExponent (p ^ (d + 1)) r)) f) =
      WithZero.exp (((p ^ (s + 1) + 1) * f.natDegree : ℕ) : ℤ) := by
  let K := SquareConstantField p s
  let b := p ^ (d + 1) - 2
  let R := kummerExponent (p ^ (d + 1)) r
  let L := SquareKummerField p s c b R
  let T := KummerInfinityField c b R (p ^ (s + 1))
  let e := kummerInfinityFieldEquiv c b R (p ^ (s + 1))
  let w := squareKummerInfinityPlace p s c d r
  let y : T := e (algebraMap K[X] L X)
  have hy : w.valuation T y = WithZero.exp ((p ^ (s + 1) + 1 : ℕ) : ℤ) :=
    squareKummerInfinityValuation_coordinate p s c d r
  have hygt : 1 < w.valuation T y := by
    rw [hy, ← WithZero.exp_zero, WithZero.exp_lt_exp]
    exact_mod_cast Nat.succ_pos (p ^ (s + 1))
  have hhom : e.toAlgHom.comp (IsScalarTower.toAlgHom K K[X] L) = aeval y := by
    apply Polynomial.algHom_ext
    rw [aeval_X]
    rfl
  have hpoly : e (algebraMap K[X] L f) = aeval y f :=
    congrArg (fun h : K[X] →ₐ[K] T => h f) hhom
  change w.valuation T (e (algebraMap K[X] L f)) = _
  rw [hpoly, heightOne_aeval_valuation w y hygt f hf, hy, ← WithZero.exp_nsmul]
  congr 1
  simp only [nsmul_eq_mul, Nat.cast_mul]
  ring

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
