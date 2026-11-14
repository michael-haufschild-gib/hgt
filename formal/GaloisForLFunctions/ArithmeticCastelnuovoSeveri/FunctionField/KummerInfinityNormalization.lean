import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerInfinityCoordinate
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.DedekindDomain.AdicValuation

/-!
# Normalization of the reciprocal-coordinate chart

The integral closure of `k[t]` in the inverted Kummer field is a finite
free Dedekind domain of rank `Q+1`. Its primes over `t=0` represent the
places at infinity of the original coordinate; lying over supplies them.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open Polynomial IsDedekindDomain
variable (p : ℕ) [Fact p.Prime] (s : ℕ) (c : (SquareConstantField p s)ˣ) (b R : ℕ)

/-- The actual integral closure in the reciprocal-coordinate field. -/
abbrev SquareKummerInfinityNormalization :=
  integralClosure (SquareConstantField p s)[X] (KummerInfinityField c b R (p ^ (s + 1)))

/-- Separability makes the normalization a Dedekind domain. -/
instance squareKummerInfinityNormalization_dedekind :
    IsDedekindDomain (SquareKummerInfinityNormalization p s c b R) := by
  letI := squareKummerInfinity_isGalois p s c b R
  infer_instance

/-- The normalized chart is finite over the polynomial base. -/
instance squareKummerInfinityNormalization_finite :
    Module.Finite (SquareConstantField p s)[X] (SquareKummerInfinityNormalization p s c b R) := by
  letI := squareKummerInfinity_isGalois p s c b R
  exact IsIntegralClosure.finite (SquareConstantField p s)[X]
    (FractionRing (SquareConstantField p s)[X]) (KummerInfinityField c b R (p ^ (s + 1))) _

/-- Torsion-freeness over the polynomial PID gives freeness. -/
instance squareKummerInfinityNormalization_free :
    Module.Free (SquareConstantField p s)[X] (SquareKummerInfinityNormalization p s c b R) := by
  letI := squareKummerInfinity_isGalois p s c b R
  exact IsIntegralClosure.module_free (SquareConstantField p s)[X]
    (FractionRing (SquareConstantField p s)[X]) (KummerInfinityField c b R (p ^ (s + 1))) _

/-- The chart recovers the inverted Kummer function field. -/
instance squareKummerInfinityNormalization_fractionRing :
    IsFractionRing (SquareKummerInfinityNormalization p s c b R)
      (KummerInfinityField c b R (p ^ (s + 1))) :=
  IsIntegralClosure.isFractionRing_of_finite_extension (SquareConstantField p s)[X]
    (FractionRing (SquareConstantField p s)[X]) (KummerInfinityField c b R (p ^ (s + 1))) _

/-- The normalization has rank equal to the covering degree. -/
theorem squareKummerInfinityNormalization_finrank :
    Module.finrank (SquareConstantField p s)[X] (SquareKummerInfinityNormalization p s c b R) =
      p ^ (s + 1) + 1 := by
  letI := squareKummerInfinity_isGalois p s c b R
  rw [IsIntegralClosure.rank (SquareConstantField p s)[X]
    (FractionRing (SquareConstantField p s)[X]) (KummerInfinityField c b R (p ^ (s + 1)))]
  exact kummerInfinityField_finrank c b R _

/-- Every finite place of the reciprocal base has a place in its normalization. -/
theorem squareKummerInfinity_exists_primeAbove (v : HeightOneSpectrum (SquareConstantField p s)[X]) :
    ∃ w : HeightOneSpectrum (SquareKummerInfinityNormalization p s c b R),
      w.asIdeal.LiesOver v.asIdeal := by
  let f := algebraMap (SquareConstantField p s)[X] (SquareKummerInfinityNormalization p s c b R)
  have hf : Function.Injective f := Module.isTorsionFree_iff_algebraMap_injective.mp inferInstance
  have hker : RingHom.ker f = ⊥ := (RingHom.injective_iff_ker_eq_bot f).mp hf
  obtain ⟨Q, _, hQ, hunder⟩ := Ideal.exists_ideal_over_prime_of_isIntegral v.asIdeal
    (⊥ : Ideal (SquareKummerInfinityNormalization p s c b R)) (by
      rw [← RingHom.ker_eq_comap_bot, hker]
      exact bot_le)
  have hQ0 : Q ≠ ⊥ := by
    intro h
    rw [h, ← RingHom.ker_eq_comap_bot, hker] at hunder
    exact v.ne_bot hunder.symm
  refine ⟨⟨Q, hQ, hQ0⟩, ?_⟩
  exact (Ideal.liesOver_iff Q v.asIdeal).mpr hunder.symm

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
