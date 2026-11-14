import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerNormalization
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.DedekindDomain.AdicValuation

/-!
# Places above the polynomial line

The normalization is an injective integral extension of the polynomial
base. Lying over therefore supplies an actual nonzero prime above every
finite base place. A chosen lift makes subsequent ramification statements
available without assuming that a place above the base point exists.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open Polynomial IsDedekindDomain

variable (p : ℕ) [Fact p.Prime] (s : ℕ) (c : (SquareConstantField p s)ˣ) (b R : ℕ)

/-- Every finite base place has a place above it in the Kummer normalization. -/
theorem squareKummer_exists_primeAbove (v : HeightOneSpectrum (SquareConstantField p s)[X]) :
    ∃ w : HeightOneSpectrum (SquareKummerNormalization p s c b R),
      w.asIdeal.LiesOver v.asIdeal := by
  let f := algebraMap (SquareConstantField p s)[X] (SquareKummerNormalization p s c b R)
  have hf : Function.Injective f := Module.isTorsionFree_iff_algebraMap_injective.mp inferInstance
  have hker : RingHom.ker f = ⊥ := (RingHom.injective_iff_ker_eq_bot f).mp hf
  obtain ⟨Q, _, hQ, hunder⟩ := Ideal.exists_ideal_over_prime_of_isIntegral v.asIdeal
    (⊥ : Ideal (SquareKummerNormalization p s c b R)) (by
      rw [← RingHom.ker_eq_comap_bot, hker]
      exact bot_le)
  have hQ0 : Q ≠ ⊥ := by
    intro h
    rw [h, ← RingHom.ker_eq_comap_bot, hker] at hunder
    exact v.ne_bot hunder.symm
  refine ⟨⟨Q, hQ, hQ0⟩, ?_⟩
  exact (Ideal.liesOver_iff Q v.asIdeal).mpr hunder.symm

/-- A chosen actual place of the normalization above a finite base place. -/
def squareKummerPrimeAbove (v : HeightOneSpectrum (SquareConstantField p s)[X]) :
    HeightOneSpectrum (SquareKummerNormalization p s c b R) :=
  (squareKummer_exists_primeAbove p s c b R v).choose

/-- The chosen place contracts to its specified base place. -/
instance squareKummerPrimeAbove_liesOver (v : HeightOneSpectrum (SquareConstantField p s)[X]) :
    (squareKummerPrimeAbove p s c b R v).asIdeal.LiesOver v.asIdeal :=
  (squareKummer_exists_primeAbove p s c b R v).choose_spec

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
