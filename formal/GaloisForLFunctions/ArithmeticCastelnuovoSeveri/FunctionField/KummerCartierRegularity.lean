import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerCartierParameterExpansion
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerLocalRegularityCriterion

/-!
# Cartier preserves intrinsic regular differentials

An integral coefficient has a uniformizer expansion whose Frobenius
roots are all integral. Cartier extraction retains one such root, so
it preserves the actual local Kähler image. The classification of
constant-field places then gives preservation of global regularity.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open Polynomial IsDedekindDomain ArithmeticHarmonicAnalysis
open GaloisForLFunctions.HTGeometry

/-- Cartier extraction preserves the actual local Kähler image at every normalized uniformizer valuation. -/
theorem squareKummerCoordinateCartier_local_regular
    (p : ℕ) [Fact p.Prime] (s : ℕ) (c : (SquareConstantField p s)ˣ) (b R : ℕ)
    (v : Valuation (SquareKummerField p s c b R) (WithZero (Multiplicative ℤ)))
    (hK : ∀ a : SquareConstantField p s,
      algebraMap (SquareConstantField p s) (SquareKummerField p s c b R) a ∈ v.valuationSubring)
    (π : SquareKummerField p s c b R) (hπ : v π = WithZero.exp (-1 : ℤ))
    (ω : KaehlerDifferential (SquareConstantField p s) (SquareKummerField p s c b R)) :
    ω ∈ valuationLocalDifferentials v.valuationSubring hK →
      squareKummerCoordinateCartier p s c b R ω ∈ valuationLocalDifferentials v.valuationSubring hK := by
  intro hω
  obtain ⟨f, hf, rfl⟩ := (squareKummer_mem_localDifferentials_iff p s c b R v hK π hπ ω).mp hω
  obtain ⟨a, ha, he⟩ := squareKummer_uniformizer_integral_power_expansion p s c b R v π hπ f hf
  let j : Fin p := ⟨p - 1, Nat.sub_lt (Fact.out : p.Prime).pos Nat.zero_lt_one⟩
  apply (squareKummer_mem_localDifferentials_iff p s c b R v hK π hπ _).mpr
  refine ⟨a j, ha j, ?_⟩
  rw [he, Finset.sum_smul]
  simp only [mul_smul]
  exact squareKummerCoordinateCartier_parameter_expansion p s c b R π a j rfl

/-- Cartier extraction preserves the actual global regular differential space of the prime-power family. -/
theorem squareKummerCoordinateCartier_global_regular
    (p : ℕ) [Fact p.Prime] (s : ℕ) (c : (SquareConstantField p s)ˣ) (d r : ℕ)
    (ω : KaehlerDifferential (SquareConstantField p s)
      (SquareKummerField p s c (p ^ (d + 1) - 2) (kummerExponent (p ^ (d + 1)) r))) :
    ω ∈ globalRegularDifferentials (SquareConstantField p s)
      (SquareKummerField p s c (p ^ (d + 1) - 2) (kummerExponent (p ^ (d + 1)) r)) →
    squareKummerCoordinateCartier p s c (p ^ (d + 1) - 2) (kummerExponent (p ^ (d + 1)) r) ω ∈
      globalRegularDifferentials (SquareConstantField p s)
        (SquareKummerField p s c (p ^ (d + 1) - 2) (kummerExponent (p ^ (d + 1)) r)) := by
  intro hω
  let b := p ^ (d + 1) - 2
  let R := kummerExponent (p ^ (d + 1)) r
  let L := SquareKummerField p s c b R
  have hlocal := (mem_globalRegularDifferentials_iff _).mp hω
  rw [mem_globalRegularDifferentials_iff]
  intro W
  rcases squareKummer_constantPlace_cases p s c d r W with ⟨v, hv⟩ | hv
  · rw [← hv]
    exact squareKummerCoordinateCartier_local_regular p s c b R (v.valuation L)
      (heightOne_constants_mem v) (placeUniformizer L v) (placeUniformizer_valuation L v) ω
      (hlocal (squareKummerFiniteConstantPlace p s c d r v))
  · rw [← hv]
    exact squareKummerCoordinateCartier_local_regular p s c b R
      (squareKummerInfinityValuation p s c d r)
      (squareKummerInfinityConstantPlace p s c d r).property.2
      (squareKummerInfinityUniformizer p s c d r) (squareKummerInfinityUniformizer_value p s c d r) ω
      (hlocal (squareKummerInfinityConstantPlace p s c d r))

/-- The Cartier operator restricts to an additive endomorphism of actual global regular differentials. -/
def squareKummerRegularCartier
    (p : ℕ) [Fact p.Prime] (s : ℕ) (c : (SquareConstantField p s)ˣ) (d r : ℕ) :
    globalRegularDifferentials (SquareConstantField p s)
      (SquareKummerField p s c (p ^ (d + 1) - 2) (kummerExponent (p ^ (d + 1)) r)) →+
    globalRegularDifferentials (SquareConstantField p s)
      (SquareKummerField p s c (p ^ (d + 1) - 2) (kummerExponent (p ^ (d + 1)) r)) where
  toFun ω := ⟨squareKummerCoordinateCartier p s c (p ^ (d + 1) - 2)
    (kummerExponent (p ^ (d + 1)) r) ω.val,
    squareKummerCoordinateCartier_global_regular p s c d r ω.val ω.property⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' ω η := Subtype.ext (map_add _ _ _)

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
