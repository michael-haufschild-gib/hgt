import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerCartierExactness

/-!
# A coordinate splitting of the Cartier exact sequence

Multiplying the highest coordinate monomial differential by the
Frobenius power of a coefficient gives a section of coefficient
extraction. Every differential is consequently the sum of an exact
form and this uniquely prescribed highest-coordinate contribution.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open Polynomial
variable (p : ℕ) [Fact p.Prime] (s : ℕ) (c : (SquareConstantField p s)ˣ) (b R : ℕ)
local notation "K" => SquareConstantField p s
local notation "L" => SquareKummerField p s c b R
local notation "Ω" => KaehlerDifferential K L
local notation "y" => algebraMap K[X] L X
local notation "dy" => KaehlerDifferential.D K L y

/-- The highest coordinate monomial gives an additive section of Frobenius coefficient extraction. -/
def squareKummerCoordinateCartierSection : Ω →+ Ω where
  toFun ω := (squareKummerDifferentialEquiv p s c b R ω) ^ p • (y ^ (p - 1) • dy)
  map_zero' := by
    rw [map_zero, zero_pow (Fact.out : p.Prime).ne_zero, zero_smul]
  map_add' ω η := by
    rw [map_add]
    change ((frobenius L p) (squareKummerDifferentialEquiv p s c b R ω +
      squareKummerDifferentialEquiv p s c b R η)) • (y ^ (p - 1) • dy) = _
    rw [map_add, add_smul]
    rfl

/-- Extracting the highest Frobenius coefficient after inserting it recovers every differential. -/
theorem squareKummerCoordinateCartier_section (ω : Ω) :
    squareKummerCoordinateCartier p s c b R
      (squareKummerCoordinateCartierSection p s c b R ω) = ω := by
  let j : Fin p := ⟨p - 1, Nat.sub_lt (Fact.out : p.Prime).pos Nat.zero_lt_one⟩
  change squareKummerCoordinateCartier p s c b R
    ((squareKummerDifferentialEquiv p s c b R ω) ^ p • (y ^ j.val • dy)) = _
  rw [squareKummerCoordinateCartier_frobenius_smul, squareKummerCoordinateCartier_power,
    if_pos (show j.val = p - 1 from rfl)]
  apply (squareKummerDifferentialEquiv p s c b R).injective
  rw [map_smul, squareKummerDifferentialEquiv_D_polynomial, derivative_X,
    map_one, smul_eq_mul, mul_one]

/-- The actual coefficient-extraction operator on Kähler differentials is surjective. -/
theorem squareKummerCoordinateCartier_surjective :
    Function.Surjective (squareKummerCoordinateCartier p s c b R) :=
  fun ω => ⟨squareKummerCoordinateCartierSection p s c b R ω,
    squareKummerCoordinateCartier_section p s c b R ω⟩

/-- Every differential differs from its prescribed highest-coordinate contribution by an exact form. -/
theorem squareKummer_differential_cartier_decomposition (ω : Ω) :
    ∃ f : L, ω = KaehlerDifferential.D K L f +
      squareKummerCoordinateCartierSection p s c b R
        (squareKummerCoordinateCartier p s c b R ω) := by
  have hzero : squareKummerCoordinateCartier p s c b R
      (ω - squareKummerCoordinateCartierSection p s c b R
        (squareKummerCoordinateCartier p s c b R ω)) = 0 := by
    rw [map_sub, squareKummerCoordinateCartier_section, sub_self]
  obtain ⟨f, hf⟩ := (squareKummerCoordinateCartier_eq_zero_iff p s c b R _).mp hzero
  exact ⟨f, (eq_sub_iff_add_eq.mp hf).symm⟩

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
