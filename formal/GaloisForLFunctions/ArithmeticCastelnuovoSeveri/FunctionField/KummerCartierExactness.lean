import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerCartierParameterExpansion

/-!
# Exactness detected by the highest Frobenius coefficient

In the separating coordinate, every lower Frobenius monomial has an
explicit primitive: divide by its next exponent, which is nonzero in
characteristic `p`. The highest monomial is the sole obstruction.
Thus coefficient extraction vanishes exactly on exact Kähler forms.
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

/-- Each lower Frobenius monomial has an explicit primitive in the same function field. -/
theorem squareKummer_frobenius_monomial_primitive (a : L) (i : Fin p) (hi : i.val < p - 1) :
    KaehlerDifferential.D K L
      ((a ^ p * algebraMap K L ((i.val + 1 : K)⁻¹)) * y ^ (i.val + 1)) =
        (a ^ p * y ^ i.val) • dy := by
  let D : Derivation K L Ω := KaehlerDifferential.D K L
  have hprimitive := squareKummer_lower_monomial_primitive p s c b R y i.val hi
  simp only [Nat.cast_add, Nat.cast_one] at hprimitive
  rw [mul_assoc, D.leibniz, derivation_frobenius_power_eq_zero p D a,
    smul_zero, add_zero, hprimitive, mul_smul]

/-- Every actual Kähler form has a Frobenius expansion in coordinate monomial differentials. -/
theorem squareKummer_differential_frobenius_expansion (ω : Ω) :
    ∃ a : Fin p → L, ω = ∑ i : Fin p, a i ^ p • (y ^ i.val • dy) := by
  classical
  let E : Ω ≃ₗ[L] L := squareKummerDifferentialEquiv p s c b R
  obtain ⟨a, ha⟩ := squareKummer_coordinate_power_expansion p s c b R (E ω)
  refine ⟨a, E.injective ?_⟩
  rw [map_sum]
  simp only [map_smul, squareKummerDifferentialEquiv_D_polynomial,
    derivative_X, map_one, smul_eq_mul, mul_one]
  exact ha

/-- Coefficient extraction on a Frobenius expansion retains precisely its highest coefficient. -/
theorem squareKummerCoordinateCartier_expansion (a : Fin p → L)
    (j : Fin p) (hj : j.val = p - 1) :
    squareKummerCoordinateCartier p s c b R
      (∑ i : Fin p, a i ^ p • (y ^ i.val • dy)) = a j • dy :=
  squareKummerCoordinateCartier_parameter_expansion p s c b R y a j hj

/-- The highest Frobenius coefficient is the exact obstruction to having a primitive in the function field. -/
theorem squareKummerCoordinateCartier_eq_zero_iff (ω : Ω) :
    squareKummerCoordinateCartier p s c b R ω = 0 ↔ ∃ f : L, KaehlerDifferential.D K L f = ω := by
  classical
  constructor
  · intro hω
    let j : Fin p := ⟨p - 1, Nat.sub_lt (Fact.out : p.Prime).pos Nat.zero_lt_one⟩
    obtain ⟨a, ha⟩ := squareKummer_differential_frobenius_expansion p s c b R ω
    have haj : a j = 0 := by
      rw [ha, squareKummerCoordinateCartier_expansion p s c b R a j rfl] at hω
      exact (smul_eq_zero.mp hω).resolve_right (squareKummer_coordinate_differential_ne_zero p s c b R)
    have hprimitive (i : Fin p) : ∃ f : L,
        KaehlerDifferential.D K L f = a i ^ p • (y ^ i.val • dy) := by
      by_cases hi : i = j
      · subst i
        refine ⟨0, ?_⟩
        rw [map_zero, haj, zero_pow (Fact.out : p.Prime).ne_zero, zero_smul]
      · have hilt : i.val < p - 1 := by
          have hival : i.val ≠ p - 1 := fun h => hi (Fin.ext h)
          omega
        refine ⟨(a i ^ p * algebraMap K L ((i.val + 1 : K)⁻¹)) * y ^ (i.val + 1), ?_⟩
        rw [squareKummer_frobenius_monomial_primitive p s c b R (a i) i hilt, mul_smul]
    choose f hf using hprimitive
    refine ⟨∑ i : Fin p, f i, ?_⟩
    rw [map_sum, ha]
    exact Finset.sum_congr rfl fun i _ => hf i
  · rintro ⟨f, rfl⟩
    exact squareKummerCoordinateCartier_D p s c b R f

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
