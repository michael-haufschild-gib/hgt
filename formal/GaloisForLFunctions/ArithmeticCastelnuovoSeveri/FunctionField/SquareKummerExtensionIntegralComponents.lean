import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.SquareKummerConstantExtensions
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerIntegralCharacterComponents

/-!
# Integral radical character components over enlarged constants

Primitive roots transported from the square field still diagonalize the
reduced radical basis. Character averaging therefore preserves integrality
after any extension of constants. The covering degree remains one in the
constant field, so the averaging denominator introduces no affine poles.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open Polynomial ArithmeticHarmonicAnalysis
variable (p : ℕ) [Fact p.Prime] (s : ℕ)
    (E : Type*) [Field E] [Algebra (SquareConstantField p s) E]
    (c : Eˣ) (b R : ℕ)

/-- Reduced radical monomials transform by their corresponding power character. -/
theorem squareKummerExtensionAutEquiv_integralMonomial
    (ζ : rootsOfUnity (p ^ (s + 1) + 1) E) (i : ℕ) :
    squareKummerExtensionAutEquiv p s E c b R ζ (kummerIntegralMonomial c b R (p ^ (s + 1)) i) =
      algebraMap E (SquareKummerExtensionField p s E c b R)
        (ζ : Eˣ) ^ i * kummerIntegralMonomial c b R (p ^ (s + 1)) i := by
  have hh : squareKummerExtensionAutEquiv p s E c b R ζ
      (algebraMap E[X] (SquareKummerExtensionField p s E c b R) (1 - X ^ (b + 1))) =
      algebraMap E[X] (SquareKummerExtensionField p s E c b R) (1 - X ^ (b + 1)) := by
    rw [IsScalarTower.algebraMap_apply E[X]
      (FractionRing E[X]), AlgEquiv.commutes]
  have hz := squareKummerExtensionAutEquiv_root p s E c b R ζ
  simp only [kummerIntegralMonomial, map_div₀, map_pow, hh, hz, mul_pow, mul_div_assoc]

/-- Every character component of an integral Kummer element remains integral. -/
theorem squareKummerExtension_integral_character_component
    (x : SquareKummerExtensionField p s E c b R)
    (hx : IsIntegral E[X] x)
    (i : Fin (p ^ (s + 1) + 1)) :
    IsIntegral E[X]
      ((kummerIntegralMonomialBasis c b R (p ^ (s + 1))).repr x i •
        kummerIntegralMonomialBasis c b R (p ^ (s + 1)) i) := by
  classical
  letI : CharP E p :=
    charP_of_injective_algebraMap (algebraMap (SquareConstantField p s) E).injective p
  let K := E
  let A := K[X]
  let F := FractionRing A
  let L := SquareKummerExtensionField p s E c b R
  let N := p ^ (s + 1) + 1
  let B := kummerIntegralMonomialBasis c b R (p ^ (s + 1))
  obtain ⟨ζ, hζmem⟩ := squareKummerExtension_primitiveRoots p s E
  have hζ : IsPrimitiveRoot ζ N := (mem_primitiveRoots (Nat.succ_pos _)).mp hζmem
  let ρ : rootsOfUnity N K := ⟨Units.mk0 ζ (hζ.ne_zero (Nat.succ_ne_zero _)),
    (mem_rootsOfUnity N _).mpr (Units.ext hζ.pow_eq_one)⟩
  let ζF := algebraMap K F ζ
  have hζF : IsPrimitiveRoot ζF N := hζ.map_of_injective (algebraMap K F).injective
  let σ : ℕ → (L ≃ₐ[F] L) := fun k => squareKummerExtensionAutEquiv p s E c b R (ρ ^ k)
  have heigen (k : ℕ) (j : Fin N) :
      (σ k).toLinearMap (B j) = ζF ^ (k * j.val) • B j := by
    change σ k (B j) = _
    rw [kummerIntegralMonomialBasis_apply, squareKummerExtensionAutEquiv_integralMonomial]
    change (algebraMap K L (ζ ^ k)) ^ j.val * kummerIntegralMonomial c b R (p ^ (s + 1)) j.val =
      ζF ^ (k * j.val) • kummerIntegralMonomial c b R (p ^ (s + 1)) j.val
    rw [map_pow, ← pow_mul, Algebra.smul_def, map_pow]
    rfl
  have hprojection := diagonal_primitiveRoot_projection hζF B
    (fun k => (σ k).toLinearMap) heigen x i
  have hN : (N : F) = 1 := by
    have hK : (N : K) = 1 := by
      dsimp only [N]
      rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, CharP.cast_eq_zero K p,
        zero_pow (Nat.succ_ne_zero s), zero_add]
    calc
      (N : F) = algebraMap K F (N : K) := (map_natCast (algebraMap K F) N).symm
      _ = 1 := by rw [hK, map_one]
  rw [hN, one_smul] at hprojection
  have hconstant (a : K) : IsIntegral A (algebraMap K L a) := by
    rw [IsScalarTower.algebraMap_apply K A L]
    exact isIntegral_algebraMap
  have hterm (k : ℕ) : IsIntegral A ((ζF ^ (k * i.val))⁻¹ • σ k x) := by
    have hw : (ζF ^ (k * i.val))⁻¹ • σ k x =
        algebraMap K L ((ζ ^ (k * i.val))⁻¹) * σ k x := by
      simp only [Algebra.smul_def, map_inv₀, map_pow]
      rfl
    rw [hw]
    exact (hconstant _).mul (hx.map ((σ k).restrictScalars A).toAlgHom)
  rw [← hprojection]
  exact show (∑ k ∈ Finset.range N, (ζF ^ (k * i.val))⁻¹ • σ k x) ∈ integralClosure A L from
    sum_mem fun k _ => hterm k

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
