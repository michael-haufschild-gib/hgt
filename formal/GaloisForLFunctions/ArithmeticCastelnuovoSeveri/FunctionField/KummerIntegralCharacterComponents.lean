import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerIntegralMonomialBasis
import GaloisForLFunctions.ArithmeticHarmonicAnalysis.FiniteGroup.PrimitiveRootProjectors
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FiniteField.KummerTraceConstants

/-!
# Integral character components of a Kummer element

Reduced radical monomials diagonalize the roots-of-unity action. Character
averaging isolates each basis component of an integral element. All
weights are constants, and the covering degree equals one in the
constant field, so every isolated component remains integral.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open Polynomial ArithmeticHarmonicAnalysis
variable (p : ℕ) [Fact p.Prime] (s : ℕ) (c : (SquareConstantField p s)ˣ) (b R : ℕ)

/-- Reduced radical monomials transform by their corresponding power character. -/
theorem squareKummerAutEquiv_integralMonomial
    (ζ : rootsOfUnity (p ^ (s + 1) + 1) (SquareConstantField p s)) (i : ℕ) :
    squareKummerAutEquiv p s c b R ζ (kummerIntegralMonomial c b R (p ^ (s + 1)) i) =
      algebraMap (SquareConstantField p s) (SquareKummerField p s c b R)
        (ζ : (SquareConstantField p s)ˣ) ^ i * kummerIntegralMonomial c b R (p ^ (s + 1)) i := by
  have hh : squareKummerAutEquiv p s c b R ζ
      (algebraMap (SquareConstantField p s)[X] (SquareKummerField p s c b R) (1 - X ^ (b + 1))) =
      algebraMap (SquareConstantField p s)[X] (SquareKummerField p s c b R) (1 - X ^ (b + 1)) := by
    rw [IsScalarTower.algebraMap_apply (SquareConstantField p s)[X]
      (FractionRing (SquareConstantField p s)[X]), AlgEquiv.commutes]
  have hz := squareKummerAutEquiv_root p s c b R ζ
  rw [← IsScalarTower.algebraMap_apply (SquareConstantField p s)
    (FractionRing (SquareConstantField p s)[X]) (SquareKummerField p s c b R)] at hz
  simp only [kummerIntegralMonomial, map_div₀, map_pow, hh, hz, mul_pow, mul_div_assoc]

/-- Every character component of an integral Kummer element remains integral. -/
theorem squareKummer_integral_character_component
    (x : SquareKummerField p s c b R)
    (hx : IsIntegral (SquareConstantField p s)[X] x)
    (i : Fin (p ^ (s + 1) + 1)) :
    IsIntegral (SquareConstantField p s)[X]
      ((kummerIntegralMonomialBasis c b R (p ^ (s + 1))).repr x i •
        kummerIntegralMonomialBasis c b R (p ^ (s + 1)) i) := by
  classical
  let K := SquareConstantField p s
  let A := K[X]
  let F := FractionRing A
  let L := SquareKummerField p s c b R
  let N := p ^ (s + 1) + 1
  let B := kummerIntegralMonomialBasis c b R (p ^ (s + 1))
  obtain ⟨ζ, hζmem⟩ := squareConstantField_primitiveRoots p s
  have hζ : IsPrimitiveRoot ζ N := (mem_primitiveRoots (Nat.succ_pos _)).mp hζmem
  let ρ : rootsOfUnity N K := ⟨Units.mk0 ζ (hζ.ne_zero (Nat.succ_ne_zero _)),
    (mem_rootsOfUnity N _).mpr (Units.ext hζ.pow_eq_one)⟩
  let ζF := algebraMap K F ζ
  have hζF : IsPrimitiveRoot ζF N := hζ.map_of_injective (algebraMap K F).injective
  let σ : ℕ → (L ≃ₐ[F] L) := fun k => squareKummerAutEquiv p s c b R (ρ ^ k)
  have heigen (k : ℕ) (j : Fin N) :
      (σ k).toLinearMap (B j) = ζF ^ (k * j.val) • B j := by
    change σ k (B j) = _
    rw [kummerIntegralMonomialBasis_apply, squareKummerAutEquiv_integralMonomial]
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
