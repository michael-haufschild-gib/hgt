import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerInverseMonomialBasis
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.ValuationDifferentialTransport


/-!
# Character components of regular Kummer differentials

Relative Kummer automorphisms fix the coordinate differential. Their
inverse radical characters separate a regular differential into regular
components. Character averaging uses only constants, and the covering
degree equals one in characteristic `p`.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open Polynomial ArithmeticHarmonicAnalysis
open GaloisForLFunctions.HTGeometry
variable (p : ℕ) [Fact p.Prime] (s : ℕ) (c : (SquareConstantField p s)ˣ) (b R : ℕ)

/-- Relative automorphisms act on a coordinate form by acting on its coefficient. -/
theorem squareKummer_coordinateForm_map_aut
    (σ : SquareKummerField p s c b R ≃ₐ[FractionRing (SquareConstantField p s)[X]]
      SquareKummerField p s c b R) (f : SquareKummerField p s c b R) :
    algHomKaehlerMap (σ.restrictScalars (SquareConstantField p s)).toAlgHom
      (f • KaehlerDifferential.D (SquareConstantField p s) (SquareKummerField p s c b R)
        (algebraMap (SquareConstantField p s)[X] (SquareKummerField p s c b R) X)) =
      σ f • KaehlerDifferential.D (SquareConstantField p s) (SquareKummerField p s c b R)
        (algebraMap (SquareConstantField p s)[X] (SquareKummerField p s c b R) X) := by
  rw [algHomKaehlerMap_smul, algHomKaehlerMap_D]
  have hy : σ (algebraMap (SquareConstantField p s)[X] (SquareKummerField p s c b R) X) =
      algebraMap (SquareConstantField p s)[X] (SquareKummerField p s c b R) X := by
    rw [IsScalarTower.algebraMap_apply (SquareConstantField p s)[X]
      (FractionRing (SquareConstantField p s)[X]), σ.commutes]
  change σ f • KaehlerDifferential.D (SquareConstantField p s) (SquareKummerField p s c b R)
    (σ (algebraMap (SquareConstantField p s)[X] (SquareKummerField p s c b R) X)) = _
  rw [hy]

/-- Every inverse radical character component of a globally regular form is globally regular. -/
theorem squareKummer_regular_character_component
    (f : SquareKummerField p s c b R)
    (hf : f • KaehlerDifferential.D (SquareConstantField p s) (SquareKummerField p s c b R)
      (algebraMap (SquareConstantField p s)[X] (SquareKummerField p s c b R) X) ∈
        globalRegularDifferentials (SquareConstantField p s) (SquareKummerField p s c b R))
    (i : Fin (p ^ (s + 1) + 1)) :
    ((squareKummerInverseMonomialBasis p s c b R).repr f i •
      squareKummerInverseMonomialBasis p s c b R i) •
      KaehlerDifferential.D (SquareConstantField p s) (SquareKummerField p s c b R)
        (algebraMap (SquareConstantField p s)[X] (SquareKummerField p s c b R) X) ∈
      globalRegularDifferentials (SquareConstantField p s) (SquareKummerField p s c b R) := by
  classical
  let K := SquareConstantField p s
  let F := FractionRing K[X]
  let L := SquareKummerField p s c b R
  let N := p ^ (s + 1) + 1
  let B := squareKummerInverseMonomialBasis p s c b R
  let dy := KaehlerDifferential.D K L (algebraMap K[X] L X)
  let S := globalRegularDifferentials K L
  obtain ⟨ζ, hζmem⟩ := squareConstantField_primitiveRoots p s
  have hζ : IsPrimitiveRoot ζ N := (mem_primitiveRoots (Nat.succ_pos _)).mp hζmem
  let ρ : rootsOfUnity N K := ⟨Units.mk0 ζ (hζ.ne_zero (Nat.succ_ne_zero _)),
    (mem_rootsOfUnity N _).mpr (Units.ext hζ.pow_eq_one)⟩
  let ζF := algebraMap K F ζ
  have hζF : IsPrimitiveRoot ζF N := hζ.map_of_injective (algebraMap K F).injective
  let σ : ℕ → (L ≃ₐ[F] L) := fun k => squareKummerAutEquiv p s c b R (ρ ^ k)
  have heigen (k : ℕ) (j : Fin N) :
      (σ k).toLinearMap (B j) = (ζF⁻¹) ^ (k * j.val) • B j := by
    change σ k (B j) = _
    rw [squareKummerInverseMonomialBasis_apply, map_inv₀, squareKummerAutEquiv_integralMonomial]
    change ((algebraMap K L (ζ ^ k)) ^ j.val *
      kummerIntegralMonomial c b R (p ^ (s + 1)) j.val)⁻¹ =
      (ζF⁻¹) ^ (k * j.val) • (kummerIntegralMonomial c b R (p ^ (s + 1)) j.val)⁻¹
    rw [mul_inv_rev, map_pow, ← pow_mul, Algebra.smul_def, map_pow, map_inv₀,
      ← IsScalarTower.algebraMap_apply K F L, inv_pow]
    exact mul_comm _ _
  have hprojection := diagonal_primitiveRoot_projection hζF.inv B
    (fun k => (σ k).toLinearMap) heigen f i
  simp only [inv_pow, inv_inv] at hprojection
  have hN : (N : F) = 1 := by
    have hK : (N : K) = 1 := by
      dsimp only [N]
      rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, CharP.cast_eq_zero K p,
        zero_pow (Nat.succ_ne_zero s), zero_add]
    calc
      (N : F) = algebraMap K F (N : K) := (map_natCast (algebraMap K F) N).symm
      _ = 1 := by rw [hK, map_one]
  rw [hN, one_smul] at hprojection
  have hterm (k : ℕ) : (ζF ^ (k * i.val) • σ k f) • dy ∈ S := by
    have hσ := globalRegularDifferentials_stable_aut ((σ k).restrictScalars K) _ hf
    rw [squareKummer_coordinateForm_map_aut] at hσ
    have h := S.smul_mem (ζ ^ (k * i.val)) hσ
    change (ζF ^ (k * i.val) • σ k f) • dy ∈ S
    rw [Algebra.smul_def, mul_smul, map_pow,
      ← IsScalarTower.algebraMap_apply K F L, ← map_pow,
      IsScalarTower.algebraMap_smul]
    exact h
  change (B.repr f i • B i) • dy ∈ S
  rw [← hprojection, Finset.sum_smul]
  exact S.sum_mem fun k _ => hterm k

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
