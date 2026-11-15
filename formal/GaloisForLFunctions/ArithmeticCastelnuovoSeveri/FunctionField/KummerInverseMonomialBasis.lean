import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerIntegralCharacterComponents
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# An inverse radical basis

The inverses of reduced radical monomials have distinct inverse characters
under a primitive Kummer automorphism. They are therefore linearly
independent; their number equals the extension degree, so they form a
basis over the rational-function field.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open Polynomial
variable (p : ℕ) [Fact p.Prime] (s : ℕ) (c : (SquareConstantField p s)ˣ) (b R : ℕ)

/-- The inverse reduced radical monomials are linearly independent over the rational base field. -/
theorem squareKummer_inverseMonomials_linearIndependent :
    LinearIndependent (FractionRing (SquareConstantField p s)[X])
      (fun i : Fin (p ^ (s + 1) + 1) =>
        (kummerIntegralMonomial c b R (p ^ (s + 1)) i.val)⁻¹) := by
  let K := SquareConstantField p s
  let F := FractionRing K[X]
  let L := SquareKummerField p s c b R
  let N := p ^ (s + 1) + 1
  obtain ⟨ζ, hζmem⟩ := squareConstantField_primitiveRoots p s
  have hζ : IsPrimitiveRoot ζ N := (mem_primitiveRoots (Nat.succ_pos _)).mp hζmem
  let ρ : rootsOfUnity N K := ⟨Units.mk0 ζ (hζ.ne_zero (Nat.succ_ne_zero _)),
    (mem_rootsOfUnity N _).mpr (Units.ext hζ.pow_eq_one)⟩
  let ζF := algebraMap K F ζ
  have hζF : IsPrimitiveRoot ζF N := hζ.map_of_injective (algebraMap K F).injective
  let σ := squareKummerAutEquiv p s c b R ρ
  let μ : Fin N → F := fun i => (ζF ^ i.val)⁻¹
  have hμ : Function.Injective μ := by
    intro i j h
    exact Fin.ext (hζF.pow_inj i.isLt j.isLt (inv_injective h))
  apply Module.End.eigenvectors_linearIndependent' σ.toLinearMap μ hμ
  intro i
  refine ⟨Module.End.mem_eigenspace_iff.mpr ?_, ?_⟩
  · change σ ((kummerIntegralMonomial c b R (p ^ (s + 1)) i.val)⁻¹) =
      μ i • (kummerIntegralMonomial c b R (p ^ (s + 1)) i.val)⁻¹
    rw [map_inv₀, squareKummerAutEquiv_integralMonomial, Algebra.smul_def]
    change (algebraMap K L ζ ^ i.val * kummerIntegralMonomial c b R (p ^ (s + 1)) i.val)⁻¹ =
      algebraMap F L ((algebraMap K F ζ ^ i.val)⁻¹) *
        (kummerIntegralMonomial c b R (p ^ (s + 1)) i.val)⁻¹
    rw [mul_inv_rev, map_inv₀, map_pow, ← IsScalarTower.algebraMap_apply K F L, mul_comm]
  · apply inv_ne_zero
    simpa only [kummerIntegralMonomialBasis_apply] using
      (kummerIntegralMonomialBasis c b R (p ^ (s + 1))).ne_zero i

/-- The inverse reduced radical monomials form a rational-function basis of the Kummer field. -/
def squareKummerInverseMonomialBasis :
    Module.Basis (Fin (p ^ (s + 1) + 1)) (FractionRing (SquareConstantField p s)[X])
      (SquareKummerField p s c b R) :=
  basisOfLinearIndependentOfCardEqFinrank
    (squareKummer_inverseMonomials_linearIndependent p s c b R)
    (by rw [Fintype.card_fin, kummerBranchField_finrank])

/-- The inverse basis vectors are the literal reciprocals of the reduced radical monomials. -/
theorem squareKummerInverseMonomialBasis_apply (i : Fin (p ^ (s + 1) + 1)) :
    squareKummerInverseMonomialBasis p s c b R i =
      (kummerIntegralMonomial c b R (p ^ (s + 1)) i.val)⁻¹ := by
  rw [squareKummerInverseMonomialBasis, coe_basisOfLinearIndependentOfCardEqFinrank]

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
