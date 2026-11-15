import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerThreePointCoordinate
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerFieldGenerators


/-!
# Isomorphism with the three-point model

The equation `z^N=c y(1-y^m)^R` has the same function field as
`z^(Nm)=c^m t(1-t)^(Rm)`. A map of radical fields and rational recovery
of `y` prove the constant-field isomorphism.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open Polynomial
open GaloisForLFunctions.HTGeometry
variable {K : Type*} [Field K] (c : Kˣ) (b R n : ℕ)

/-- The radical model with branch support contained in `0`, `1`, and infinity. -/
abbrev KummerThreePointField :=
  KummerBranchField (c ^ (b + 1)) 0 (R * (b + 1)) ((n + 1) * (b + 1) - 1)

private theorem threePoint_polynomial_eval :
    (kummerBranchFieldPolynomial (c ^ (b + 1)) 0 (R * (b + 1)) ((n + 1) * (b + 1) - 1)).eval₂
      (fracRealize (kummerMonomialCoordinate_transcendental c b R n))
      (AdjoinRoot.root (kummerBranchFieldPolynomial c b R n)) = 0 := by
  have hM : (n + 1) * (b + 1) - 1 + 1 = (n + 1) * (b + 1) :=
    Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (Nat.succ_ne_zero _) (Nat.succ_ne_zero _)))
  change (X ^ ((n + 1) * (b + 1) - 1 + 1) -
    C (algebraMap K[X] (FractionRing K[X]) (kummerBranch (c ^ (b + 1)) 0 (R * (b + 1))))).eval₂
      (fracRealize (kummerMonomialCoordinate_transcendental c b R n))
      (AdjoinRoot.root (kummerBranchFieldPolynomial c b R n)) = 0
  rw [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C, hM]
  change AdjoinRoot.root (kummerBranchFieldPolynomial c b R n) ^ ((n + 1) * (b + 1)) -
    fracRealize (kummerMonomialCoordinate_transcendental c b R n)
      (algebraMap K[X] (FractionRing K[X]) (kummerBranch (c ^ (b + 1)) 0 (R * (b + 1)))) = 0
  rw [fracRealize_algebraMap, kummerBranch]
  simp only [map_mul, map_pow, map_sub, map_one, aeval_C, aeval_X, Nat.zero_add,
    pow_one, Units.val_pow_eq_pow_val]
  exact sub_eq_zero.mpr (by
    simpa only [map_pow] using kummerBranchField_threePoint_equation c b R n)

/-- The three-point model maps into the original field by `t=y^(b+1)` and the same radical. -/
def kummerThreePointHom : KummerThreePointField c b R n →ₐ[K] KummerBranchField c b R n :=
  AdjoinRoot.liftAlgHom _ (fracRealize (kummerMonomialCoordinate_transcendental c b R n))
    (AdjoinRoot.root (kummerBranchFieldPolynomial c b R n)) (threePoint_polynomial_eval c b R n)

/-- The coordinate of the three-point model is the power of the original coordinate. -/
theorem kummerThreePointHom_coordinate :
    kummerThreePointHom c b R n (algebraMap K[X] (KummerThreePointField c b R n) X) =
      kummerMonomialCoordinate c b R n := by
  rw [IsScalarTower.algebraMap_apply K[X] (FractionRing K[X]), AdjoinRoot.algebraMap_eq,
    kummerThreePointHom, AdjoinRoot.liftAlgHom_of, fracRealize_algebraMap, aeval_X]

/-- The three-point change of model preserves the radical. -/
theorem kummerThreePointHom_root :
    kummerThreePointHom c b R n
      (AdjoinRoot.root (kummerBranchFieldPolynomial (c ^ (b + 1)) 0
        (R * (b + 1)) ((n + 1) * (b + 1) - 1))) =
      AdjoinRoot.root (kummerBranchFieldPolynomial c b R n) := by
  exact AdjoinRoot.liftAlgHom_root _ _ _ _

/-- Rational recovery of the old coordinate makes the change of model surjective. -/
theorem kummerThreePointHom_surjective : Function.Surjective (kummerThreePointHom c b R n) := by
  let f := kummerThreePointHom c b R n
  have hz : AdjoinRoot.root (kummerBranchFieldPolynomial c b R n) ∈ f.fieldRange :=
    ⟨_, kummerThreePointHom_root c b R n⟩
  have ht : kummerMonomialCoordinate c b R n ∈ f.fieldRange :=
    ⟨_, kummerThreePointHom_coordinate c b R n⟩
  have hy : algebraMap K[X] (KummerBranchField c b R n) X ∈ f.fieldRange := by
    rw [kummerBranchField_coordinate_recover]
    exact f.fieldRange.div_mem (pow_mem hz (n + 1)) (f.fieldRange.mul_mem
      (f.fieldRange.algebraMap_mem _) (pow_mem (f.fieldRange.sub_mem f.fieldRange.one_mem ht) R))
  have htop := kummerBranchField_eq_top_of_coordinate_root_mem c b R n f.fieldRange hy hz
  intro x
  have hx : x ∈ f.fieldRange := by rw [htop]; trivial
  exact hx

/-- Every model `z^N=c y(1-y^m)^R` is isomorphic over constants to the three-point model
`z^(Nm)=c^m t(1-t)^(Rm)`. -/
def kummerThreePointEquiv : KummerThreePointField c b R n ≃ₐ[K] KummerBranchField c b R n :=
  AlgEquiv.ofBijective (kummerThreePointHom c b R n)
    ⟨(kummerThreePointHom c b R n).injective, kummerThreePointHom_surjective c b R n⟩

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
