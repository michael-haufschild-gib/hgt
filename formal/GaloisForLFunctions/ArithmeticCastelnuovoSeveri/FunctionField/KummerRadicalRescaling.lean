import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerFieldGenerators

/-!
# Rescaling radical coefficients

Multiplication of the defining coefficient by an `N`th power is absorbed
by multiplying the radical by its root. The resulting field isomorphism
fixes the polynomial coordinate and every constant.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open Polynomial
variable {K : Type*} [Field K] (c ξ : Kˣ) (b R n : ℕ)

/-- Multiplying the coefficient by an `N`th power rescales the branch polynomial by that power. -/
theorem kummerBranch_rescale :
    kummerBranch (c * ξ ^ (n + 1)) b R =
      C (ξ : K) ^ (n + 1) * kummerBranch c b R := by
  simp only [kummerBranch, Units.val_mul, Units.val_pow_eq_pow_val, map_mul, map_pow]
  ring

private theorem kummerRadicalRescaling_eval :
    (kummerBranchFieldPolynomial (c * ξ ^ (n + 1)) b R n).eval₂
      (IsScalarTower.toAlgHom K (FractionRing K[X]) (KummerBranchField c b R n))
      (algebraMap K (KummerBranchField c b R n) (ξ : K) *
        AdjoinRoot.root (kummerBranchFieldPolynomial c b R n)) = 0 := by
  change (X ^ (n + 1) - C (algebraMap K[X] (FractionRing K[X])
      (kummerBranch (c * ξ ^ (n + 1)) b R))).eval₂
    (IsScalarTower.toAlgHom K (FractionRing K[X]) (KummerBranchField c b R n))
    (algebraMap K (KummerBranchField c b R n) (ξ : K) *
      AdjoinRoot.root (kummerBranchFieldPolynomial c b R n)) = 0
  rw [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C, sub_eq_zero,
    mul_pow, kummerBranchField_root_pow]
  change algebraMap K (KummerBranchField c b R n) (ξ : K) ^ (n + 1) *
      algebraMap (FractionRing K[X]) (KummerBranchField c b R n)
        (algebraMap K[X] (FractionRing K[X]) (kummerBranch c b R)) =
    algebraMap (FractionRing K[X]) (KummerBranchField c b R n)
      (algebraMap K[X] (FractionRing K[X]) (kummerBranch (c * ξ ^ (n + 1)) b R))
  rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply,
    kummerBranch_rescale, map_mul, map_pow]
  have hξ : algebraMap K[X] (KummerBranchField c b R n) (C (ξ : K)) =
      algebraMap K (KummerBranchField c b R n) (ξ : K) :=
    (IsScalarTower.algebraMap_apply K K[X] (KummerBranchField c b R n) (ξ : K)).symm
  rw [hξ]

/-- Rescaling the radical gives a homomorphism from the correspondingly rescaled coefficient model. -/
def kummerRadicalRescalingHom :
    KummerBranchField (c * ξ ^ (n + 1)) b R n →ₐ[K] KummerBranchField c b R n :=
  AdjoinRoot.liftAlgHom _ (IsScalarTower.toAlgHom K (FractionRing K[X]) _)
    (algebraMap K (KummerBranchField c b R n) (ξ : K) *
      AdjoinRoot.root (kummerBranchFieldPolynomial c b R n))
    (kummerRadicalRescaling_eval c ξ b R n)

/-- Radical rescaling fixes the original rational coordinate. -/
theorem kummerRadicalRescalingHom_coordinate :
    kummerRadicalRescalingHom c ξ b R n
      (algebraMap K[X] (KummerBranchField (c * ξ ^ (n + 1)) b R n) X) =
        algebraMap K[X] (KummerBranchField c b R n) X := by
  rw [IsScalarTower.algebraMap_apply K[X] (FractionRing K[X]), AdjoinRoot.algebraMap_eq,
    kummerRadicalRescalingHom, AdjoinRoot.liftAlgHom_of]
  exact (IsScalarTower.algebraMap_apply K[X] (FractionRing K[X]) _ X).symm

/-- The named radical is multiplied by the chosen nonzero constant. -/
theorem kummerRadicalRescalingHom_root :
    kummerRadicalRescalingHom c ξ b R n
      (AdjoinRoot.root (kummerBranchFieldPolynomial (c * ξ ^ (n + 1)) b R n)) =
        algebraMap K (KummerBranchField c b R n) (ξ : K) *
          AdjoinRoot.root (kummerBranchFieldPolynomial c b R n) :=
  AdjoinRoot.liftAlgHom_root _ _ _ _

/-- The coordinate and radical can both be recovered after rescaling. -/
theorem kummerRadicalRescalingHom_surjective :
    Function.Surjective (kummerRadicalRescalingHom c ξ b R n) := by
  let f := kummerRadicalRescalingHom c ξ b R n
  have hy : algebraMap K[X] (KummerBranchField c b R n) X ∈ f.fieldRange :=
    ⟨_, kummerRadicalRescalingHom_coordinate c ξ b R n⟩
  have hz : AdjoinRoot.root (kummerBranchFieldPolynomial c b R n) ∈ f.fieldRange := by
    have h := f.fieldRange.mul_mem (f.fieldRange.algebraMap_mem (ξ : K)⁻¹)
      (show f (AdjoinRoot.root (kummerBranchFieldPolynomial (c * ξ ^ (n + 1)) b R n)) ∈ f.fieldRange
        from ⟨_, rfl⟩)
    change algebraMap K (KummerBranchField c b R n) (ξ : K)⁻¹ *
      kummerRadicalRescalingHom c ξ b R n
        (AdjoinRoot.root (kummerBranchFieldPolynomial (c * ξ ^ (n + 1)) b R n)) ∈ f.fieldRange at h
    rw [kummerRadicalRescalingHom_root, ← mul_assoc, ← map_mul,
      inv_mul_cancel₀ ξ.ne_zero, map_one, one_mul] at h
    exact h
  have htop := kummerBranchField_eq_top_of_coordinate_root_mem c b R n f.fieldRange hy hz
  intro x
  have hx : x ∈ f.fieldRange := by rw [htop]; trivial
  exact hx

/-- Coefficients differing by an `N`th power define isomorphic Kummer fields over the constants. -/
def kummerRadicalRescalingEquiv :
    KummerBranchField (c * ξ ^ (n + 1)) b R n ≃ₐ[K] KummerBranchField c b R n :=
  AlgEquiv.ofBijective (kummerRadicalRescalingHom c ξ b R n)
    ⟨(kummerRadicalRescalingHom c ξ b R n).injective,
      kummerRadicalRescalingHom_surjective c ξ b R n⟩

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
