import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerThreePointCoordinate
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerFieldGenerators

/-!
# Removing a branch exponent dividing the covering degree

The models
`z^(AR)=ξ^R y(1-y^m)^R` and `z^A=ξ u(1-u^(mR))`
have the same constant-field function field. The map sends `y` to
`u^R` and preserves `z`; rational recovery
`u=z^A/(ξ(1-y^m))` proves surjectivity.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open Polynomial
open GaloisForLFunctions.HTGeometry
variable {K : Type*} [Field K] (ξ : Kˣ) (b r a : ℕ)
local notation "S" => KummerBranchField (ξ ^ (r + 1)) b (r + 1) ((a + 1) * (r + 1) - 1)
local notation "T" => KummerBranchField ξ ((b + 1) * (r + 1) - 1) 1 a
local notation "u" => algebraMap K[X] T X
local notation "z" => AdjoinRoot.root (kummerBranchFieldPolynomial ξ ((b + 1) * (r + 1) - 1) 1 a)

private theorem divisor_cover_index :
    (a + 1) * (r + 1) - 1 + 1 = (a + 1) * (r + 1) :=
  Nat.sub_add_cancel (Nat.mul_pos (Nat.succ_pos a) (Nat.succ_pos r))

private theorem divisor_branch_index :
    (b + 1) * (r + 1) - 1 + 1 = (b + 1) * (r + 1) :=
  Nat.sub_add_cancel (Nat.mul_pos (Nat.succ_pos b) (Nat.succ_pos r))

private theorem divisor_parameter_transcendental : Transcendental K (u ^ (r + 1)) := by
  intro h
  apply kummerBranchField_coordinate_transcendental ξ ((b + 1) * (r + 1) - 1) 1 a
  exact (IsIntegral.of_pow (Nat.succ_pos r) h.isIntegral).isAlgebraic

private theorem divisor_root_equation :
    z ^ (a + 1) = algebraMap K T ξ * u * (1 - u ^ ((b + 1) * (r + 1))) := by
  have h := kummerBranchField_root_pow ξ ((b + 1) * (r + 1) - 1) 1 a
  rw [← IsScalarTower.algebraMap_apply, kummerBranch, map_mul, map_mul,
    map_pow, map_sub, map_one, map_pow] at h
  have hc : algebraMap K[X] T (C (ξ : K)) = algebraMap K T ξ :=
    (IsScalarTower.algebraMap_apply K K[X] T ξ).symm
  rw [hc, divisor_branch_index, pow_one] at h
  exact h

private theorem divisor_parameter_power :
    (u ^ (r + 1)) ^ (b + 1) = u ^ ((b + 1) * (r + 1)) :=
  (pow_mul u (r + 1) (b + 1)).symm.trans
    (congrArg (fun j : ℕ => u ^ j) (Nat.mul_comm (r + 1) (b + 1)))

private theorem divisor_power_equation :
    z ^ ((a + 1) * (r + 1)) =
      algebraMap K T ((ξ : K) ^ (r + 1)) * u ^ (r + 1) *
        (1 - (u ^ (r + 1)) ^ (b + 1)) ^ (r + 1) := by
  calc
    z ^ ((a + 1) * (r + 1)) = (z ^ (a + 1)) ^ (r + 1) := pow_mul z _ _
    _ = (algebraMap K T ξ * u * (1 - u ^ ((b + 1) * (r + 1)))) ^ (r + 1) := by
      rw [divisor_root_equation]
    _ = _ := by rw [divisor_parameter_power, mul_pow, mul_pow, map_pow]

private theorem divisor_polynomial_eval :
    (kummerBranchFieldPolynomial (ξ ^ (r + 1)) b (r + 1) ((a + 1) * (r + 1) - 1)).eval₂
      (fracRealize (divisor_parameter_transcendental ξ b r a)) z = 0 := by
  change (X ^ ((a + 1) * (r + 1) - 1 + 1) -
    C (algebraMap K[X] (FractionRing K[X]) (kummerBranch (ξ ^ (r + 1)) b (r + 1)))).eval₂
      (fracRealize (divisor_parameter_transcendental ξ b r a)) z = 0
  rw [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C, divisor_cover_index]
  change z ^ ((a + 1) * (r + 1)) -
    fracRealize (divisor_parameter_transcendental ξ b r a)
      (algebraMap K[X] (FractionRing K[X]) (kummerBranch (ξ ^ (r + 1)) b (r + 1))) = 0
  rw [fracRealize_algebraMap, kummerBranch]
  simp only [map_mul, map_pow, map_sub, map_one, aeval_C, aeval_X,
    Units.val_pow_eq_pow_val]
  exact sub_eq_zero.mpr (by simpa only [map_pow] using divisor_power_equation ξ b r a)

/-- Raising the new rational coordinate to the branch exponent and preserving the radical defines the change of model. -/
def kummerDivisorExponentHom : S →ₐ[K] T :=
  AdjoinRoot.liftAlgHom _ (fracRealize (divisor_parameter_transcendental ξ b r a)) z
    (divisor_polynomial_eval ξ b r a)

/-- The old rational coordinate becomes the prescribed power of the new coordinate. -/
theorem kummerDivisorExponentHom_coordinate :
    kummerDivisorExponentHom ξ b r a (algebraMap K[X] S X) = u ^ (r + 1) := by
  rw [IsScalarTower.algebraMap_apply K[X] (FractionRing K[X]), AdjoinRoot.algebraMap_eq,
    kummerDivisorExponentHom, AdjoinRoot.liftAlgHom_of, fracRealize_algebraMap, aeval_X]

/-- The change of model preserves the radical generator. -/
theorem kummerDivisorExponentHom_root :
    kummerDivisorExponentHom ξ b r a
      (AdjoinRoot.root (kummerBranchFieldPolynomial (ξ ^ (r + 1)) b (r + 1)
        ((a + 1) * (r + 1) - 1))) = z :=
  AdjoinRoot.liftAlgHom_root _ _ _ _

/-- The new coordinate is recovered rationally from the old coordinate and radical. -/
theorem kummerDivisorExponentHom_surjective : Function.Surjective (kummerDivisorExponentHom ξ b r a) := by
  let f := kummerDivisorExponentHom ξ b r a
  have hz : z ∈ f.fieldRange := ⟨_, kummerDivisorExponentHom_root ξ b r a⟩
  have hy : u ^ (r + 1) ∈ f.fieldRange := ⟨_, kummerDivisorExponentHom_coordinate ξ b r a⟩
  have ht : kummerMonomialCoordinate ξ ((b + 1) * (r + 1) - 1) 1 a ∈ f.fieldRange := by
    change u ^ ((b + 1) * (r + 1) - 1 + 1) ∈ f.fieldRange
    rw [divisor_branch_index, ← divisor_parameter_power]
    exact pow_mem hy (b + 1)
  have hu : u ∈ f.fieldRange := by
    rw [kummerBranchField_coordinate_recover ξ ((b + 1) * (r + 1) - 1) 1 a]
    exact f.fieldRange.div_mem (pow_mem hz (a + 1)) (f.fieldRange.mul_mem
      (f.fieldRange.algebraMap_mem _) (pow_mem (f.fieldRange.sub_mem f.fieldRange.one_mem ht) 1))
  have htop := kummerBranchField_eq_top_of_coordinate_root_mem ξ
    ((b + 1) * (r + 1) - 1) 1 a f.fieldRange hu hz
  intro x
  have hx : x ∈ f.fieldRange := by rw [htop]; trivial
  exact hx

/-- A branch exponent dividing the covering degree can be replaced by one, with the covering degree divided by that exponent. -/
def kummerDivisorExponentEquiv : S ≃ₐ[K] T :=
  AlgEquiv.ofBijective (kummerDivisorExponentHom ξ b r a)
    ⟨(kummerDivisorExponentHom ξ b r a).injective, kummerDivisorExponentHom_surjective ξ b r a⟩

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
