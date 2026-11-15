import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerRationalSubcover


/-!
# Generators of Kummer function fields

The polynomial coordinate generates the rational base field. Together
with the radical it generates the entire field over its constants.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open Polynomial
variable {K : Type*} [Field K] (c : Kˣ) (b R n : ℕ)

/-- A constant-field subfield containing the coordinate contains its full rational-function field. -/
theorem kummerBranchField_base_mem_of_coordinate_mem
    (S : IntermediateField K (KummerBranchField c b R n))
    (hX : algebraMap K[X] (KummerBranchField c b R n) X ∈ S) (x : FractionRing K[X]) :
    algebraMap (FractionRing K[X]) (KummerBranchField c b R n) x ∈ S := by
  let L := KummerBranchField c b R n
  have hp : ∀ f : K[X], algebraMap K[X] L f ∈ S := by
    intro f
    induction f using Polynomial.induction_on' with
    | add f g hf hg => rw [map_add]; exact S.add_mem hf hg
    | monomial i a =>
      rw [← C_mul_X_pow_eq_monomial, map_mul, map_pow]
      apply S.mul_mem _ (pow_mem hX i)
      have h := S.algebraMap_mem a
      rw [IsScalarTower.algebraMap_apply K K[X] L] at h
      exact h
  obtain ⟨f, g, _, rfl⟩ := IsFractionRing.div_surjective (A := K[X]) x
  rw [map_div₀, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  exact S.div_mem (hp f) (hp g)

/-- The original coordinate and the radical generate the entire Kummer field over its constants. -/
theorem kummerBranchField_eq_top_of_coordinate_root_mem
    (S : IntermediateField K (KummerBranchField c b R n))
    (hX : algebraMap K[X] (KummerBranchField c b R n) X ∈ S)
    (hz : AdjoinRoot.root (kummerBranchFieldPolynomial c b R n) ∈ S) : S = ⊤ := by
  apply top_unique
  intro x _
  refine AdjoinRoot.induction_on (kummerBranchFieldPolynomial c b R n) x ?_
  intro f
  induction f using Polynomial.induction_on' with
  | add f g hf hg => rw [map_add]; exact S.add_mem hf hg
  | monomial i a =>
    rw [← C_mul_X_pow_eq_monomial, map_mul, map_pow, AdjoinRoot.mk_X, AdjoinRoot.mk_C]
    exact S.mul_mem (kummerBranchField_base_mem_of_coordinate_mem c b R n S hX a)
      (pow_mem hz i)

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
