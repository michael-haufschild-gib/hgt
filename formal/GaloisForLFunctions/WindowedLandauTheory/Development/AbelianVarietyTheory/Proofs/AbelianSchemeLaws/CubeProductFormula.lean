import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.AbelianSchemeLaws.CubeFaces
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Data.Fintype.Powerset
import Mathlib.Tactic.NormNum

/-! Evaluation of the eight alternating cube factors on three points. -/

noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj
open scoped BigOperators CategoryTheory.Obj

namespace GlobalTheory.AbLaw.Cube

attribute [local instance] Over.cartesianMonoidalCategory

private theorem prod_subsets_three {U : Type*} [CommMonoid U] (F : Finset (Fin 3) → U) :
    ∏ I, F I = (F ∅ * F {2}) * (F {1} * F {1, 2}) *
      ((F {0} * F {0, 2}) * (F {0, 1} * F {0, 1, 2})) := by
  have h : (Finset.univ : Finset (Fin 3)) = {0, 1, 2} := by
    ext i
    fin_cases i <;> simp
  rw [← Finset.powerset_univ, h]
  have h₀ : 0 ∉ ({1, 2} : Finset (Fin 3)) := by simp
  have h₁ : 1 ∉ ({2} : Finset (Fin 3)) := by simp
  have h₂ (G : Finset (Fin 3) → U) :
      ∏ I ∈ ({2} : Finset (Fin 3)).powerset, G I = G ∅ * G {2} := by
    simpa only [Finset.powerset_empty, Finset.prod_singleton, Finset.insert_empty] using
      Finset.prod_powerset_insert (Finset.notMem_empty (2 : Fin 3)) G
  simp only [Finset.prod_powerset_insert h₀, Finset.prod_powerset_insert h₁, h₂,
    Finset.insert_empty]

variable {S : Scheme.{0}} {A T : Over S} [GrpObj A] [IsCommMonObj A]

private theorem lift_comp_cubeMorphism (x y z : T ⟶ A) (I : Finset (Fin 3)) :
    (lift x (lift y z)).left ≫ cubeMorphism A I =
      (∏ i ∈ I, (![x, y, z] : Fin 3 → (T ⟶ A)) i).left := by
  let d := lift x (lift y z)
  let E : (A ⊗ (A ⊗ A) ⟶ A) →* (T ⟶ A) :=
    { toFun := fun g => d ≫ g
      map_one' := MonObj.comp_one d
      map_mul' := MonObj.comp_mul d }
  have h (i : Fin 3) : E (cubeProjection A i) = (![x, y, z] : Fin 3 → (T ⟶ A)) i := by
    fin_cases i <;> simp [E, d, cubeProjection]
  change (E (∏ i ∈ I, cubeProjection A i)).left = _
  exact congrArg Over.Hom.left ((map_prod E _ I).trans (Finset.prod_congr rfl (fun i _ => h i)))

/-- The cube product evaluated on a triple is the product of the triple and singleton
factors divided by the pair and identity factors. -/
theorem prod_cube (x y z : T ⟶ A) {U : Type} [CommGroup U] (k : (T.left ⟶ A.left) → U) :
    ∏ I, k ((lift x (lift y z)).left ≫ cubeMorphism A I) ^ cubeExponent I =
      k (x * y * z).left * (k (x * y).left)⁻¹ * (k (x * z).left)⁻¹ * (k (y * z).left)⁻¹ *
        k x.left * k y.left * k z.left * (k (1 : T ⟶ A).left)⁻¹ := by
  rw [prod_subsets_three]
  have h₀ : 0 ∉ ({1, 2} : Finset (Fin 3)) := by simp
  have h₁ : 0 ∉ ({1} : Finset (Fin 3)) := by simp
  have h₂ : 0 ∉ ({2} : Finset (Fin 3)) := by simp
  have h₃ : 1 ∉ ({2} : Finset (Fin 3)) := by simp
  simp only [lift_comp_cubeMorphism, cubeExponent, Finset.card_empty, Finset.card_singleton,
    Finset.card_insert_of_notMem h₀, Finset.card_insert_of_notMem h₁,
    Finset.card_insert_of_notMem h₂, Finset.card_insert_of_notMem h₃,
    Finset.prod_empty, Finset.prod_singleton,
    Finset.prod_insert h₀, Finset.prod_insert h₁, Finset.prod_insert h₂, Finset.prod_insert h₃,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  norm_num only [zpow_neg_one, zpow_one, zpow_zero, pow_succ, pow_zero]
  rw [← _root_.mul_assoc x y z]
  ac_rfl

end GlobalTheory.AbLaw.Cube
