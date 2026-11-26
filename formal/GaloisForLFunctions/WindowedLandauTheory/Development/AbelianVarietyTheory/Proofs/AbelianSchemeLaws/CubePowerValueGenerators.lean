import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.AbelianSchemeLaws.CubicalProducts
import Mathlib.Tactic.Module

/-! Successive cube pullbacks telescope to eight factors and retain their cubical product values. -/

open AlgebraicGeometry CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory.AbLaw.Cube

attribute [local instance] Over.cartesianMonoidalCategory

variable {S : Scheme.{0}} {A T : Over S} [GrpObj A] [IsCommMonObj A] {L : LB A.left}

/-- The remaining morphisms after multiplying n successive cube factors. -/
noncomputable def cubePowerFactors (a m x : T ⟶ A) (n : ℕ) : Fin 8 → (T.left ⟶ A.left) :=
  ![(a * m ^ n * x).left, (a * m ^ n).left, (a * x).left, a.left,
    (m * x).left, m.left, x.left, (1 : T ⟶ A).left]

/-- Multiplicities of the remaining cube factors. -/
def cubePowerExponents (n : ℕ) : Fin 8 → ℤ :=
  ![1, -1, -1, 1, -(n : ℤ), (n : ℤ), (n : ℤ), -(n : ℤ)]

/-- The telescoped cube product has a generator with the prescribed product of values. -/
theorem exists_cube_power_generator (hL : L.IsLB) {s : (cubeBundle A L).Gen} (hs : s.IsGen)
    (a m x : T ⟶ A) (n : ℕ) :
    ∃ t : (LB.LinComb L (cubePowerFactors a m x n) (cubePowerExponents n)).Gen, t.IsGen ∧
      ∀ (T' : Over S) (r : T' ⟶ T) (z : T'.left) (J : (T'.left ⟶ A.left) → L.ι),
        Good L z J → val t r.left z J =
          cubicalProduct (fun b d e => cubeValue s b d e z J) n (r ≫ a) (r ≫ m) (r ≫ x) := by
  induction n with
  | zero =>
    obtain ⟨t, ht, hv⟩ := exists_gen_of_cancellation L hL (cubePowerFactors a m x 0)
      (cubePowerExponents 0) (fun U _ k => by
        simp [cubePowerFactors, cubePowerExponents, Fin.prod_univ_succ])
    exact ⟨t, ht, fun T' r z J hJ => (hv T'.left r.left z J hJ).trans (by simp [cubicalProduct])⟩
  | succ n ih =>
    obtain ⟨t, ht, hv⟩ := ih
    have hform : FormEq (Sum.elim (cubePowerFactors a m x n) (cubeFactors (a * m ^ n) m x))
        (Sum.elim (cubePowerExponents n) cubeExponent)
        (cubePowerFactors a m x (n + 1)) (cubePowerExponents (n + 1)) := by
      intro U _ k
      rw [Fintype.prod_sum_type]
      simp only [Sum.elim_inl, Sum.elim_inr, cubeFactors, prod_cube, cubePowerFactors, cubePowerExponents]
      rw [pow_succ m, ← _root_.mul_assoc a]
      apply Additive.ofMul.injective
      simp [Fin.prod_univ_succ, ofMul_mul, ofMul_inv, ofMul_zpow]
      module
    obtain ⟨u, hu, hv'⟩ := exists_gen_of_formEq hL hform _
      (mulGen_isGen ht (cubePull_isGen hs (a * m ^ n) m x))
    refine ⟨u, hu, fun T' r z J hJ => ?_⟩
    rw [hv' T'.left r.left z J hJ, val_mul hJ, hv T' r z J hJ, cubePull_value s _ _ _ r z J hJ,
      MonObj.comp_mul r a (m ^ n), MonObj.comp_pow m n r]
    exact (Finset.prod_range_succ _ _).symm

end GlobalTheory.AbLaw.Cube
