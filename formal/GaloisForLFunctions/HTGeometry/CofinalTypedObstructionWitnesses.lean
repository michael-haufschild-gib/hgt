import GaloisForLFunctions.HTGeometry.TateFractureObstructionBianchiAmplitudeLaw

/-!
# Cofinal typed-obstruction witnesses

The constant bigraded rational module with the identity as every twisted component realizes
cofinally nonzero typed Maurer--Cartan obstructions. This is necessarily an unbounded
vertical-amplitude model, exactly as the existing no-go theorem predicts.
-/

namespace GaloisForLFunctions.HTGeometry

open CategoryTheory

/-- The constant bigraded rational module. -/
abbrev constantRationalBigradedModule : ℤ → ℤ → ModuleCat ℚ :=
  fun _ _ => ModuleCat.of ℚ ℚ

/-- Every weight acts by the identity between the definitionally equal constant bidegrees. -/
def identityRationalTwistedComponent (r : ℕ) :
    BundledTwistedComponent constantRationalBigradedModule r :=
  fun _ _ => 𝟙 _

/-- Every identity component is nonzero. -/
theorem identityRationalTwistedComponent_ne_zero (r : ℕ) :
    identityRationalTwistedComponent r ≠ 0 := by
  intro hzero
  have hhom := congrArg ModuleCat.Hom.hom (congrFun (congrFun hzero 0) 0)
  have happly := LinearMap.congr_fun hhom (1 : ℚ)
  change (1 : ℚ) = 0 at happly
  norm_num at happly

/-- The identity components themselves remain nonzero above every cutoff. -/
theorem hasCofinalNonzeroBundledTwistedComponents_identityRational :
    HasCofinalNonzeroBundledTwistedComponents constantRationalBigradedModule
      identityRationalTwistedComponent := by
  intro c
  exact ⟨c + 1, by omega, identityRationalTwistedComponent_ne_zero _⟩

/-- Every on-weight composite in the identity model sends `1` to `1`. -/
theorem identityRational_comp_apply_one
    (n r s : ℕ) (h : r + s = n) (p q : ℤ) :
    (bundledComposeTwistedComponentsAtWeight constantRationalBigradedModule n r s
      (identityRationalTwistedComponent r) (identityRationalTwistedComponent s) p q).hom
        (1 : ℚ) = 1 := by
  rw [bundledComposeTwistedComponentsAtWeight, dif_pos h]
  change (LinearMap.id (R := ℚ) (M := ℚ)) 1 = 1
  rfl

/-- **Exact all-weight law.** The weight-`n` obstruction sends `1` to the number of positive
ordered decompositions `r+s=n`. -/
theorem identityRational_typedObstruction_apply_one (n : ℕ) :
    (bundledTypedTwistedObstruction constantRationalBigradedModule
      identityRationalTwistedComponent n 0 0).hom (1 : ℚ) =
        ∑ _x ∈ (Finset.antidiagonal n).filter (fun x ↦ 1 ≤ x.1 ∧ 1 ≤ x.2),
          (1 : ℚ) := by
  rw [bundledTypedTwistedObstruction]
  let ev : BundledTwistedDegreeTwoComponent constantRationalBigradedModule n →+
      (constantRationalBigradedModule 0 0 ⟶
        constantRationalBigradedModule (n : ℤ) (2 - (n : ℤ))) := {
    toFun F := F 0 0
    map_zero' := rfl
    map_add' _ _ := rfl }
  change (ModuleCat.Hom.hom (ev (∑ x ∈ (Finset.antidiagonal n).filter
    (fun x ↦ 1 ≤ x.1 ∧ 1 ≤ x.2),
      bundledComposeTwistedComponentsAtWeight constantRationalBigradedModule n x.1 x.2
        (identityRationalTwistedComponent x.1)
        (identityRationalTwistedComponent x.2)))) (1 : ℚ) = _
  rw [map_sum, ModuleCat.hom_sum]
  let evOne : (ℚ →ₗ[ℚ] ℚ) →+ ℚ := {
    toFun F := F 1
    map_zero' := rfl
    map_add' _ _ := rfl }
  change evOne (∑ x ∈ (Finset.antidiagonal n).filter
    (fun x ↦ 1 ≤ x.1 ∧ 1 ≤ x.2),
      ModuleCat.Hom.hom (ev
        (bundledComposeTwistedComponentsAtWeight constantRationalBigradedModule n x.1 x.2
          (identityRationalTwistedComponent x.1)
          (identityRationalTwistedComponent x.2)))) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro x hx
  have hsum : x.1 + x.2 = n :=
    Finset.mem_antidiagonal.mp (Finset.mem_filter.mp hx).1
  exact identityRational_comp_apply_one n x.1 x.2 hsum 0 0

/-- Every weight at least two carries a nonzero obstruction in the identity model. -/
theorem identityRational_typedObstruction_ne_zero {n : ℕ} (hn : 2 ≤ n) :
    bundledTypedTwistedObstruction constantRationalBigradedModule
      identityRationalTwistedComponent n ≠ 0 := by
  intro hzero
  have hhom := congrArg ModuleCat.Hom.hom (congrFun (congrFun hzero 0) 0)
  have happly := LinearMap.congr_fun hhom (1 : ℚ)
  rw [identityRational_typedObstruction_apply_one] at happly
  have hmem : (1, n - 1) ∈
      (Finset.antidiagonal n).filter (fun x ↦ 1 ≤ x.1 ∧ 1 ≤ x.2) := by
    simp
    omega
  have happly0 :
      (∑ _x ∈ (Finset.antidiagonal n).filter (fun x ↦ 1 ≤ x.1 ∧ 1 ≤ x.2),
        (1 : ℚ)) = 0 := by
    calc
      _ = (ModuleCat.Hom.hom
          (0 : constantRationalBigradedModule 0 0 ⟶
            constantRationalBigradedModule (n : ℤ) (2 - (n : ℤ)))) (1 : ℚ) := happly
      _ = 0 := by rfl
  have hone : (1 : ℚ) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg
      (fun _ _ => (show (0 : ℚ) ≤ 1 by norm_num))).mp happly0 _ hmem
  norm_num at hone

/-- The identity model has nonzero typed obstructions above every cutoff. -/
theorem hasCofinalNonzeroBundledTypedObstructions_identityRational_cofinalTypedObstructionWitnesses :
    HasCofinalNonzeroBundledTypedObstructions constantRationalBigradedModule
      identityRationalTwistedComponent := by
  intro c
  refine ⟨c + 2, by omega, identityRational_typedObstruction_ne_zero (by omega)⟩

end GaloisForLFunctions.HTGeometry
