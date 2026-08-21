import GaloisForLFunctions.HTGeometry.PolynomialPlaceResidue

namespace GaloisForLFunctions.HTGeometry

universe u

variable (F : Type u) [Field F]

/-- Specialization at `X`, with its residue field identified with `F`. -/
noncomputable def milnorPolynomialXSpecialization (n : ℕ) :
    MilnorKDeg (RatFunc F) n →+ MilnorKDeg F n :=
  (milnorKDegMap (polyPlaceXResidueEquiv (F := F)).toRingHom n).comp
    (milnorSpecialization (residueDataAtPlace (RatFunc F)
      (polyPlace (Polynomial.irreducible_X (R := F)))) n)

/-- The map on Milnor `K`-groups induced by the constant embedding `F → F(t)`. -/
noncomputable def milnorPolynomialConstantMap (n : ℕ) :
    MilnorKDeg F n →+ MilnorKDeg (RatFunc F) n :=
  milnorKDegMap (ratFuncConstHom (F := F)) n

/-- Specialization at `X` is a left inverse to the constant embedding. -/
theorem milnorPolynomialXSpecialization_constant_apply (n : ℕ) (x : MilnorKDeg F n) :
    milnorPolynomialXSpecialization F n (milnorPolynomialConstantMap F n x) = x := by
  exact milnorSpecialization_polyPlaceX_retract (F := F) n x

/-- The constant embedding is split by specialization at `X`. -/
theorem milnorPolynomialXSpecialization_comp_constant (n : ℕ) :
    (milnorPolynomialXSpecialization F n).comp (milnorPolynomialConstantMap F n) =
      AddMonoidHom.id (MilnorKDeg F n) := by
  ext x
  exact milnorPolynomialXSpecialization_constant_apply F n x

/-- Decompose a rational-function Milnor class into its specialization and its invisible part. -/
noncomputable def milnorPolynomialXSplitToProd (n : ℕ) :
    MilnorKDeg (RatFunc F) n →+ MilnorKDeg F n × (milnorPolynomialXSpecialization F n).ker where
  toFun x :=
    (milnorPolynomialXSpecialization F n x,
      ⟨x - milnorPolynomialConstantMap F n (milnorPolynomialXSpecialization F n x), by
        change milnorPolynomialXSpecialization F n
          (x - milnorPolynomialConstantMap F n (milnorPolynomialXSpecialization F n x)) = 0
        rw [map_sub, milnorPolynomialXSpecialization_constant_apply]
        exact sub_self _⟩)
  map_zero' := by
    ext <;> simp [milnorPolynomialXSpecialization, milnorPolynomialConstantMap]
  map_add' x y := by
    apply Prod.ext
    · exact map_add _ x y
    · apply Subtype.ext
      change x + y - milnorPolynomialConstantMap F n
          (milnorPolynomialXSpecialization F n (x + y)) =
        (x - milnorPolynomialConstantMap F n (milnorPolynomialXSpecialization F n x)) +
          (y - milnorPolynomialConstantMap F n (milnorPolynomialXSpecialization F n y))
      rw [map_add, map_add]
      abel

/-- Reassemble a rational-function Milnor class from its constant and invisible parts. -/
noncomputable def milnorPolynomialXSplitFromProd (n : ℕ) :
    MilnorKDeg F n × (milnorPolynomialXSpecialization F n).ker →+ MilnorKDeg (RatFunc F) n where
  toFun p := milnorPolynomialConstantMap F n p.1 + p.2
  map_zero' := by
    simp [milnorPolynomialConstantMap]
  map_add' p q := by
    change milnorPolynomialConstantMap F n (p.1 + q.1) + ↑(p.2 + q.2) =
      (milnorPolynomialConstantMap F n p.1 + ↑p.2) +
        (milnorPolynomialConstantMap F n q.1 + ↑q.2)
    rw [map_add, AddSubgroup.coe_add]
    abel

/-- A single local specialization splits rational-function Milnor `K`-theory into constants and
the kernel invisible at that place. -/
noncomputable def milnorPolynomialXSplitEquiv (n : ℕ) :
    MilnorKDeg (RatFunc F) n ≃+ MilnorKDeg F n × (milnorPolynomialXSpecialization F n).ker :=
  { milnorPolynomialXSplitToProd F n with
    invFun := milnorPolynomialXSplitFromProd F n
    left_inv := by
      intro x
      change milnorPolynomialConstantMap F n (milnorPolynomialXSpecialization F n x) +
        (x - milnorPolynomialConstantMap F n (milnorPolynomialXSpecialization F n x)) = x
      abel
    right_inv := by
      rintro ⟨a, x⟩
      apply Prod.ext
      · change milnorPolynomialXSpecialization F n
          (milnorPolynomialConstantMap F n a + ↑x) = a
        rw [map_add, milnorPolynomialXSpecialization_constant_apply, x.property]
        exact add_zero a
      · apply Subtype.ext
        change milnorPolynomialConstantMap F n a + ↑x -
            milnorPolynomialConstantMap F n
              (milnorPolynomialXSpecialization F n (milnorPolynomialConstantMap F n a + ↑x)) = x
        rw [map_add, milnorPolynomialXSpecialization_constant_apply, x.property, add_zero]
        abel }

end GaloisForLFunctions.HTGeometry
