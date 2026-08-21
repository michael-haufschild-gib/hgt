import GaloisForLFunctions.HTGeometry.ABHN.CyclicHilbert90
import Mathlib.FieldTheory.Galois.Basic

/-!
# Degree-two cohomology of cyclic Galois extensions

For a finite cyclic Galois extension, Mathlib's periodic resolution presents degree-two Galois
cohomology of units as generator-fixed units modulo norm images.  This file exposes that result in
the field-theoretic language used by cyclic algebras.

This is one input for the cyclic-algebra route to local invariants.  It does not identify this
cohomology group with a Brauer group and does not construct local reciprocity.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

open CategoryTheory groupCohomology Rep Rep.FiniteCyclicGroup

attribute [local instance] IsCyclic.commGroup

variable (K L : Type) [Field K] [Field L] [Algebra K L] [IsCyclic Gal(L/K)]

/-- A chosen generator of a cyclic Galois group. -/
noncomputable def cyclicGaloisGenerator : Gal(L/K) :=
  (IsCyclic.exists_generator (α := Gal(L/K))).choose

/-- The chosen Galois automorphism generates the Galois group. -/
theorem cyclicGaloisGenerator_spec :
    ∀ sigma : Gal(L/K), sigma ∈ Subgroup.zpowers (cyclicGaloisGenerator K L) :=
  (IsCyclic.exists_generator (α := Gal(L/K))).choose_spec

/-- In a finite cyclic Galois extension, the chosen cyclic generator has order equal to the
extension degree. -/
theorem cyclicGaloisGenerator_orderOf [FiniteDimensional K L] [IsGalois K L] :
    orderOf (cyclicGaloisGenerator K L) = Module.finrank K L := by
  calc
    orderOf (cyclicGaloisGenerator K L) = Nat.card Gal(L/K) :=
      orderOf_eq_card_of_forall_mem_zpowers (cyclicGaloisGenerator_spec K L)
    _ = Module.finrank K L := IsGalois.card_aut_eq_finrank K L

/-- The degree-th power of the chosen cyclic Galois generator is the identity. -/
theorem cyclicGaloisGenerator_pow_finrank [FiniteDimensional K L] [IsGalois K L] :
    cyclicGaloisGenerator K L ^ Module.finrank K L = 1 := by
  rw [← cyclicGaloisGenerator_orderOf K L]
  exact pow_orderOf_eq_one _

section H2

variable [FiniteDimensional K L]

/-- The quotient map from units fixed by a cyclic generator to degree-two Galois cohomology. -/
noncomputable def cyclicGaloisH2Projection :
    LinearMap.ker
      ((Rep.ofAlgebraAutOnUnits K L).applyAsHom (cyclicGaloisGenerator K L) -
        𝟙 (Rep.ofAlgebraAutOnUnits K L)).hom.toLinearMap →+
      groupCohomology (Rep.ofAlgebraAutOnUnits K L) 2 :=
  (Rep.FiniteCyclicGroup.groupCohomologyπEven
    (Rep.ofAlgebraAutOnUnits K L) (cyclicGaloisGenerator K L)
      (cyclicGaloisGenerator_spec K L) 2 even_two).hom.toAddMonoidHom

/-- Every degree-two Galois cohomology class of cyclic units has a generator-fixed-unit
representative. -/
theorem cyclicGaloisH2Projection_surjective :
    Function.Surjective (cyclicGaloisH2Projection K L) :=
  (ModuleCat.epi_iff_surjective
    (Rep.FiniteCyclicGroup.groupCohomologyπEven
      (Rep.ofAlgebraAutOnUnits K L) (cyclicGaloisGenerator K L)
        (cyclicGaloisGenerator_spec K L) 2 even_two)).mp inferInstance

/-- A generator-fixed unit represents zero in degree-two Galois cohomology precisely when it is
a norm. -/
theorem cyclicGaloisH2Projection_eq_zero_iff
    (x : LinearMap.ker
      ((Rep.ofAlgebraAutOnUnits K L).applyAsHom (cyclicGaloisGenerator K L) -
        𝟙 (Rep.ofAlgebraAutOnUnits K L)).hom.toLinearMap) :
    cyclicGaloisH2Projection K L x = 0 ↔
      x.1 ∈ LinearMap.range (Rep.ofAlgebraAutOnUnits K L).norm.hom.toLinearMap :=
  Rep.FiniteCyclicGroup.groupCohomologyπEven_eq_zero_iff
    (Rep.ofAlgebraAutOnUnits K L) (cyclicGaloisGenerator K L)
      (cyclicGaloisGenerator_spec K L) 2 even_two x

/-- Two generator-fixed units represent the same degree-two Galois cohomology class precisely
when their quotient in additive notation is a norm. -/
theorem cyclicGaloisH2Projection_eq_iff
    (x y : LinearMap.ker
      ((Rep.ofAlgebraAutOnUnits K L).applyAsHom (cyclicGaloisGenerator K L) -
        𝟙 (Rep.ofAlgebraAutOnUnits K L)).hom.toLinearMap) :
    cyclicGaloisH2Projection K L x = cyclicGaloisH2Projection K L y ↔
      x.1 - y.1 ∈ LinearMap.range (Rep.ofAlgebraAutOnUnits K L).norm.hom.toLinearMap :=
  Rep.FiniteCyclicGroup.groupCohomologyπEven_eq_iff
    (Rep.ofAlgebraAutOnUnits K L) (cyclicGaloisGenerator K L)
      (cyclicGaloisGenerator_spec K L) 2 even_two x y

/-- The unit underlying a generator-fixed representative for cyclic degree-two cohomology. -/
noncomputable def cyclicGaloisH2FixedUnit
    (x : LinearMap.ker
      ((Rep.ofAlgebraAutOnUnits K L).applyAsHom (cyclicGaloisGenerator K L) -
        𝟙 (Rep.ofAlgebraAutOnUnits K L)).hom.toLinearMap) : Lˣ :=
  Additive.toMul (Rep.toAdditive (M := Gal(L/K)) (G := Lˣ) x.1)

omit [FiniteDimensional K L] in
/-- A cyclic degree-two representative is fixed by the chosen generator. -/
theorem cyclicGaloisH2FixedUnit_generator_fixed
    (x : LinearMap.ker
      ((Rep.ofAlgebraAutOnUnits K L).applyAsHom (cyclicGaloisGenerator K L) -
        𝟙 (Rep.ofAlgebraAutOnUnits K L)).hom.toLinearMap) :
    Units.map (cyclicGaloisGenerator K L).toMonoidHom (cyclicGaloisH2FixedUnit K L x) =
      cyclicGaloisH2FixedUnit K L x := by
  have hx := x.property
  change Additive.ofMul (Units.map (cyclicGaloisGenerator K L).toMonoidHom
    (Additive.toMul (Rep.toAdditive (M := Gal(L/K)) (G := Lˣ) x.1))) -
      Rep.toAdditive (M := Gal(L/K)) (G := Lˣ) x.1 = 0 at hx
  exact congrArg Additive.toMul (sub_eq_zero.mp hx)

omit [FiniteDimensional K L] in
/-- In a cyclic Galois extension, a cyclic degree-two representative is fixed by every Galois
automorphism. -/
theorem cyclicGaloisH2FixedUnit_fixed [IsGalois K L]
    (x : LinearMap.ker
      ((Rep.ofAlgebraAutOnUnits K L).applyAsHom (cyclicGaloisGenerator K L) -
        𝟙 (Rep.ofAlgebraAutOnUnits K L)).hom.toLinearMap) (sigma : Gal(L/K)) :
    Units.map sigma.toMonoidHom (cyclicGaloisH2FixedUnit K L x) =
      cyclicGaloisH2FixedUnit K L x := by
  let u := cyclicGaloisH2FixedUnit K L x
  let H : Subgroup Gal(L/K) := MulAction.stabilizer Gal(L/K) u
  have hgen : Units.map (cyclicGaloisGenerator K L).toMonoidHom u = u := by
    change Units.map (cyclicGaloisGenerator K L).toMonoidHom (cyclicGaloisH2FixedUnit K L x) =
      cyclicGaloisH2FixedUnit K L x
    exact cyclicGaloisH2FixedUnit_generator_fixed K L x
  have hgmem : cyclicGaloisGenerator K L ∈ H := by
    change Units.map (cyclicGaloisGenerator K L).toMonoidHom u = u
    exact hgen
  have hsigmamem : sigma ∈ H :=
    (Subgroup.zpowers_le.mpr hgmem) (cyclicGaloisGenerator_spec K L sigma)
  change Units.map sigma.toMonoidHom u = u at hsigmamem
  exact hsigmamem

/-- A generator-fixed degree-two representative of a finite cyclic Galois extension comes from a
base-field unit. -/
theorem cyclicGaloisH2FixedUnit_exists_base_unit [IsGalois K L]
    (x : LinearMap.ker
      ((Rep.ofAlgebraAutOnUnits K L).applyAsHom (cyclicGaloisGenerator K L) -
        𝟙 (Rep.ofAlgebraAutOnUnits K L)).hom.toLinearMap) :
    ∃ y : Kˣ, Units.map (algebraMap K L) y = cyclicGaloisH2FixedUnit K L x := by
  let u := cyclicGaloisH2FixedUnit K L x
  have hfixed : ∀ sigma : Gal(L/K), sigma (u : L) = u := by
    intro sigma
    have hs : Units.map sigma.toMonoidHom u = u := by
      exact cyclicGaloisH2FixedUnit_fixed K L x sigma
    simpa using congrArg Units.val hs
  obtain ⟨y, hy⟩ := (IsGalois.mem_range_algebraMap_iff_fixed (u : L)).mpr hfixed
  have hy_ne : y ≠ 0 := by
    intro hy0
    rw [hy0, map_zero] at hy
    exact u.ne_zero hy.symm
  refine ⟨Units.mk0 y hy_ne, ?_⟩
  apply Units.ext
  exact hy

/-- The base-field unit underlying a generator-fixed degree-two representative is unique. -/
theorem cyclicGaloisH2FixedUnit_existsUnique_base_unit [IsGalois K L]
    (x : LinearMap.ker
      ((Rep.ofAlgebraAutOnUnits K L).applyAsHom (cyclicGaloisGenerator K L) -
        𝟙 (Rep.ofAlgebraAutOnUnits K L)).hom.toLinearMap) :
    ∃! y : Kˣ, Units.map (algebraMap K L) y = cyclicGaloisH2FixedUnit K L x := by
  obtain ⟨y, hy⟩ := cyclicGaloisH2FixedUnit_exists_base_unit K L x
  refine ⟨y, hy, ?_⟩
  intro z hz
  apply Units.ext
  apply FaithfulSMul.algebraMap_injective K L
  exact congrArg Units.val (hz.trans hy.symm)

/-- The additive group of generator-fixed unit representatives for cyclic degree-two
cohomology.  Naming this kernel keeps the cohomology-to-cyclic-algebra interface independent of
the implementation of the periodic resolution. -/
noncomputable abbrev cyclicGaloisH2FixedUnits :=
  LinearMap.ker
    ((Rep.ofAlgebraAutOnUnits K L).applyAsHom (cyclicGaloisGenerator K L) -
      𝟙 (Rep.ofAlgebraAutOnUnits K L)).hom.toLinearMap

/-- Degree-two Galois cohomology of the unit representation, named for the cyclic-algebra
interface. -/
noncomputable abbrev cyclicGaloisH2 :=
  groupCohomology (Rep.ofAlgebraAutOnUnits K L) 2

/-- A chosen generator-fixed unit representative of every cyclic degree-two cohomology class. -/
noncomputable def cyclicGaloisH2Representative (z : cyclicGaloisH2 K L) :
    cyclicGaloisH2FixedUnits K L :=
  (cyclicGaloisH2Projection_surjective K L z).choose

/-- The chosen representative projects to its original degree-two cohomology class. -/
theorem cyclicGaloisH2Representative_projection (z : cyclicGaloisH2 K L) :
    cyclicGaloisH2Projection K L (cyclicGaloisH2Representative K L z) = z :=
  (cyclicGaloisH2Projection_surjective K L z).choose_spec

/-- The unique base-field unit represented by a generator-fixed cyclic degree-two cocycle. -/
noncomputable def cyclicGaloisH2FixedBaseUnit [IsGalois K L]
    (x : LinearMap.ker
      ((Rep.ofAlgebraAutOnUnits K L).applyAsHom (cyclicGaloisGenerator K L) -
        𝟙 (Rep.ofAlgebraAutOnUnits K L)).hom.toLinearMap) : Kˣ :=
  (cyclicGaloisH2FixedUnit_existsUnique_base_unit K L x).choose

/-- The canonical base unit maps to the fixed unit underlying the degree-two representative. -/
theorem cyclicGaloisH2FixedBaseUnit_map [IsGalois K L]
    (x : LinearMap.ker
      ((Rep.ofAlgebraAutOnUnits K L).applyAsHom (cyclicGaloisGenerator K L) -
        𝟙 (Rep.ofAlgebraAutOnUnits K L)).hom.toLinearMap) :
    Units.map (algebraMap K L) (cyclicGaloisH2FixedBaseUnit K L x) =
      cyclicGaloisH2FixedUnit K L x :=
  (cyclicGaloisH2FixedUnit_existsUnique_base_unit K L x).choose_spec.1

/-- A cyclic degree-two representative is cohomologically zero precisely when its underlying
fixed unit is a field norm. -/
theorem cyclicGaloisH2Projection_eq_zero_iff_exists_field_norm [IsGalois K L]
    (x : LinearMap.ker
      ((Rep.ofAlgebraAutOnUnits K L).applyAsHom (cyclicGaloisGenerator K L) -
        𝟙 (Rep.ofAlgebraAutOnUnits K L)).hom.toLinearMap) :
    cyclicGaloisH2Projection K L x = 0 ↔
      ∃ y : Lˣ, cyclicGaloisH2FixedUnit K L x =
        Units.map (algebraMap K L) (cyclicGaloisNormUnits K L y) := by
  let e := Rep.toAdditive (M := Gal(L/K)) (G := Lˣ)
  constructor
  · intro hx
    obtain ⟨z, hz⟩ := (cyclicGaloisH2Projection_eq_zero_iff K L x).mp hx
    let y : Lˣ := Additive.toMul (e z)
    have hzy : z = e.symm (Additive.ofMul y) := by
      apply e.injective
      simp [y]
    rw [hzy] at hz
    refine ⟨y, ?_⟩
    apply Units.ext
    have hval := congrArg (fun w => ((Additive.toMul (e w) : Lˣ) : L)) hz
    change ((Additive.toMul (e ((Rep.ofAlgebraAutOnUnits K L).norm.hom
      (e.symm (Additive.ofMul y)))) : Lˣ) : L) =
        ((Additive.toMul (e x.1) : Lˣ) : L) at hval
    rw [show e = Rep.toAdditive (M := Gal(L/K)) (G := Lˣ) by rfl] at hval
    rw [groupCohomology.norm_ofAlgebraAutOnUnits_eq y] at hval
    exact hval.symm
  · rintro ⟨y, hy⟩
    apply (cyclicGaloisH2Projection_eq_zero_iff K L x).mpr
    refine ⟨e.symm (Additive.ofMul y), ?_⟩
    apply e.injective
    apply Additive.toMul.injective
    apply Units.ext
    change ((Additive.toMul (e ((Rep.ofAlgebraAutOnUnits K L).norm.hom
      (e.symm (Additive.ofMul y)))) : Lˣ) : L) = cyclicGaloisH2FixedUnit K L x
    rw [show e = Rep.toAdditive (M := Gal(L/K)) (G := Lˣ) by rfl]
    rw [groupCohomology.norm_ofAlgebraAutOnUnits_eq y]
    exact congrArg Units.val hy.symm

/-- The subgroup of generator-fixed units that are norms. -/
noncomputable def cyclicGaloisH2NormImage :
    AddSubgroup (LinearMap.ker
      ((Rep.ofAlgebraAutOnUnits K L).applyAsHom (cyclicGaloisGenerator K L) -
        𝟙 (Rep.ofAlgebraAutOnUnits K L)).hom.toLinearMap) where
  carrier := {x | x.1 ∈ LinearMap.range (Rep.ofAlgebraAutOnUnits K L).norm.hom.toLinearMap}
  zero_mem' := by
    exact ⟨0, map_zero _⟩
  add_mem' := by
    intro x y hx hy
    exact (LinearMap.range (Rep.ofAlgebraAutOnUnits K L).norm.hom.toLinearMap).add_mem hx hy
  neg_mem' := by
    intro x hx
    exact (LinearMap.range (Rep.ofAlgebraAutOnUnits K L).norm.hom.toLinearMap).neg_mem hx

/-- Within generator-fixed units, the norm-image subgroup is exactly the kernel of the degree-two
cohomology projection. -/
theorem cyclicGaloisH2NormImage_eq_ker :
    cyclicGaloisH2NormImage K L = (cyclicGaloisH2Projection K L).ker := by
  ext x
  rw [AddMonoidHom.mem_ker]
  exact (cyclicGaloisH2Projection_eq_zero_iff K L x).symm

/-- Generator-fixed units, their norm-image subgroup, and degree-two Galois cohomology are exact. -/
theorem cyclicGaloisH2NormImage_exact :
    Function.Exact (cyclicGaloisH2NormImage K L).subtype (cyclicGaloisH2Projection K L) := by
  intro x
  change x ∈ (cyclicGaloisH2Projection K L).ker ↔ _
  rw [← cyclicGaloisH2NormImage_eq_ker K L]
  constructor
  · intro hx
    exact ⟨⟨x, hx⟩, rfl⟩
  · rintro ⟨y, rfl⟩
    exact y.property

/-- The quotient of generator-fixed units by norm images is degree-two Galois cohomology. -/
noncomputable def cyclicGaloisH2NormQuotientEquiv :
    (LinearMap.ker
      ((Rep.ofAlgebraAutOnUnits K L).applyAsHom (cyclicGaloisGenerator K L) -
        𝟙 (Rep.ofAlgebraAutOnUnits K L)).hom.toLinearMap) ⧸
      cyclicGaloisH2NormImage K L ≃+
      groupCohomology (Rep.ofAlgebraAutOnUnits K L) 2 :=
  (QuotientAddGroup.quotientAddEquivOfEq (cyclicGaloisH2NormImage_eq_ker K L)).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective (cyclicGaloisH2Projection K L)
      (cyclicGaloisH2Projection_surjective K L))

end H2

end GaloisForLFunctions.HTGeometry.ABHN
