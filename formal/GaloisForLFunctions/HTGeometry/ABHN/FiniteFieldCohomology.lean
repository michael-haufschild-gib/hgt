/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.FiniteFieldNormSequence

/-!
# Finite-field Galois cohomology for ABHN

For a finite extension of finite fields, every positive even Galois cohomology group of the unit
representation vanishes.  The degree-two case is a necessary cohomological precursor to the
triviality of the finite-field Brauer group.  This module does not identify degree-two Galois
cohomology with Brauer classes.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

open CategoryTheory
open groupCohomology Rep Rep.FiniteCyclicGroup

section

attribute [local instance] IsCyclic.commGroup

/-- A unit fixed by a generator of a finite-field Galois group is a representation norm. -/
theorem finiteField_cyclicGalois_invariantUnit_is_norm {K L : Type} [Field K] [Field L]
    [Algebra K L] [Finite L] {g : Gal(L/K)} (hg : ∀ sigma, sigma ∈ Subgroup.zpowers g)
    (x : LinearMap.ker
      ((Rep.ofAlgebraAutOnUnits K L).applyAsHom g - 𝟙 (Rep.ofAlgebraAutOnUnits K L)).hom.toLinearMap) :
    x.1 ∈ LinearMap.range (Rep.ofAlgebraAutOnUnits K L).norm.hom.toLinearMap := by
  have hx' : ((Rep.ofAlgebraAutOnUnits K L).applyAsHom g).hom x.1 = x.1 := by
    exact sub_eq_zero.mp x.2
  let e := Rep.toAdditive (M := Gal(L/K)) (G := Lˣ)
  have hxg' : Additive.ofMul (Units.map g.toMonoidHom (e x.1).toMul) = e x.1 := by
    change Additive.ofMul (Units.map g.toMonoidHom (e x.1).toMul) = e x.1 at hx'
    exact hx'
  have hxg : Units.map g.toMonoidHom (e x.1).toMul = (e x.1).toMul := by
    exact Additive.ofMul.injective hxg'
  let u : Lˣ := (e x.1).toMul
  have hxg_val : g (u : L) = u := by
    simpa [u] using congrArg Units.val hxg
  have hg_mem : g ∈ MulAction.stabilizer (Gal(L/K)) (u : L) := by
    rw [MulAction.mem_stabilizer_iff]
    exact hxg_val
  have hzpowers : Subgroup.zpowers g ≤ MulAction.stabilizer (Gal(L/K)) (u : L) :=
    Subgroup.zpowers_le_of_mem hg_mem
  have hfixed : ∀ sigma : Gal(L/K), sigma (u : L) = u := by
    intro sigma
    exact MulAction.mem_stabilizer_iff.mp (hzpowers (hg sigma))
  obtain ⟨a, ha⟩ := (IsGalois.mem_range_algebraMap_iff_fixed (u : L)).mpr hfixed
  have ha0 : a ≠ 0 := by
    intro ha0
    have hu0 : (u : L) = 0 := by simpa [ha0] using ha.symm
    exact u.ne_zero hu0
  obtain ⟨y, hy⟩ := FiniteField.unitsMap_norm_surjective K L (Units.mk0 a ha0)
  refine ⟨e.symm (Additive.ofMul y), ?_⟩
  apply e.injective
  apply Additive.toMul.injective
  apply Units.ext
  change
    ((Additive.toMul (e ((Rep.ofAlgebraAutOnUnits K L).norm.hom
      (e.symm (Additive.ofMul y)))) : Lˣ) : L) = u
  rw [show e = Rep.toAdditive (M := Gal(L/K)) (G := Lˣ) by rfl]
  rw [groupCohomology.norm_ofAlgebraAutOnUnits_eq]
  have hy' := congrArg Units.val hy
  change Algebra.norm K (y : L) = a at hy'
  rw [hy', ha]

/-- Every positive even cohomology class of the unit Galois representation of a finite-field
extension is zero. -/
theorem finiteField_cyclicGalois_evenCohomology_eq_zero {K L : Type} [Field K] [Field L]
    [Algebra K L] [Finite L] {g : Gal(L/K)} (hg : ∀ sigma, sigma ∈ Subgroup.zpowers g)
    (i : ℕ) [NeZero i] (hi : Even i)
    (z : groupCohomology (Rep.ofAlgebraAutOnUnits K L) i) : z = 0 := by
  obtain ⟨x, hx⟩ :=
    (ModuleCat.epi_iff_surjective (groupCohomologyπEven
      (Rep.ofAlgebraAutOnUnits K L) g hg i hi)).mp inferInstance z
  rw [← hx]
  exact (groupCohomologyπEven_eq_zero_iff (Rep.ofAlgebraAutOnUnits K L) g hg i hi x).mpr
    (finiteField_cyclicGalois_invariantUnit_is_norm hg x)

/-- Every positive odd cohomology class of the unit Galois representation of a finite-field
extension is zero.  Cyclic Hilbert 90 identifies the kernel of the norm with the image of the
generator-minus-identity map. -/
theorem finiteField_cyclicGalois_oddCohomology_eq_zero {K L : Type} [Field K] [Field L]
    [Algebra K L] [Finite L] {g : Gal(L/K)} (hg : ∀ sigma, sigma ∈ Subgroup.zpowers g)
    (i : ℕ) (hi : Odd i)
    (z : groupCohomology (Rep.ofAlgebraAutOnUnits K L) i) : z = 0 := by
  obtain ⟨x, hx⟩ :=
    (ModuleCat.epi_iff_surjective (groupCohomologyπOdd
      (Rep.ofAlgebraAutOnUnits K L) g hg i hi)).mp inferInstance z
  rw [← hx]
  apply (groupCohomologyπOdd_eq_zero_iff
    (Rep.ofAlgebraAutOnUnits K L) g hg i hi x).mpr
  let e := Rep.toAdditive (M := Gal(L/K)) (G := Lˣ)
  let u : Lˣ := (e x.1).toMul
  have hxu : e.symm (Additive.ofMul u) = x.1 := by
    apply e.injective
    simp [u]
  have hnorm_u :
      ((Rep.ofAlgebraAutOnUnits K L).norm.hom (e.symm (Additive.ofMul u))) = 0 := by
    rw [hxu]
    exact x.2
  have hnorm_add := congrArg e hnorm_u
  have hnorm_L : algebraMap K L (Algebra.norm K (u : L)) = 1 := by
    rw [← groupCohomology.norm_ofAlgebraAutOnUnits_eq u, hnorm_add]
    rfl
  have hnorm : Algebra.norm K (u : L) = 1 := by
    apply FaithfulSMul.algebraMap_injective K L
    simpa using hnorm_L
  obtain ⟨y, hy⟩ :=
    (cyclicGalois_norm_eq_one_iff_exists_div_apply hg (u : L)).mp hnorm
  refine ⟨e.symm (Additive.ofMul y⁻¹), ?_⟩
  apply e.injective
  rw [← hxu]
  simp only [sub_hom, Rep.hom_id,
    Representation.IntertwiningMap.sub_toLinearMap, Representation.IntertwiningMap.toLinearMap_id,
    LinearMap.sub_apply, Representation.IntertwiningMap.coe_toLinearMap, applyAsHom_apply,
    LinearMap.id_coe, id_eq, AddEquiv.apply_symm_apply]
  change Additive.ofMul (Units.map g.toMonoidHom y⁻¹) - Additive.ofMul y⁻¹ =
    Additive.ofMul u
  apply Additive.toMul.injective
  change Units.map g.toMonoidHom y⁻¹ / y⁻¹ = u
  apply Units.ext
  simp only [Units.val_div_eq_div_val, Units.coe_map, Units.val_inv_eq_inv_val]
  change g ((y : L)⁻¹) / (y : L)⁻¹ = (u : L)
  field_simp
  have hginv : g (1 / (y : L)) = 1 / g (y : L) := by
    change g.toAlgHom (1 / (y : L)) = 1 / g.toAlgHom (y : L)
    simpa only [map_one] using (map_div₀ g.toAlgHom 1 (y : L))
  rw [hginv]
  simpa [div_eq_mul_inv] using hy

end

/-- Positive even cohomology of the unit Galois representation vanishes for every finite-field
extension, without choosing a generator in the statement. -/
theorem finiteField_evenCohomology_eq_zero {K L : Type} [Field K] [Field L] [Algebra K L]
    [Finite L] (i : ℕ) [NeZero i] (hi : Even i)
    (z : groupCohomology (Rep.ofAlgebraAutOnUnits K L) i) : z = 0 := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Gal(L/K))
  exact finiteField_cyclicGalois_evenCohomology_eq_zero hg i hi z

/-- Positive odd cohomology of the unit Galois representation vanishes for every finite-field
extension, without choosing a generator in the statement. -/
theorem finiteField_oddCohomology_eq_zero {K L : Type} [Field K] [Field L] [Algebra K L]
    [Finite L] (i : ℕ) (hi : Odd i)
    (z : groupCohomology (Rep.ofAlgebraAutOnUnits K L) i) : z = 0 := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Gal(L/K))
  exact finiteField_cyclicGalois_oddCohomology_eq_zero hg i hi z

/-- Every positive Galois cohomology group of units of a finite-field extension vanishes. -/
theorem finiteField_positiveCohomology_eq_zero {K L : Type} [Field K] [Field L] [Algebra K L]
    [Finite L] (i : ℕ) (hi : i ≠ 0)
    (z : groupCohomology (Rep.ofAlgebraAutOnUnits K L) i) : z = 0 := by
  rcases Nat.even_or_odd i with h | h
  · letI : NeZero i := ⟨hi⟩
    exact finiteField_evenCohomology_eq_zero i h z
  · exact finiteField_oddCohomology_eq_zero i h z

/-- All positive Galois cohomology of units is trivial for a finite-field extension. -/
theorem finiteField_positiveCohomology_subsingleton {K L : Type} [Field K] [Field L]
    [Algebra K L] [Finite L] (i : ℕ) (hi : i ≠ 0) :
    Subsingleton (groupCohomology (Rep.ofAlgebraAutOnUnits K L) i) where
  allEq x y := (finiteField_positiveCohomology_eq_zero i hi x).trans
    (finiteField_positiveCohomology_eq_zero i hi y).symm

/-- The degree-two Galois cohomology of units of a finite-field extension is zero. -/
theorem finiteField_H2_eq_zero {K L : Type} [Field K] [Field L] [Algebra K L] [Finite L]
    (z : groupCohomology (Rep.ofAlgebraAutOnUnits K L) 2) : z = 0 :=
  finiteField_evenCohomology_eq_zero 2 even_two z

/-- The degree-two Galois cohomology of units of a finite-field extension is subsingleton. -/
theorem finiteField_H2_subsingleton {K L : Type} [Field K] [Field L] [Algebra K L] [Finite L] :
    Subsingleton (groupCohomology (Rep.ofAlgebraAutOnUnits K L) 2) where
  allEq x y := (finiteField_H2_eq_zero x).trans (finiteField_H2_eq_zero y).symm

end GaloisForLFunctions.HTGeometry.ABHN
