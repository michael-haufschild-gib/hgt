import GaloisForLFunctions.RHTower.Artin.HerbrandIndicesOfFinitelyGeneratedAndPermutationModules
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import Mathlib.NumberTheory.NumberField.InfinitePlace.Ramification
import Mathlib.LinearAlgebra.Dimension.Torsion.Finite
import Mathlib.LinearAlgebra.Dimension.RankNullity
import Mathlib.LinearAlgebra.Isomorphisms

/-!
# Units permuted by the Galois group have finite index

Let a finite group `G` act on a number field `L` by automorphisms. It acts on the infinite
places of `L`, `(τ w)(x) = w(τ⁻¹ x)` (`infinitePlaceMulAction`), and on the units of `L`
(`unitsRep`).

* **Units permuted by `G`** (`artinUnit`, `unitsMap_artinUnit`, `logAt_artinUnit_neg`): there
  are units `η_w`, one for every infinite place `w`, with `τ η_w = η_{τ w}` and `|η_w|_{w'} < 1`
  for `w' ≠ w`. If `u_w` is any unit with `|u_w|_{w'} < 1` for `w' ≠ w`, take
  `η_w = Π_τ τ(u_{τ⁻¹ w})`.
* **Independence** (`eq_zero_of_artinUnitHom_eq_zero`): `Π_w η_w^{y_w} = 1` and `Σ_w y_w = 0`
  give `y = 0`. The matrix `M_{w' w} = n_{w'} log |η_w|_{w'}` has negative entries off the
  diagonal and zero column sums; a real vector `c` with `M c = 0` and `Σ c = 0` vanishes
  (`eq_zero_of_offDiag_neg`): summing the rows with `c_{w'} > 0` gives
  `Σ_w c_w S_w = 0`, `S_w = Σ_{c_{w'} > 0} M_{w' w}`, where `S_w > 0` if `c_w > 0` and
  `S_w ≤ 0` if `c_w ≤ 0`.
* **Finite index** (`index_map_artinUnitHom_ne_zero`): the units `Π_w η_w^{y_w}`, `Σ_w y_w = 0`,
  form a subgroup of finite index in the unit group, because both have rank `r₁ + r₂ − 1`
  (`index_ne_zero_of_finrank_eq`).

So `y ↦ Π_w η_w^{y_w}` is an injective `G`-homomorphism with finite cokernel from the
vectors of sum zero in the permutation module of the infinite places to the units.
-/

open scoped Classical NumberField
open NumberField NumberField.InfinitePlace NumberField.Units Module

noncomputable section

namespace GaloisForLFunctions

section Matrix

variable {X : Type*} [Fintype X]

/-- A real matrix with negative entries off the diagonal and zero column sums has no nonzero
vector of coordinate sum zero in its kernel. -/
theorem eq_zero_of_offDiag_neg (M : X → X → ℝ) (hneg : ∀ w' w, w' ≠ w → M w' w < 0)
    (hcol : ∀ w, ∑ w', M w' w = 0) (c : X → ℝ) (hrow : ∀ w', ∑ w, c w * M w' w = 0)
    (hsum : ∑ w, c w = 0) : c = 0 := by
  by_contra hc
  have hpos : ∃ w, 0 < c w := by
    by_contra h
    simp only [not_exists, not_lt] at h
    exact hc (funext fun w =>
      (Finset.sum_eq_zero_iff_of_nonpos fun w _ => h w).mp hsum w (Finset.mem_univ w))
  have hlt : ∃ w, c w < 0 := by
    by_contra h
    simp only [not_exists, not_lt] at h
    exact hc (funext fun w =>
      (Finset.sum_eq_zero_iff_of_nonneg fun w _ => h w).mp hsum w (Finset.mem_univ w))
  obtain ⟨w₁, hw₁⟩ := hpos
  obtain ⟨w₂, hw₂⟩ := hlt
  set P := Finset.univ.filter fun w => 0 < c w
  have hP : ∀ w, w ∈ P ↔ 0 < c w := fun w => by simp [P]
  -- the sum of the rows in `P`
  have h0 : ∑ w, c w * ∑ w' ∈ P, M w' w = 0 := by
    have e : ∑ w, c w * ∑ w' ∈ P, M w' w = ∑ w' ∈ P, ∑ w, c w * M w' w := by
      simp_rw [Finset.mul_sum]
      exact Finset.sum_comm
    rw [e]
    exact Finset.sum_eq_zero fun w' _ => hrow w'
  have hS : ∀ w, w ∈ P → 0 < ∑ w' ∈ P, M w' w := fun w hw => by
    have hc' : ∑ w' ∈ Pᶜ, M w' w < 0 :=
      Finset.sum_neg (fun w' hw' => hneg w' w fun e => Finset.mem_compl.mp hw' (e ▸ hw))
        ⟨w₂, Finset.mem_compl.mpr fun h => absurd ((hP w₂).mp h) (not_lt.mpr hw₂.le)⟩
    have := Finset.sum_add_sum_compl P fun w' => M w' w
    rw [hcol w] at this
    linarith
  have hS' : ∀ w, w ∉ P → ∑ w' ∈ P, M w' w ≤ 0 := fun w hw =>
    Finset.sum_nonpos fun w' hw' => (hneg w' w fun e => hw (e ▸ hw')).le
  have hge : ∀ w ∈ Finset.univ, 0 ≤ c w * ∑ w' ∈ P, M w' w := fun w _ => by
    by_cases hw : w ∈ P
    · exact mul_nonneg ((hP w).mp hw).le (hS w hw).le
    · exact mul_nonneg_of_nonpos_of_nonpos (not_lt.mp fun h => hw ((hP w).mpr h)) (hS' w hw)
  have hgt : 0 < ∑ w, c w * ∑ w' ∈ P, M w' w :=
    Finset.sum_pos' hge ⟨w₁, Finset.mem_univ _, mul_pos hw₁ (hS w₁ ((hP w₁).mpr hw₁))⟩
  exact hgt.ne' h0

/-- The sum of the coordinates of an integer vector. -/
def coordSum (X : Type*) [Fintype X] : (X → ℤ) →+ ℤ where
  toFun y := ∑ x, y x
  map_zero' := Finset.sum_const_zero
  map_add' _ _ := Finset.sum_add_distrib

theorem coordSum_apply (y : X → ℤ) : coordSum X y = ∑ x, y x := rfl

end Matrix

section Rank

/-- The image of an injective homomorphism between finitely generated abelian groups of the same
rank has finite index: the quotient is finitely generated of rank zero, hence finite. -/
theorem index_range_ne_zero_of_finrank_eq {M E : Type*} [AddCommGroup M] [Module ℤ M]
    [AddCommGroup E] [Module.Finite ℤ E] (f : M →ₗ[ℤ] E) (hf : Function.Injective f)
    (h : finrank ℤ M = finrank ℤ E) : (LinearMap.range f).toAddSubgroup.index ≠ 0 := by
  have hq := (LinearMap.range f).finrank_quotient_add_finrank
  rw [LinearMap.finrank_range_of_inj hf, h] at hq
  have h0 := (by omega : ∀ a b : ℕ, a + b = b → a = 0) _ _ hq
  have ht := Module.finrank_eq_zero_iff_isTorsion.mp h0
  haveI : Finite (E ⧸ LinearMap.range f) := Module.finite_of_fg_torsion _ ht
  haveI : Finite (E ⧸ (LinearMap.range f).toAddSubgroup) := ‹Finite (E ⧸ LinearMap.range f)›
  exact AddSubgroup.index_ne_zero_of_finite

end Rank

section Units

variable (L : Type*) [Field L] [NumberField L] (G : Type*) [Group G] [MulSemiringAction G L]

/-- The action of `G` on the infinite places of `L`: `(τ w)(x) = w(τ⁻¹ x)`. -/
@[reducible]
def infinitePlaceMulAction : MulAction G (InfinitePlace L) where
  smul τ w := InfinitePlace.comap w (MulSemiringAction.toRingHom G L τ⁻¹)
  one_smul w := DFunLike.ext _ _ fun x => by
    show w ((1 : G)⁻¹ • x) = w x
    rw [inv_one, one_smul]
  mul_smul τ τ' w := DFunLike.ext _ _ fun x => by
    show w ((τ * τ')⁻¹ • x) = w (τ'⁻¹ • τ⁻¹ • x)
    rw [mul_inv_rev, mul_smul]

attribute [local instance] infinitePlaceMulAction

omit [NumberField L] in
theorem infinitePlace_smul_apply (τ : G) (w : InfinitePlace L) (x : L) :
    (τ • w) x = w (τ⁻¹ • x) := rfl

/-- The action of `τ` on the units of `L`. -/
def unitsMap (τ : G) : (𝓞 L)ˣ →* (𝓞 L)ˣ :=
  Units.map (MulSemiringAction.toRingHom G (𝓞 L) τ : 𝓞 L →* 𝓞 L)

omit [NumberField L] in
theorem coe_unitsMap (τ : G) (u : (𝓞 L)ˣ) :
    ((unitsMap L G τ u : (𝓞 L)ˣ) : L) = τ • ((u : (𝓞 L)ˣ) : L) := rfl

omit [NumberField L] in
theorem unitsMap_mul (τ τ' : G) (u : (𝓞 L)ˣ) :
    unitsMap L G (τ * τ') u = unitsMap L G τ (unitsMap L G τ' u) :=
  Units.ext (mul_smul τ τ' (u : 𝓞 L))

omit [NumberField L] in
theorem unitsMap_one (u : (𝓞 L)ˣ) : unitsMap L G 1 u = u :=
  Units.ext (one_smul G (u : 𝓞 L))

/-- The representation of `G` on the group of units, written additively. -/
def unitsRep : G →* AddMonoid.End (Additive (𝓞 L)ˣ) where
  toFun τ := MonoidHom.toAdditive (unitsMap L G τ)
  map_one' := AddMonoidHom.ext fun u => congrArg Additive.ofMul (unitsMap_one L G u.toMul)
  map_mul' τ τ' :=
    AddMonoidHom.ext fun u => congrArg Additive.ofMul (unitsMap_mul L G τ τ' u.toMul)

omit [NumberField L] in
theorem unitsRep_apply (τ : G) (u : (𝓞 L)ˣ) :
    unitsRep L G τ (Additive.ofMul u) = Additive.ofMul (unitsMap L G τ u) := rfl

omit [NumberField L] in
/-- `|τ u|_w = |u|_{τ⁻¹ w}`. -/
theorem place_unitsMap (w : InfinitePlace L) (τ : G) (u : (𝓞 L)ˣ) :
    w (unitsMap L G τ u : (𝓞 L)ˣ) = (τ⁻¹ • w) (u : (𝓞 L)ˣ) := by
  rw [infinitePlace_smul_apply, inv_inv]
  rfl

/-- The logarithm of the absolute value of a unit at an infinite place. -/
def logAt (w : InfinitePlace L) : Additive (𝓞 L)ˣ →+ ℝ where
  toFun u := Real.log (w ((Additive.toMul u : (𝓞 L)ˣ) : L))
  map_zero' := by simp
  map_add' u v := by
    have hu := pos_at_place (Additive.toMul u) w
    have hv := pos_at_place (Additive.toMul v) w
    simp only [toMul_add, Units.val_mul, map_mul]
    exact Real.log_mul hu.ne' hv.ne'

omit [NumberField L] in
theorem logAt_ofMul (w : InfinitePlace L) (u : (𝓞 L)ˣ) :
    logAt L w (Additive.ofMul u) = Real.log (w (u : (𝓞 L)ˣ)) := rfl

/-- A unit with absolute value `< 1` at all infinite places other than `w`. -/
def seedUnit (w : InfinitePlace L) : (𝓞 L)ˣ := (dirichletUnitTheorem.exists_unit L w).choose

theorem log_seedUnit_neg {w w' : InfinitePlace L} (h : w' ≠ w) :
    Real.log (w' (seedUnit L w : (𝓞 L)ˣ)) < 0 :=
  (dirichletUnitTheorem.exists_unit L w).choose_spec w' h

variable [Fintype G]

/-- The unit `η_w = Π_τ τ(u_{τ⁻¹ w})`. -/
def artinUnit (w : InfinitePlace L) : (𝓞 L)ˣ :=
  ∏ τ : G, unitsMap L G τ (seedUnit L (τ⁻¹ • w))

/-- The units `η_w` are permuted by `G`: `ν η_w = η_{ν w}`. -/
theorem unitsMap_artinUnit (ν : G) (w : InfinitePlace L) :
    unitsMap L G ν (artinUnit L G w) = artinUnit L G (ν • w) := by
  rw [artinUnit, map_prod, artinUnit]
  simp_rw [← unitsMap_mul]
  refine Fintype.prod_bijective (ν * ·) (Group.mulLeft_bijective ν) _ _ fun τ => ?_
  rw [smul_smul, mul_inv_rev, inv_mul_cancel_right]

/-- `|η_w|_{w'} < 1` for `w' ≠ w`. -/
theorem logAt_artinUnit_neg {w w' : InfinitePlace L} (h : w' ≠ w) :
    logAt L w' (Additive.ofMul (artinUnit L G w)) < 0 := by
  rw [artinUnit, ofMul_prod, map_sum]
  refine Finset.sum_neg (fun τ _ => ?_) Finset.univ_nonempty
  rw [logAt_ofMul, place_unitsMap]
  exact log_seedUnit_neg L fun h' => h (smul_left_cancel τ⁻¹ h')

/-- The homomorphism `y ↦ Π_w η_w^{y_w}` from the permutation module of the infinite places
to the units. -/
def artinUnitHom : (InfinitePlace L → ℤ) →+ Additive (𝓞 L)ˣ where
  toFun y := ∑ w, y w • Additive.ofMul (artinUnit L G w)
  map_zero' := by simp
  map_add' y z := by simp only [Pi.add_apply, add_zsmul, Finset.sum_add_distrib]

theorem artinUnitHom_apply (y : InfinitePlace L → ℤ) :
    artinUnitHom L G y = ∑ w, y w • Additive.ofMul (artinUnit L G w) := rfl

/-- The homomorphism `y ↦ Π_w η_w^{y_w}` is `G`-equivariant. -/
theorem artinUnitHom_permRep (τ : G) (y : InfinitePlace L → ℤ) :
    artinUnitHom L G (permRep G (InfinitePlace L) τ y) =
      unitsRep L G τ (artinUnitHom L G y) := by
  rw [artinUnitHom_apply, artinUnitHom_apply, map_sum]
  simp_rw [map_zsmul, unitsRep_apply, unitsMap_artinUnit, permRep_apply]
  exact Fintype.sum_bijective (τ⁻¹ • ·) (MulAction.bijective τ⁻¹) _ _ fun w => by
    rw [smul_inv_smul]

/-- **Independence**: `Π_w η_w^{y_w} = 1` and `Σ_w y_w = 0` give `y = 0`. -/
theorem eq_zero_of_artinUnitHom_eq_zero {y : InfinitePlace L → ℤ} (hs : ∑ w, y w = 0)
    (h : artinUnitHom L G y = 0) : y = 0 := by
  have hc : (fun w => (y w : ℝ)) = 0 := by
    refine eq_zero_of_offDiag_neg
      (fun w' w => (mult w' : ℝ) * logAt L w' (Additive.ofMul (artinUnit L G w))) ?_ ?_ _ ?_ ?_
    · intro w' w hne
      exact mul_neg_of_pos_of_neg (Nat.cast_pos.mpr mult_pos) (logAt_artinUnit_neg L G hne)
    · intro w
      exact sum_mult_mul_log (artinUnit L G w)
    · intro w'
      have h' := congrArg (logAt L w') h
      rw [artinUnitHom_apply, map_sum, map_zero] at h'
      simp_rw [map_zsmul, zsmul_eq_mul] at h'
      calc ∑ w, (y w : ℝ) * ((mult w' : ℝ) * logAt L w' (Additive.ofMul (artinUnit L G w)))
          = (mult w' : ℝ) * ∑ w, (y w : ℝ) * logAt L w' (Additive.ofMul (artinUnit L G w)) := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun w _ => by ring
        _ = 0 := by rw [h', mul_zero]
    · exact_mod_cast hs
  funext w
  have hw : (y w : ℝ) = 0 := congrFun hc w
  exact_mod_cast hw

/-- **Finite index**: the units `Π_w η_w^{y_w}` with `Σ_w y_w = 0` form a subgroup of finite
index in the group of units. -/
theorem index_map_artinUnitHom_ne_zero :
    ((coordSum (InfinitePlace L)).ker.map (artinUnitHom L G)).index ≠ 0 := by
  set s : (InfinitePlace L → ℤ) →ₗ[ℤ] ℤ := (coordSum (InfinitePlace L)).toIntLinearMap
  set φ : (InfinitePlace L → ℤ) →ₗ[ℤ] Additive (𝓞 L)ˣ := (artinUnitHom L G).toIntLinearMap
  have hinj : Function.Injective (φ.domRestrict (LinearMap.ker s)) :=
    (injective_iff_map_eq_zero _).mpr fun b hb =>
      Subtype.ext (eq_zero_of_artinUnitHom_eq_zero L G (LinearMap.mem_ker.mp b.2) hb)
  have hsurj : Function.Surjective s := fun n => by
    obtain ⟨w₀⟩ := (inferInstance : Nonempty (InfinitePlace L))
    refine ⟨Pi.single w₀ n, ?_⟩
    show ∑ w, (Pi.single w₀ n : InfinitePlace L → ℤ) w = n
    rw [Finset.sum_pi_single' w₀ n Finset.univ, if_pos (Finset.mem_univ _)]
  have hN : (LinearMap.range (φ.domRestrict (LinearMap.ker s))).toAddSubgroup.index ≠ 0 := by
    refine index_range_ne_zero_of_finrank_eq _ hinj ?_
    -- both ranks are the number of infinite places minus one
    have hq := (LinearMap.ker s).finrank_quotient_add_finrank
    rw [(s.quotKerEquivOfSurjective hsurj).finrank_eq, Module.finrank_self,
      Module.finrank_fintype_fun_eq_card] at hq
    rw [NumberField.Units.finrank_eq, NumberField.Units.rank]
    omega
  rw [LinearMap.range_domRestrict] at hN
  exact hN

end Units

end GaloisForLFunctions
