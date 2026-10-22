import GaloisForLFunctions.RHTower.Deninger.DeningerGaloisInvariance

/-!
# The fibrewise projection of test functions

Summing a test function over the fibres of a map of discrete spaces gives a test function on the
target: the fibre sums are finite because the support is, and the mass is unchanged, because
grouping a finite sum by the fibres of a map does not change it.

Applied to the restriction of places along an extension of number fields this is the projection
the card calls the field-norm projection: it maps the test space of the larger place space onto
the test space of the smaller one, preserves the mass, and therefore preserves the mass-zero
condition `(5)`.

* `deningerPushFun`, `deningerPush` : **the fibrewise projection.**
* `deningerPush_mass` : **the projection preserves the mass.**
* `deningerPlaceRestrict`, `deningerPlacePush` : the arithmetic instance, along the restriction of
  places.
* `deningerPlacePush_sum` : **the place sum is preserved**, so the mass-zero condition is.
-/

namespace RHTower

open NumberField

section Pushforward

variable {Y Y' : Type*} [TopologicalSpace Y] [DiscreteTopology Y] [TopologicalSpace Y']
  [DiscreteTopology Y']

/-- **The fibrewise projection of a test function**: the sum over the fibre of the map. -/
noncomputable def deningerPushFun (π : Y → Y') (g : DeningerTestSpace Y) : Y' → ℝ :=
  fun v => ∑ᶠ w ∈ π ⁻¹' {v}, (g : Y → ℝ) w

omit [DiscreteTopology Y] [TopologicalSpace Y'] [DiscreteTopology Y'] in
theorem deningerPushFun_eq_sum [DecidableEq Y'] (π : Y → Y') (g : DeningerTestSpace Y)
    (S : Finset Y)
    (hS : Function.support ((g : Y → ℝ)) ⊆ (S : Set Y)) (v : Y') :
    deningerPushFun π g v = ∑ w ∈ S.filter (fun w => π w = v), (g : Y → ℝ) w := by
  classical
  refine finsum_mem_eq_sum_of_inter_support_eq _ ?_
  ext w
  constructor
  · rintro ⟨hw, hs⟩
    exact ⟨Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨Finset.mem_coe.mp (hS hs), hw⟩), hs⟩
  · rintro ⟨hw, hs⟩
    exact ⟨(Finset.mem_filter.mp (Finset.mem_coe.mp hw)).2, hs⟩

omit [DiscreteTopology Y] [TopologicalSpace Y'] [DiscreteTopology Y'] in
theorem deningerPushFun_support (π : Y → Y') (g : DeningerTestSpace Y) :
    Function.support (deningerPushFun π g) ⊆ π '' Function.support ((g : Y → ℝ)) := by
  classical
  intro v hv
  by_contra hmem
  refine hv ?_
  have hzero : ∀ w ∈ π ⁻¹' {v}, (g : Y → ℝ) w = 0 := by
    intro w hw
    by_contra hne
    exact hmem ⟨w, hne, hw⟩
  exact finsum_mem_eq_zero_of_forall_eq_zero hzero

theorem deningerPushFun_mem (π : Y → Y') (g : DeningerTestSpace Y) :
    deningerPushFun π g ∈ DeningerTestSpace Y' := by
  refine ⟨IsLocallyConstant.of_discrete _, ?_⟩
  refine Set.Finite.isCompact (Set.Finite.subset ?_ (deningerPushFun_support π g))
  exact (g.2.2.finite_of_discrete).image π

/-- **The fibrewise projection, as a linear map of test spaces.** -/
noncomputable def deningerPush (π : Y → Y') :
    DeningerTestSpace Y →ₗ[ℝ] DeningerTestSpace Y' where
  toFun g := ⟨deningerPushFun π g, deningerPushFun_mem π g⟩
  map_add' g h := by
    classical
    refine Subtype.ext (funext fun v => ?_)
    set S : Finset Y := (g.2.2.finite_of_discrete).toFinset ∪ (h.2.2.finite_of_discrete).toFinset
      with hS
    have hgS : Function.support ((g : Y → ℝ)) ⊆ (S : Set Y) := by
      intro w hw
      exact Finset.mem_coe.mpr (Finset.mem_union_left _
        ((g.2.2.finite_of_discrete).mem_toFinset.mpr hw))
    have hhS : Function.support ((h : Y → ℝ)) ⊆ (S : Set Y) := by
      intro w hw
      exact Finset.mem_coe.mpr (Finset.mem_union_right _
        ((h.2.2.finite_of_discrete).mem_toFinset.mpr hw))
    have hghS : Function.support (((g + h : DeningerTestSpace Y) : Y → ℝ)) ⊆ (S : Set Y) := by
      intro w hw
      by_contra hnot
      refine hw ?_
      have hg : (g : Y → ℝ) w = 0 := by
        by_contra hne
        exact hnot (hgS hne)
      have hh : (h : Y → ℝ) w = 0 := by
        by_contra hne
        exact hnot (hhS hne)
      show (g : Y → ℝ) w + (h : Y → ℝ) w = 0
      rw [hg, hh, add_zero]
    show deningerPushFun π (g + h) v = deningerPushFun π g v + deningerPushFun π h v
    rw [deningerPushFun_eq_sum π _ S hghS v, deningerPushFun_eq_sum π g S hgS v,
      deningerPushFun_eq_sum π h S hhS v, ← Finset.sum_add_distrib]
    rfl
  map_smul' c g := by
    classical
    refine Subtype.ext (funext fun v => ?_)
    set S : Finset Y := (g.2.2.finite_of_discrete).toFinset with hS
    have hgS : Function.support ((g : Y → ℝ)) ⊆ (S : Set Y) := by
      intro w hw
      exact Finset.mem_coe.mpr ((g.2.2.finite_of_discrete).mem_toFinset.mpr hw)
    have hcS : Function.support (((c • g : DeningerTestSpace Y) : Y → ℝ)) ⊆ (S : Set Y) := by
      intro w hw
      refine hgS ?_
      intro hzero
      refine hw ?_
      show c * (g : Y → ℝ) w = 0
      rw [hzero, mul_zero]
    show deningerPushFun π (c • g) v = c * deningerPushFun π g v
    rw [deningerPushFun_eq_sum π _ S hcS v, deningerPushFun_eq_sum π g S hgS v, Finset.mul_sum]
    rfl

theorem deningerPush_apply (π : Y → Y') (g : DeningerTestSpace Y) :
    ((deningerPush π g : DeningerTestSpace Y') : Y' → ℝ) = deningerPushFun π g := rfl

/-- **The fibrewise projection preserves the mass**: grouping a finite sum by the fibres of a map
does not change it. -/
theorem deningerPush_mass (π : Y → Y') (g : DeningerTestSpace Y) :
    ∑ᶠ v, ((deningerPush π g : DeningerTestSpace Y') : Y' → ℝ) v = ∑ᶠ w, (g : Y → ℝ) w := by
  classical
  have hfin : (Function.support ((g : Y → ℝ))).Finite := g.2.2.finite_of_discrete
  set S : Finset Y := hfin.toFinset with hSdef
  have hgS : Function.support ((g : Y → ℝ)) ⊆ (S : Set Y) := by
    intro w hw
    exact Finset.mem_coe.mpr (hfin.mem_toFinset.mpr hw)
  set T : Finset Y' := S.image π with hTdef
  have hmaps : ∀ w ∈ S, π w ∈ T := fun w hw => Finset.mem_image_of_mem π hw
  have hpushS : Function.support (deningerPushFun π g) ⊆ (T : Set Y') := by
    refine (deningerPushFun_support π g).trans ?_
    rintro v ⟨w, hw, rfl⟩
    exact Finset.mem_coe.mpr (Finset.mem_image_of_mem π (Finset.mem_coe.mp (hgS hw)))
  show ∑ᶠ v, deningerPushFun π g v = ∑ᶠ w, (g : Y → ℝ) w
  rw [finsum_eq_sum_of_support_subset _ hpushS, finsum_eq_sum_of_support_subset _ hgS,
    ← Finset.sum_fiberwise_of_maps_to hmaps ((g : Y → ℝ))]
  exact Finset.sum_congr rfl fun v _ => deningerPushFun_eq_sum π g S hgS v

end Pushforward

section PlaceProjection

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

/-- The place of the base below a place of the extension. -/
noncomputable def deningerPlaceRestrict : DeningerPlace L → DeningerPlace K :=
  Sum.map (fun w : InfinitePlace L => w.comap (algebraMap K L)) (deningerRestrictPlace (K := K))

/-- **The field-norm projection of the card**: the fibrewise sum along the restriction of places,
from the test space of the places of `L` to that of the places of `K`. -/
noncomputable def deningerPlacePush :
    DeningerTestSpace (DeningerPlace L) →ₗ[ℝ] DeningerTestSpace (DeningerPlace K) :=
  deningerPush (deningerPlaceRestrict K L)

/-- **The projection preserves the place sum**, hence maps the mass-zero condition `(5)` of the
larger place space into that of the smaller one. -/
theorem deningerPlacePush_sum (g : DeningerTestSpace (DeningerPlace L)) :
    deningerPlaceSum K (deningerPlacePush K L g) = deningerPlaceSum L g := by
  rw [deningerPlaceSum_eq_finsum, deningerPlaceSum_eq_finsum]
  exact deningerPush_mass (deningerPlaceRestrict K L) g

/-- **The projection maps the kernel of the mass into the kernel of the mass.** -/
theorem deningerPlacePush_ker (g : DeningerTestSpace (DeningerPlace L))
    (hg : g ∈ LinearMap.ker (deningerPlaceSum L)) :
    deningerPlacePush K L g ∈ LinearMap.ker (deningerPlaceSum K) := by
  have hzero : deningerPlaceSum L g = 0 := hg
  show deningerPlaceSum K (deningerPlacePush K L g) = 0
  rw [deningerPlacePush_sum, hzero]

end PlaceProjection

end RHTower
