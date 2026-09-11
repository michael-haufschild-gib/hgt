import GaloisForLFunctions.HTGeometry.KukolTubeProductGeometry

/-!
# Actual subgroup orbit quotients and simultaneous future-tube domains

For every complex linear subgroup of Kukol's unipotent group, the orbit
projection is continuous, open and surjective. Its fibers are exactly the
genuine simultaneous orbits, and its topological quotient is an explicit
quotient-vector/slice product. Finite simultaneous future tubes descend to
open domains in this model, with an exact orbit-intersection criterion.
These are topological and coordinate conclusions; no global Stein theorem
is assumed or asserted.
-/

noncomputable section
namespace GaloisForLFunctions.HTGeometry
open scoped BigOperators
open Topology
variable {κ ι : Type*} [Fintype κ]

/-- The natural projection to subgroup quotient coordinates and the canonical slice. -/
def kukolSubgroupOrbitProjection (W : Submodule ℂ (κ → ℂ)) (anchor : ι) :
    C((ι → KukolRegularPoint κ),((κ → ℂ) ⧸ W) × KukolDiagonalSlice (κ := κ) anchor) where
  toFun x := (W.mkQ (kukolDiagonalGauge anchor x),
    ⟨kukolDiagonalNormalize anchor x,kukolDiagonalNormalize_anchor anchor x⟩)
  continuous_toFun := (W.continuous_mkQ.comp (continuous_kukolDiagonalGauge anchor)).prodMk
    ((continuous_kukolDiagonalNormalize anchor).subtype_mk (kukolDiagonalNormalize_anchor anchor))

/-- The proposed subgroup quotient coordinates have exactly the genuine orbit fibers. -/
theorem kukolSubgroupOrbitProjection_eq_iff (W : Submodule ℂ (κ → ℂ)) (anchor : ι)
    (x y : ι → KukolRegularPoint κ) :
    kukolSubgroupOrbitProjection W anchor x=kukolSubgroupOrbitProjection W anchor y ↔
      ∃ u : W,∀ j,kukolRegularAction u.val (x j)=y j := by
  rw [kukolSubgroup_orbit_iff]
  change (W.mkQ (kukolDiagonalGauge anchor x),
      (⟨kukolDiagonalNormalize anchor x,kukolDiagonalNormalize_anchor anchor x⟩ : KukolDiagonalSlice anchor)) =
    (W.mkQ (kukolDiagonalGauge anchor y),
      (⟨kukolDiagonalNormalize anchor y,kukolDiagonalNormalize_anchor anchor y⟩ : KukolDiagonalSlice anchor)) ↔
      (kukolDiagonalInvariants anchor x,(Submodule.Quotient.mk (kukolDiagonalGauge anchor x) : (κ → ℂ) ⧸ W)) =
      (kukolDiagonalInvariants anchor y,(Submodule.Quotient.mk (kukolDiagonalGauge anchor y) : (κ → ℂ) ⧸ W))
  simp only [Prod.mk.injEq,Subtype.mk.injEq,kukolDiagonalNormalize_eq_iff]
  exact and_comm

/-- The orbit projection is open; quotient coordinates carry their ordinary product topology. -/
theorem isOpenMap_kukolSubgroupOrbitProjection (W : Submodule ℂ (κ → ℂ)) (anchor : ι) :
    IsOpenMap (kukolSubgroupOrbitProjection W anchor) := by
  change IsOpenMap (Prod.map W.mkQ id ∘ kukolDiagonalOrbitHomeomorph anchor)
  exact (W.isOpenMap_mkQ.prodMap IsOpenMap.id).comp (kukolDiagonalOrbitHomeomorph anchor).isOpenMap

/-- Every quotient/slice pair is attained by an actual regular family. -/
theorem kukolSubgroupOrbitProjection_surjective (W : Submodule ℂ (κ → ℂ)) (anchor : ι) :
    Function.Surjective (kukolSubgroupOrbitProjection W anchor) := by
  rintro ⟨q,s⟩
  obtain ⟨u,hu⟩ := W.mkQ_surjective q
  refine ⟨(kukolDiagonalOrbitHomeomorph anchor).symm (u,s),?_⟩
  change Prod.map W.mkQ id ((kukolDiagonalOrbitHomeomorph anchor)
    ((kukolDiagonalOrbitHomeomorph anchor).symm (u,s)))=(q,s)
  rw [Homeomorph.apply_symm_apply]
  simp only [Prod.map_apply,hu,id_eq]

/-- The orbit map is a topological quotient map, with no missing quotient-topology assumption. -/
theorem isQuotientMap_kukolSubgroupOrbitProjection (W : Submodule ℂ (κ → ℂ)) (anchor : ι) :
    IsQuotientMap (kukolSubgroupOrbitProjection W anchor) :=
  (isOpenMap_kukolSubgroupOrbitProjection W anchor).isQuotientMap
    (kukolSubgroupOrbitProjection W anchor).continuous (kukolSubgroupOrbitProjection_surjective W anchor)

/-- The actual orbit quotient, with its quotient topology, is the explicit quotient-vector/slice product. -/
def kukolSubgroupOrbitQuotientHomeomorph (W : Submodule ℂ (κ → ℂ)) (anchor : ι) :
    Quotient (Setoid.ker (kukolSubgroupOrbitProjection W anchor)) ≃ₜ
      ((κ → ℂ) ⧸ W) × KukolDiagonalSlice (κ := κ) anchor :=
  (isQuotientMap_kukolSubgroupOrbitProjection W anchor).homeomorph

/-- Future-tube margins are continuous in the same raw complex coordinates. -/
@[fun_prop] theorem continuous_kukolRegularImaginaryMargin :
    Continuous (kukolRegularImaginaryMargin (κ := κ)) := by
  unfold kukolRegularImaginaryMargin
  fun_prop

/-- The strict future tube is open in the regular complex coordinate chart. -/
theorem isOpen_kukolRegularFutureTube : IsOpen (kukolRegularFutureTube (κ := κ)) := by
  change IsOpen ({x : KukolRegularPoint κ | 0 < (x.minus : ℂ).im} ∩
    {x | 0 < kukolRegularImaginaryMargin x})
  exact (isOpen_lt continuous_const
    (Complex.continuous_im.comp (Units.continuous_val.comp continuous_kukolRegularMinus))).inter
      (isOpen_lt continuous_const continuous_kukolRegularImaginaryMargin)

/-- The quotient domain of simultaneous future-tube points in the paper's subgroup setting. -/
def kukolSubgroupTubeQuotientDomain (W : Submodule ℂ (κ → ℂ)) (anchor : ι) :=
  kukolSubgroupOrbitProjection W anchor '' {x : ι → KukolRegularPoint κ | ∀ j,x j ∈ kukolRegularFutureTube}

/-- For finite simultaneous families, the tube quotient is an open domain in the explicit orbit model. -/
theorem isOpen_kukolSubgroupTubeQuotientDomain [Fintype ι]
    (W : Submodule ℂ (κ → ℂ)) (anchor : ι) :
    IsOpen (kukolSubgroupTubeQuotientDomain W anchor) := by
  apply isOpenMap_kukolSubgroupOrbitProjection W anchor
  simp only [Set.setOf_forall]
  exact isOpen_iInter_of_finite fun j => isOpen_kukolRegularFutureTube.preimage (continuous_apply j)

/-- Membership in that quotient domain is exactly meeting the full simultaneous future tube along the subgroup orbit. -/
theorem kukolSubgroupTubeQuotientDomain_mem_iff (W : Submodule ℂ (κ → ℂ)) (anchor : ι)
    (x : ι → KukolRegularPoint κ) :
    kukolSubgroupOrbitProjection W anchor x ∈ kukolSubgroupTubeQuotientDomain W anchor ↔
      ∃ u : W,∀ j,kukolRegularAction u.val (x j) ∈ kukolRegularFutureTube := by
  constructor
  · rintro ⟨y,hy,he⟩
    obtain ⟨u,hu⟩ := (kukolSubgroupOrbitProjection_eq_iff W anchor x y).mp he.symm
    exact ⟨u,fun j => (hu j).symm ▸ hy j⟩
  · rintro ⟨u,hu⟩
    refine ⟨fun j => kukolRegularAction u.val (x j),hu,?_⟩
    symm
    exact (kukolSubgroupOrbitProjection_eq_iff W anchor x _).mpr ⟨u,fun _ => rfl⟩

end GaloisForLFunctions.HTGeometry
