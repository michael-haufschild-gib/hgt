import GaloisForLFunctions.HTGeometry.PseudoDiffOpAutomorphism

/-!
# Valuation lattices in the completed pseudodifferential skew field

This file constructs the actual finite-rank valuation lattices used by the differential
variational building.  A lattice is a finitely generated left module over the valuation ring whose
span over the completed skew field is the whole ambient vector space.  Differential coefficient
automorphisms act semilinearly on these lattices, functorially and without a choice of generators.
-/

open scoped Differential

namespace GaloisForLFunctions.HTGeometry

namespace DiffOp

noncomputable section

variable {K : Type u} [Field K] [Differential K]
variable {ι : Type*}

/-- The valuation-ring embedding into the completed pseudodifferential skew field, as a left-linear
map over the valuation ring. -/
def completedPseudoDiffOpIntegerEmbedding (K : Type u) [Field K] [Differential K] :
    CompletedPseudoDiffOpInteger (K := K) →ₗ[CompletedPseudoDiffOpInteger (K := K)]
      CompletedPseudoDiffOp K where
  toFun x := x
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- A finite-rank valuation lattice in the completed pseudodifferential vector space.  The
finiteness and full-span conditions are part of the object, rather than later side hypotheses. -/
structure CompletedPseudoDiffOpLattice (K : Type u) [Field K] [Differential K] (ι : Type*) where
  carrier : Submodule (CompletedPseudoDiffOpInteger (K := K)) (ι → CompletedPseudoDiffOp K)
  fg : carrier.FG
  full : Submodule.span (CompletedPseudoDiffOp K)
      (carrier : Set (ι → CompletedPseudoDiffOp K)) = ⊤

@[ext]
theorem CompletedPseudoDiffOpLattice.ext
    {L M : CompletedPseudoDiffOpLattice K ι} (h : L.carrier = M.carrier) : L = M := by
  cases L
  cases M
  simp_all

/-- Coordinatewise semilinear action on completed vectors, with scalar action restricted to the
valuation ring. -/
def mapCompletedPseudoIntegerVecLinearMap (σ : K ≃+* K)
    (hσ : ∀ a : K, σ (a′) = (σ a)′) :
    (ι → CompletedPseudoDiffOp K) →ₛₗ[(mapCompletedPseudoIntegerEquiv σ hσ).toRingHom]
      (ι → CompletedPseudoDiffOp K) where
  toFun v i := mapCompletedPseudoRingEquiv σ hσ (v i)
  map_add' v w := by
    funext i
    exact (mapCompletedPseudoRingEquiv σ hσ).map_add (v i) (w i)
  map_smul' c v := by
    funext i
    exact (mapCompletedPseudoRingEquiv σ hσ).map_mul (c : CompletedPseudoDiffOp K) (v i)

/-- Coordinatewise semilinear action over the completed pseudodifferential skew field. -/
def mapCompletedPseudoVecLinearMap (σ : K ≃+* K)
    (hσ : ∀ a : K, σ (a′) = (σ a)′) :
    (ι → CompletedPseudoDiffOp K) →ₛₗ[(mapCompletedPseudoRingEquiv σ hσ).toRingHom]
      (ι → CompletedPseudoDiffOp K) where
  toFun v i := mapCompletedPseudoRingEquiv σ hσ (v i)
  map_add' v w := by
    funext i
    exact (mapCompletedPseudoRingEquiv σ hσ).map_add (v i) (w i)
  map_smul' c v := by
    funext i
    exact (mapCompletedPseudoRingEquiv σ hσ).map_mul c (v i)

/-- Differential coefficient automorphisms transport full valuation lattices to full valuation
lattices. -/
def mapCompletedPseudoDiffOpLattice (σ : K ≃+* K)
    (hσ : ∀ a : K, σ (a′) = (σ a)′) (L : CompletedPseudoDiffOpLattice K ι) :
    CompletedPseudoDiffOpLattice K ι := by
  let eO := mapCompletedPseudoIntegerEquiv σ hσ
  let eD := mapCompletedPseudoRingEquiv σ hσ
  letI : RingHomSurjective eO.toRingHom := ⟨eO.surjective⟩
  letI : RingHomSurjective eD.toRingHom := ⟨eD.surjective⟩
  refine
    { carrier := L.carrier.map (mapCompletedPseudoIntegerVecLinearMap (ι := ι) σ hσ)
      fg := L.fg.map (mapCompletedPseudoIntegerVecLinearMap (ι := ι) σ hσ)
      full := ?_ }
  rw [Submodule.eq_top_iff']
  intro y
  let x : ι → CompletedPseudoDiffOp K := fun i =>
    mapCompletedPseudoRingEquiv σ.symm (symm_deriv_comm hσ) (y i)
  have hx : x ∈ Submodule.span (CompletedPseudoDiffOp K)
      (L.carrier : Set (ι → CompletedPseudoDiffOp K)) := by
    rw [L.full]
    trivial
  have himage : mapCompletedPseudoVecLinearMap (ι := ι) σ hσ x ∈
      Submodule.map (mapCompletedPseudoVecLinearMap (ι := ι) σ hσ)
        (Submodule.span (CompletedPseudoDiffOp K)
          (L.carrier : Set (ι → CompletedPseudoDiffOp K))) := ⟨x, hx, rfl⟩
  rw [Submodule.map_span] at himage
  have hsubset : mapCompletedPseudoVecLinearMap (ι := ι) σ hσ ''
        (L.carrier : Set (ι → CompletedPseudoDiffOp K)) ⊆
      (L.carrier.map (mapCompletedPseudoIntegerVecLinearMap (ι := ι) σ hσ) :
        Set (ι → CompletedPseudoDiffOp K)) := by
    rintro _ ⟨z, hz, rfl⟩
    exact ⟨z, hz, rfl⟩
  have hy := Submodule.span_mono hsubset himage
  have heq : mapCompletedPseudoVecLinearMap (ι := ι) σ hσ x = y := by
    funext i
    exact (mapCompletedPseudoRingEquiv σ hσ).right_inv (y i)
  rwa [heq] at hy

theorem mem_mapCompletedPseudoDiffOpLattice_iff (σ : K ≃+* K)
    (hσ : ∀ a : K, σ (a′) = (σ a)′) (L : CompletedPseudoDiffOpLattice K ι)
    (y : ι → CompletedPseudoDiffOp K) :
    y ∈ (mapCompletedPseudoDiffOpLattice σ hσ L).carrier ↔
      ∃ x ∈ L.carrier, mapCompletedPseudoIntegerVecLinearMap (ι := ι) σ hσ x = y := by
  let eO := mapCompletedPseudoIntegerEquiv σ hσ
  letI : RingHomSurjective eO.toRingHom := ⟨eO.surjective⟩
  change y ∈ L.carrier.map (mapCompletedPseudoIntegerVecLinearMap (ι := ι) σ hσ) ↔ _
  constructor <;> rintro ⟨x, hx, rfl⟩ <;> exact ⟨x, hx, rfl⟩

/-- Identity coefficient automorphism acts trivially on valuation lattices. -/
theorem mapCompletedPseudoDiffOpLattice_refl (L : CompletedPseudoDiffOpLattice K ι) :
    mapCompletedPseudoDiffOpLattice (RingEquiv.refl K) refl_deriv_comm L = L := by
  apply CompletedPseudoDiffOpLattice.ext
  ext y
  rw [mem_mapCompletedPseudoDiffOpLattice_iff]
  constructor
  · rintro ⟨x, hx, rfl⟩
    have heq : mapCompletedPseudoIntegerVecLinearMap (ι := ι) (RingEquiv.refl K)
        refl_deriv_comm x = x := by
      funext i
      exact DFunLike.congr_fun (mapCompletedPseudoRingEquiv_refl (K := K)) (x i)
    rwa [heq]
  · intro hy
    refine ⟨y, hy, ?_⟩
    funext i
    exact DFunLike.congr_fun (mapCompletedPseudoRingEquiv_refl (K := K)) (y i)

/-- Coefficient transport of valuation lattices respects composition. -/
theorem mapCompletedPseudoDiffOpLattice_trans (σ τ : K ≃+* K)
    (hσ : ∀ a : K, σ (a′) = (σ a)′)
    (hτ : ∀ a : K, τ (a′) = (τ a)′) (L : CompletedPseudoDiffOpLattice K ι) :
    mapCompletedPseudoDiffOpLattice τ hτ (mapCompletedPseudoDiffOpLattice σ hσ L) =
      mapCompletedPseudoDiffOpLattice (σ.trans τ) (trans_deriv_comm σ τ hσ hτ) L := by
  apply CompletedPseudoDiffOpLattice.ext
  ext y
  simp only [mem_mapCompletedPseudoDiffOpLattice_iff]
  constructor
  · rintro ⟨z, ⟨x, hx, hzx⟩, hyz⟩
    refine ⟨x, hx, ?_⟩
    rw [← hyz, ← hzx]
    funext i
    exact (DFunLike.congr_fun (mapCompletedPseudoRingEquiv_trans σ τ hσ hτ) (x i)).symm
  · rintro ⟨x, hx, hyx⟩
    let z := mapCompletedPseudoIntegerVecLinearMap (ι := ι) σ hσ x
    refine ⟨z, ⟨x, hx, rfl⟩, ?_⟩
    rw [← hyx]
    funext i
    exact DFunLike.congr_fun (mapCompletedPseudoRingEquiv_trans σ τ hσ hτ) (x i)

variable [Fintype ι]

/-- Coordinatewise integral vectors in the completed pseudodifferential vector space. -/
def completedPseudoDiffOpIntegralCarrier (K : Type u) [Field K] [Differential K] (ι : Type*) :
    Submodule (CompletedPseudoDiffOpInteger (K := K)) (ι → CompletedPseudoDiffOp K) :=
  Submodule.pi Set.univ
    (fun _ => LinearMap.range (completedPseudoDiffOpIntegerEmbedding K))

theorem completedPseudoDiffOpIntegralCarrier_fg :
    (completedPseudoDiffOpIntegralCarrier K ι).FG := by
  apply Submodule.fg_pi
  intro i
  rw [LinearMap.range_eq_map]
  exact Module.Finite.fg_top.map (completedPseudoDiffOpIntegerEmbedding K)

theorem basisFun_mem_completedPseudoDiffOpIntegralCarrier (i : ι) :
    Pi.basisFun (CompletedPseudoDiffOp K) ι i ∈
      completedPseudoDiffOpIntegralCarrier K ι := by
  intro j hj
  change (Pi.basisFun (CompletedPseudoDiffOp K) ι) i j ∈
    (completedPseudoDiffOpIntegerEmbedding K).range
  rw [LinearMap.mem_range]
  classical
  by_cases h : i = j
  · subst j
    exact ⟨1, by simp [completedPseudoDiffOpIntegerEmbedding]⟩
  · exact ⟨0, by simp [completedPseudoDiffOpIntegerEmbedding, h]⟩

theorem completedPseudoDiffOpIntegralCarrier_full :
    Submodule.span (CompletedPseudoDiffOp K)
      (completedPseudoDiffOpIntegralCarrier K ι : Set (ι → CompletedPseudoDiffOp K)) = ⊤ := by
  rw [Submodule.eq_top_iff']
  intro x
  rw [← (Pi.basisFun (CompletedPseudoDiffOp K) ι).sum_repr x]
  apply Submodule.sum_mem
  intro i hi
  apply Submodule.smul_mem
  exact Submodule.subset_span (basisFun_mem_completedPseudoDiffOpIntegralCarrier (K := K) i)

/-- Standard valuation lattice `O^ι` inside the completed skew vector space. -/
def standardCompletedPseudoDiffOpLattice : CompletedPseudoDiffOpLattice K ι where
  carrier := completedPseudoDiffOpIntegralCarrier K ι
  fg := completedPseudoDiffOpIntegralCarrier_fg
  full := completedPseudoDiffOpIntegralCarrier_full

/-- Coefficient automorphisms preserve the standard valuation lattice exactly. -/
theorem map_standardCompletedPseudoDiffOpLattice (σ : K ≃+* K)
    (hσ : ∀ a : K, σ (a′) = (σ a)′) :
    mapCompletedPseudoDiffOpLattice σ hσ
        (standardCompletedPseudoDiffOpLattice (K := K) (ι := ι)) =
      standardCompletedPseudoDiffOpLattice (K := K) (ι := ι) := by
  apply CompletedPseudoDiffOpLattice.ext
  ext y
  rw [mem_mapCompletedPseudoDiffOpLattice_iff]
  constructor
  · rintro ⟨x, hx, rfl⟩
    intro i hi
    change mapCompletedPseudoRingEquiv σ hσ (x i) ∈
      (completedPseudoDiffOpIntegerEmbedding K).range
    have hxi := hx i (Set.mem_univ i)
    change x i ∈ (completedPseudoDiffOpIntegerEmbedding K).range at hxi
    obtain ⟨c, hc⟩ := hxi
    refine ⟨mapCompletedPseudoIntegerEquiv σ hσ c, ?_⟩
    change (mapCompletedPseudoIntegerEquiv σ hσ c : CompletedPseudoDiffOp K) =
      mapCompletedPseudoRingEquiv σ hσ (x i)
    rw [mapCompletedPseudoIntegerEquiv_apply_coe, ← hc]
    rfl
  · intro hy
    let x : ι → CompletedPseudoDiffOp K := fun i =>
      mapCompletedPseudoRingEquiv σ.symm (symm_deriv_comm hσ) (y i)
    refine ⟨x, ?_, ?_⟩
    · intro i hi
      change x i ∈ (completedPseudoDiffOpIntegerEmbedding K).range
      have hyi := hy i (Set.mem_univ i)
      change y i ∈ (completedPseudoDiffOpIntegerEmbedding K).range at hyi
      obtain ⟨c, hc⟩ := hyi
      refine ⟨(mapCompletedPseudoIntegerEquiv σ hσ).symm c, ?_⟩
      change ((mapCompletedPseudoIntegerEquiv σ hσ).symm c : CompletedPseudoDiffOp K) =
        mapCompletedPseudoRingEquiv σ.symm (symm_deriv_comm hσ) (y i)
      rw [← hc]
      rfl
    · funext i
      exact (mapCompletedPseudoRingEquiv σ hσ).right_inv (y i)

end

end DiffOp

end GaloisForLFunctions.HTGeometry
