import GaloisForLFunctions.HTGeometry.TorusExteriorComparison
import GaloisForLFunctions.HTGeometry.ExteriorPowerDirectLimit
import Mathlib.Algebra.Colimit.Module

/-!
# The colimit of the cohomologies of a directed system of tori

A directed system of tori is a directed family of coordinate spaces with linear maps carrying the
period lattice into the period lattice and composing functorially.  Pullback makes the cohomology of
the tori a directed system of vector spaces, the exterior powers of the duals of the covering spaces
form another, and the comparison of one with the other is an isomorphism at every stage compatible
with the transition maps.  Therefore the direct limits are isomorphic: the cohomology of the
inverse limit of the tori, computed as the colimit of the cohomologies, is the exterior algebra of
the colimit of the lattices.

* `TorusCoverSystem` : a directed system of tori, given by their covering spaces.
* `torusCohomologyColimitEquiv` : the comparison is an isomorphism of direct limits.
-/

set_option maxSynthPendingDepth 3
set_option maxHeartbeats 1000000

namespace GaloisForLFunctions.HTGeometry

open exteriorPower Module

section System

/-- **A directed system of tori**, given by the covering spaces of the tori and the lifts of the
homomorphisms between them: linear maps carrying the period lattice into the period lattice and
composing functorially. -/
structure TorusCoverSystem (𝕜 : Type*) [RCLike 𝕜] (p : 𝕜) (ι : Type*) [Preorder ι] where
  /-- The dimension of the covering space of each torus. -/
  dim : ι → ℕ
  /-- The lift of the homomorphism of tori to the covering spaces. -/
  map : ∀ i j, i ≤ j → (Fin (dim j) → 𝕜) →L[𝕜] (Fin (dim i) → 𝕜)
  /-- The lift carries the period lattice into the period lattice. -/
  map_lattice : ∀ i j (h : i ≤ j) (l : Fin (dim j)),
    map i j h (p • (Pi.single l (1 : 𝕜) : Fin (dim j) → 𝕜)) ∈ periodLattice p (dim i)
  /-- The lift of the identity is the identity. -/
  map_self : ∀ i (h : i ≤ i), map i i h = ContinuousLinearMap.id 𝕜 (Fin (dim i) → 𝕜)
  /-- The lifts compose. -/
  map_trans : ∀ i j k (hij : i ≤ j) (hjk : j ≤ k),
    (map i j hij).comp (map j k hjk) = map i k (hij.trans hjk)

variable {𝕜 : Type*} [RCLike 𝕜] {p : 𝕜} {ι : Type*} [Preorder ι]

/-- The maps induced on cohomology by equal lifts agree. -/
theorem periodicCohomologyMap_congr {r s : ℕ} {T T' : (Fin r → 𝕜) →L[𝕜] (Fin s → 𝕜)}
    (hTT : T = T')
    (hT : ∀ l : Fin r, T (p • (Pi.single l (1 : 𝕜) : Fin r → 𝕜)) ∈ periodLattice p s)
    (hT' : ∀ l : Fin r, T' (p • (Pi.single l (1 : 𝕜) : Fin r → 𝕜)) ∈ periodLattice p s)
    (n : ℕ) : periodicCohomologyMap p T hT n = periodicCohomologyMap p T' hT' n := by
  subst hTT
  rfl

/-- The transition maps of the directed system of cohomologies. -/
noncomputable def torusCohomologyTransition (S : TorusCoverSystem 𝕜 p ι) (n : ℕ) (i j : ι)
    (h : i ≤ j) : periodicCohomology p (S.dim i) n →ₗ[𝕜] periodicCohomology p (S.dim j) n :=
  periodicCohomologyMap p (S.map i j h) (S.map_lattice i j h) n

/-- The transition maps of the directed system of exterior powers of the duals. -/
noncomputable def torusExteriorTransition (S : TorusCoverSystem 𝕜 p ι) (n : ℕ) (i j : ι)
    (h : i ≤ j) :
    ⋀[𝕜]^(n + 1) (Module.Dual 𝕜 (Fin (S.dim i) → 𝕜)) →ₗ[𝕜]
      ⋀[𝕜]^(n + 1) (Module.Dual 𝕜 (Fin (S.dim j) → 𝕜)) :=
  exteriorPower.map (n + 1)
    ((S.map i j h : (Fin (S.dim j) → 𝕜) →ₗ[𝕜] (Fin (S.dim i) → 𝕜)).dualMap)

instance (S : TorusCoverSystem 𝕜 p ι) (n : ℕ) :
    DirectedSystem (fun i => periodicCohomology p (S.dim i) n)
      (fun i j h => torusCohomologyTransition S n i j h) where
  map_self := by
    intro i x
    have hid := periodicCohomologyMap_congr (S.map_self i le_rfl)
      (S.map_lattice i i le_rfl)
      (fun l => by
        rw [ContinuousLinearMap.id_apply]
        exact periodVector_mem_periodLattice p l) n
    show torusCohomologyTransition S n i i le_rfl x = x
    rw [torusCohomologyTransition, hid, periodicCohomologyMap_id]
    rfl
  map_map := by
    intro k j i hij hjk x
    have hcomp := periodicCohomologyMap_comp (S.map i j hij) (S.map j k hjk)
      (S.map_lattice i j hij) (S.map_lattice j k hjk)
      (fun l => by
        show (S.map i j hij) ((S.map j k hjk)
          (p • (Pi.single l (1 : 𝕜) : Fin (S.dim k) → 𝕜))) ∈ _
        exact map_periodLattice (S.map i j hij) (S.map_lattice i j hij)
          (S.map_lattice j k hjk l)) n
    show torusCohomologyTransition S n j k hjk (torusCohomologyTransition S n i j hij x) =
      torusCohomologyTransition S n i k (hij.trans hjk) x
    rw [torusCohomologyTransition, torusCohomologyTransition, torusCohomologyTransition,
      periodicCohomologyMap_congr (S.map_trans i j k hij hjk) _
        (S.map_lattice i k (hij.trans hjk)) n] at *
    rw [hcomp]
    rfl

instance (S : TorusCoverSystem 𝕜 p ι) (n : ℕ) :
    DirectedSystem (fun i => ⋀[𝕜]^(n + 1) (Module.Dual 𝕜 (Fin (S.dim i) → 𝕜)))
      (fun i j h => torusExteriorTransition S n i j h) where
  map_self := by
    intro i x
    show torusExteriorTransition S n i i le_rfl x = x
    rw [torusExteriorTransition, S.map_self i le_rfl]
    show exteriorPower.map (n + 1)
      ((ContinuousLinearMap.id 𝕜 (Fin (S.dim i) → 𝕜) :
        (Fin (S.dim i) → 𝕜) →ₗ[𝕜] (Fin (S.dim i) → 𝕜)).dualMap) x = x
    rw [show ((ContinuousLinearMap.id 𝕜 (Fin (S.dim i) → 𝕜) :
        (Fin (S.dim i) → 𝕜) →ₗ[𝕜] (Fin (S.dim i) → 𝕜)).dualMap) =
      LinearMap.id from rfl, exteriorPower.map_id]
    rfl
  map_map := by
    intro k j i hij hjk x
    show torusExteriorTransition S n j k hjk (torusExteriorTransition S n i j hij x) =
      torusExteriorTransition S n i k (hij.trans hjk) x
    rw [torusExteriorTransition, torusExteriorTransition, torusExteriorTransition,
      ← S.map_trans i j k hij hjk]
    show exteriorPower.map (n + 1) _ (exteriorPower.map (n + 1) _ x) = _
    rw [← LinearMap.comp_apply, ← exteriorPower.map_comp]
    rfl

end System

section Colimit

variable {𝕜 : Type*} [RCLike 𝕜] {p : 𝕜} {ι : Type*} [Preorder ι] [DecidableEq ι]

/-- **The comparison of the cohomology of a torus with the exterior power of the dual of its
covering space passes to the colimit**: for a directed system of tori, the direct limit of the
cohomologies is the direct limit of the exterior powers. -/
noncomputable def torusCohomologyColimitEquiv (S : TorusCoverSystem 𝕜 p ι) (hp : p ≠ 0) (n : ℕ) :
    Module.DirectLimit (fun i => ⋀[𝕜]^(n + 1) (Module.Dual 𝕜 (Fin (S.dim i) → 𝕜)))
        (torusExteriorTransition S n) ≃ₗ[𝕜]
      Module.DirectLimit (fun i => periodicCohomology p (S.dim i) n)
        (torusCohomologyTransition S n) :=
  Module.DirectLimit.congr (fun i => periodicCohomologyDualEquiv hp (S.dim i) n)
    (fun i j h => LinearMap.ext fun x =>
      (periodicCohomologyDualEquiv_naturality hp (S.map i j h) (S.map_lattice i j h) n x).symm)

theorem torusCohomologyColimitEquiv_of (S : TorusCoverSystem 𝕜 p ι) (hp : p ≠ 0) (n : ℕ) (i : ι)
    (x : ⋀[𝕜]^(n + 1) (Module.Dual 𝕜 (Fin (S.dim i) → 𝕜))) :
    torusCohomologyColimitEquiv S hp n
        (Module.DirectLimit.of 𝕜 ι _ (torusExteriorTransition S n) i x) =
      Module.DirectLimit.of 𝕜 ι _ (torusCohomologyTransition S n) i
        (periodicCohomologyDualEquiv hp (S.dim i) n x) :=
  Module.DirectLimit.congr_apply_of _ _ _

/-- The directed system of the duals of the covering spaces. -/
instance dualCoverDirectedSystem (S : TorusCoverSystem 𝕜 p ι) :
    DirectedSystem (fun i => Module.Dual 𝕜 (Fin (S.dim i) → 𝕜))
      (fun i j h => ((S.map i j h : (Fin (S.dim j) → 𝕜) →ₗ[𝕜] (Fin (S.dim i) → 𝕜)).dualMap)) where
  map_self := by
    intro i x
    have h : ∀ v : Fin (S.dim i) → 𝕜,
        ((S.map i i le_rfl : (Fin (S.dim i) → 𝕜) →ₗ[𝕜] (Fin (S.dim i) → 𝕜)).dualMap x) v =
          x v := by
      intro v
      rw [S.map_self i le_rfl]
      rfl
    exact LinearMap.ext h
  map_map := by
    intro k j i hij hjk x
    have h : ∀ v : Fin (S.dim k) → 𝕜,
        (((S.map j k hjk : (Fin (S.dim k) → 𝕜) →ₗ[𝕜] (Fin (S.dim j) → 𝕜)).dualMap)
            (((S.map i j hij : (Fin (S.dim j) → 𝕜) →ₗ[𝕜] (Fin (S.dim i) → 𝕜)).dualMap) x)) v =
          (((S.map i k (hij.trans hjk) :
            (Fin (S.dim k) → 𝕜) →ₗ[𝕜] (Fin (S.dim i) → 𝕜)).dualMap) x) v := by
      intro v
      rw [← S.map_trans i j k hij hjk]
      rfl
    exact LinearMap.ext h

/-- **The colimit of the cohomologies of a directed system of tori is the exterior power of the
colimit of the duals of the covering spaces.**  This is the comparison of the exterior algebra of
the colimit of the lattices with the cohomology of the inverse limit of the tori, computed as the
colimit of the cohomologies. -/
noncomputable def torusCohomologyColimitExteriorEquiv [IsDirectedOrder ι] [Nonempty ι]
    (S : TorusCoverSystem 𝕜 p ι) (hp : p ≠ 0) (n : ℕ)
    (hsurj : ∀ i j (h : i ≤ j), Function.Surjective (S.map i j h)) :
    ⋀[𝕜]^(n + 1) (Module.DirectLimit (fun i => Module.Dual 𝕜 (Fin (S.dim i) → 𝕜))
        (fun i j h => ((S.map i j h : (Fin (S.dim j) → 𝕜) →ₗ[𝕜] (Fin (S.dim i) → 𝕜)).dualMap)))
        ≃ₗ[𝕜]
      Module.DirectLimit (fun i => periodicCohomology p (S.dim i) n)
        (torusCohomologyTransition S n) :=
  (exteriorPowerDirectLimitEquiv (K := 𝕜) (ι := ι)
      (fun i => Module.Dual 𝕜 (Fin (S.dim i) → 𝕜))
      (fun i j h => ((S.map i j h : (Fin (S.dim j) → 𝕜) →ₗ[𝕜] (Fin (S.dim i) → 𝕜)).dualMap))
      (n + 1)
      (fun i j h => LinearMap.dualMap_injective_of_surjective (hsurj i j h))).symm.trans
    (torusCohomologyColimitEquiv S hp n)

end Colimit

section Example

variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} [Preorder ι]

theorem castLE_injective {a b : ℕ} (h : a ≤ b) : Function.Injective (Fin.castLE h) := by
  intro x y hxy
  have hval : ((Fin.castLE h x : Fin b) : ℕ) = ((Fin.castLE h y : Fin b) : ℕ) :=
    congrArg Fin.val hxy
  exact Fin.ext hval

/-- The lift of a projection of tori: restriction of a coordinate tuple along the inclusion of an
initial segment. -/
noncomputable def coordProjection {a b : ℕ} (h : a ≤ b) :
    (Fin b → 𝕜) →L[𝕜] (Fin a → 𝕜) :=
  ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj (Fin.castLE h i)

@[simp]
theorem coordProjection_apply {a b : ℕ} (h : a ≤ b) (x : Fin b → 𝕜) (i : Fin a) :
    coordProjection h x i = x (Fin.castLE h i) := rfl

/-- **The tower of tori of a monotone family of dimensions**, with the coordinate projections as the
lifts: a directed system of tori in which every map is surjective, so the comparison of the colimit
of the cohomologies with the exterior power of the colimit applies. -/
noncomputable def coordProjectionSystem (p : 𝕜) (d : ι → ℕ) (hd : ∀ i j, i ≤ j → d i ≤ d j) :
    TorusCoverSystem 𝕜 p ι where
  dim := d
  map i j h := coordProjection (hd i j h)
  map_lattice := by
    classical
    intro i j h l
    by_cases hl : ∃ a : Fin (d i), Fin.castLE (hd i j h) a = l
    · obtain ⟨a, rfl⟩ := hl
      have hval : coordProjection (𝕜 := 𝕜) (hd i j h)
          (p • (Pi.single (Fin.castLE (hd i j h) a) (1 : 𝕜) : Fin (d j) → 𝕜)) =
          p • (Pi.single a (1 : 𝕜) : Fin (d i) → 𝕜) := by
        funext b
        show p * (Pi.single (Fin.castLE (hd i j h) a) (1 : 𝕜) : Fin (d j) → 𝕜)
            (Fin.castLE (hd i j h) b) = p * (Pi.single a (1 : 𝕜) : Fin (d i) → 𝕜) b
        rw [Pi.single_apply, Pi.single_apply]
        by_cases hab : b = a
        · rw [if_pos hab, if_pos (congrArg (Fin.castLE (hd i j h)) hab)]
        · rw [if_neg hab, if_neg fun hc => hab (castLE_injective (hd i j h) hc)]
      rw [hval]
      exact periodVector_mem_periodLattice p a
    · have hval : coordProjection (𝕜 := 𝕜) (hd i j h)
          (p • (Pi.single l (1 : 𝕜) : Fin (d j) → 𝕜)) = 0 := by
        funext b
        show p * (Pi.single l (1 : 𝕜) : Fin (d j) → 𝕜) (Fin.castLE (hd i j h) b) = 0
        rw [Pi.single_apply, if_neg fun hc => hl ⟨b, hc⟩, mul_zero]
      rw [hval]
      exact zero_mem _
  map_self := by
    intro i h
    refine ContinuousLinearMap.ext fun x => ?_
    funext a
    show x (Fin.castLE (hd i i h) a) = x a
    rw [show Fin.castLE (hd i i h) a = a from Fin.ext rfl]
  map_trans := by
    intro i j k hij hjk
    refine ContinuousLinearMap.ext fun x => ?_
    funext a
    show x (Fin.castLE (hd j k hjk) (Fin.castLE (hd i j hij) a)) =
      x (Fin.castLE (hd i k (hij.trans hjk)) a)
    rw [show Fin.castLE (hd j k hjk) (Fin.castLE (hd i j hij) a) =
      Fin.castLE (hd i k (hij.trans hjk)) a from Fin.ext rfl]

theorem coordProjection_surjective {a b : ℕ} (h : a ≤ b) :
    Function.Surjective (coordProjection (𝕜 := 𝕜) h) := by
  classical
  intro y
  refine ⟨fun c => if hc : ∃ i : Fin a, Fin.castLE h i = c then y hc.choose else 0, ?_⟩
  funext i
  show (if hc : ∃ i' : Fin a, Fin.castLE h i' = Fin.castLE h i then y hc.choose else 0) = y i
  have hex : ∃ i' : Fin a, Fin.castLE h i' = Fin.castLE h i := ⟨i, rfl⟩
  rw [dif_pos hex]
  exact congrArg y (castLE_injective h hex.choose_spec)

theorem coordProjectionSystem_surjective (p : 𝕜) (d : ι → ℕ) (hd : ∀ i j, i ≤ j → d i ≤ d j)
    (i j : ι) (h : i ≤ j) :
    Function.Surjective ((coordProjectionSystem p d hd).map i j h) :=
  coordProjection_surjective (hd i j h)

end Example

end GaloisForLFunctions.HTGeometry
