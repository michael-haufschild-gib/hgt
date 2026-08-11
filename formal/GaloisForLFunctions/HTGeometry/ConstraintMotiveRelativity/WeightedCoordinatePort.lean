import GaloisForLFunctions.HTGeometry.ConstraintMotiveRelativity.CofinalInverseCapacityHilbert
import GaloisForLFunctions.HTGeometry.ConstraintMotiveRelativity.LatticeDirectionCapacity
import Mathlib

/-!
# Weighted coordinate ports and their Gram operators

Given a family of directions `dir : J → Y` in a finite-dimensional real inner product space and
weights `wt : J → ℝ`, the **weighted coordinate port** is the partially defined map

`T : ℓ²(J) →ₗ. Y`,  `T (∑ t_j e_j) = ∑ t_j · wt j · dir j`,

defined on the finitely supported vectors.  Restricted to the coordinate stage of a finite set `F`
its Gram operator is the finite sum of rank-one operators

`T_F T_F^* = ∑_{j ∈ F} (wt j)² · dir j ⊗ dir j`.

Every increasing chart built from finitely many marked directions with nondecreasing weights is
therefore literally a Gram family of a nested surjective finite-dimensional port tower.
-/

open Filter GaloisForLFunctions.HTGeometry
open scoped Topology RealInnerProductSpace

namespace HTGeometry.ConstraintMotiveRelativity

section WeightedPort

variable {Y : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y]
variable {J : Type*} [DecidableEq J]

/-- The coordinate Hilbert space of a weighted port. -/
abbrev PortCoord (J : Type*) : Type _ := lp (fun _ : J => ℝ) 2

/-- The standard coordinate vector. -/
noncomputable def portBasis (j : J) : PortCoord J := lp.single 2 j (1 : ℝ)

theorem portBasis_apply (i j : J) : (portBasis j : J → ℝ) i = if i = j then 1 else 0 := by
  rw [portBasis, lp.single_apply]
  simp [Pi.single_apply]

theorem inner_portBasis (i j : J) :
    ⟪portBasis i, portBasis j⟫ = if i = j then (1 : ℝ) else 0 := by
  rw [portBasis, lp.inner_single_left, portBasis_apply]
  by_cases h : i = j
  · simp [h]
  · simp [h]

theorem orthonormal_portBasis : Orthonormal ℝ (portBasis : J → PortCoord J) := by
  rw [orthonormal_iff_ite]
  intro i j
  rw [inner_portBasis]

/-- Finitely supported coordinate vectors. -/
noncomputable def portEmb : (J →₀ ℝ) →ₗ[ℝ] PortCoord J :=
  Finsupp.linearCombination ℝ portBasis

theorem portEmb_injective : Function.Injective (portEmb (J := J)) :=
  Orthonormal.linearIndependent orthonormal_portBasis

theorem portEmb_single (j : J) (t : ℝ) : portEmb (Finsupp.single j t) = t • portBasis j := by
  simp [portEmb]

variable (dir : J → Y) (wt : J → ℝ)

/-- The mass map of a weighted coordinate family. -/
noncomputable def portMass : (J →₀ ℝ) →ₗ[ℝ] Y :=
  Finsupp.lsum ℝ fun j => LinearMap.toSpanSingleton ℝ Y (wt j • dir j)

omit [FiniteDimensional ℝ Y] [DecidableEq J] in
@[simp] theorem portMass_single (j : J) (t : ℝ) :
    portMass dir wt (Finsupp.single j t) = t • (wt j • dir j) := by
  simp [portMass]

/-- The **weighted coordinate port**. -/
noncomputable def weightedPort : PortCoord J →ₗ.[ℝ] Y where
  domain := LinearMap.range (portEmb (J := J))
  toFun := portMass dir wt ∘ₗ
    (LinearEquiv.ofInjective _ (portEmb_injective (J := J))).symm.toLinearMap

omit [FiniteDimensional ℝ Y] in
@[simp] theorem weightedPort_domain :
    (weightedPort dir wt).domain = LinearMap.range (portEmb (J := J)) := rfl

omit [FiniteDimensional ℝ Y] in
theorem weightedPort_apply (l : J →₀ ℝ)
    (hmem : portEmb (J := J) l ∈ LinearMap.range (portEmb (J := J))) :
    weightedPort dir wt ⟨portEmb l, hmem⟩ = portMass dir wt l := by
  have hval : (LinearEquiv.ofInjective _ (portEmb_injective (J := J))) l
      = (⟨portEmb (J := J) l, hmem⟩ : LinearMap.range (portEmb (J := J))) := Subtype.ext rfl
  have hsymm : (LinearEquiv.ofInjective _ (portEmb_injective (J := J))).symm
      (⟨portEmb (J := J) l, hmem⟩ : LinearMap.range (portEmb (J := J))) = l := by
    rw [← hval, LinearEquiv.symm_apply_apply]
  exact congrArg (portMass dir wt) hsymm

omit [FiniteDimensional ℝ Y] in
theorem portBasis_mem_domain (j : J) :
    portBasis j ∈ (weightedPort dir wt).domain :=
  ⟨Finsupp.single j 1, by rw [portEmb_single, one_smul]⟩

omit [FiniteDimensional ℝ Y] in
theorem weightedPort_portBasis (j : J) :
    weightedPort dir wt ⟨portBasis j, portBasis_mem_domain dir wt j⟩ = wt j • dir j := by
  have hmem : portEmb (J := J) (Finsupp.single j 1)
      ∈ LinearMap.range (portEmb (J := J)) := ⟨Finsupp.single j 1, rfl⟩
  have hval := weightedPort_apply dir wt (Finsupp.single j 1) hmem
  have hcoe : portEmb (J := J) (Finsupp.single j (1 : ℝ)) = portBasis j := by
    rw [portEmb_single, one_smul]
  simp only [hcoe] at hval
  rw [hval, portMass_single, one_smul]

/-- The coordinate stage of a finite index set. -/
noncomputable def portStage (F : Finset J) : Submodule ℝ (PortCoord J) :=
  Submodule.span ℝ (portBasis '' (F : Set J))

instance portStage_finiteDimensional (F : Finset J) :
    FiniteDimensional ℝ (portStage (J := J) F) :=
  FiniteDimensional.span_of_finite ℝ ((F : Set J).toFinite.image _)

omit [FiniteDimensional ℝ Y] in
theorem portStage_le (F : Finset J) : portStage (J := J) F ≤ (weightedPort dir wt).domain := by
  rw [portStage]
  refine Submodule.span_le.2 ?_
  rintro _ ⟨j, -, rfl⟩
  exact portBasis_mem_domain dir wt j

/-- The co-lift witness of the weighted coordinate port at a finite stage. -/
noncomputable def portWitness (F : Finset J) (z : Y) : J →₀ ℝ :=
  ∑ j ∈ F, Finsupp.single j (wt j * ⟪dir j, z⟫)

omit [FiniteDimensional ℝ Y] in
theorem portEmb_portWitness (F : Finset J) (z : Y) :
    portEmb (J := J) (portWitness dir wt F z)
      = ∑ j ∈ F, (wt j * ⟪dir j, z⟫) • portBasis j := by
  rw [portWitness, map_sum]
  exact Finset.sum_congr rfl fun j _ => portEmb_single j _

omit [FiniteDimensional ℝ Y] in
theorem portWitness_mem_stage (F : Finset J) (z : Y) :
    portEmb (J := J) (portWitness dir wt F z) ∈ portStage (J := J) F := by
  rw [portEmb_portWitness, portStage]
  exact Submodule.sum_mem _ fun j hj =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, hj, rfl⟩)

omit [FiniteDimensional ℝ Y] in
theorem inner_portEmb_portWitness_portBasis (F : Finset J) (z : Y) {k : J} (hk : k ∈ F) :
    ⟪portEmb (J := J) (portWitness dir wt F z), portBasis k⟫ = wt k * ⟪dir k, z⟫ := by
  rw [portEmb_portWitness, sum_inner]
  rw [Finset.sum_eq_single k]
  · rw [real_inner_smul_left, inner_portBasis, if_pos rfl, mul_one]
  · intro j _ hjk
    rw [real_inner_smul_left, inner_portBasis, if_neg hjk, mul_zero]
  · intro h
    exact absurd hk h

/-- **The Gram operator of a weighted coordinate stage.** -/
theorem portGram_portStage (F : Finset J) (z : Y) :
    portGram (weightedPort dir wt) (portStage (J := J) F) (portStage_le dir wt F) z
      = ∑ j ∈ F, ((wt j) ^ 2 * ⟪dir j, z⟫) • dir j := by
  set uv : PortCoord J := portEmb (J := J) (portWitness dir wt F z) with huv
  set u : (weightedPort dir wt).domain := ⟨uv, ⟨portWitness dir wt F z, rfl⟩⟩ with hu
  have humem : ((u : (weightedPort dir wt).domain) : PortCoord J) ∈ portStage (J := J) F :=
    portWitness_mem_stage dir wt F z
  have hgen : ∀ (y : PortCoord J) (hy : y ∈ portStage (J := J) F),
      ⟪uv, y⟫ = ⟪z, weightedPort dir wt ⟨y, portStage_le dir wt F hy⟩⟫ := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem w hw =>
        obtain ⟨k, hk, rfl⟩ := hw
        have hvalue : weightedPort dir wt
            ⟨portBasis k, portStage_le dir wt F (Submodule.subset_span ⟨k, hk, rfl⟩)⟩
            = wt k • dir k := weightedPort_portBasis dir wt k
        rw [hvalue, huv, inner_portEmb_portWitness_portBasis dir wt F z hk,
          real_inner_smul_right, real_inner_comm]
    | zero =>
        rw [inner_zero_right]
        have hz0 : (⟨(0 : PortCoord J), portStage_le dir wt F (Submodule.zero_mem _)⟩ :
            (weightedPort dir wt).domain) = 0 := Subtype.ext rfl
        rw [hz0, LinearPMap.map_zero, inner_zero_right]
    | add a b ha hb iha ihb =>
        have hadd : (⟨a + b, portStage_le dir wt F (Submodule.add_mem _ ha hb)⟩ :
            (weightedPort dir wt).domain)
            = ⟨a, portStage_le dir wt F ha⟩ + ⟨b, portStage_le dir wt F hb⟩ := Subtype.ext rfl
        rw [inner_add_right, iha, ihb, hadd, LinearPMap.map_add, inner_add_right]
    | smul t a ha iha =>
        have hsm : (⟨t • a, portStage_le dir wt F (Submodule.smul_mem _ t ha)⟩ :
            (weightedPort dir wt).domain)
            = t • ⟨a, portStage_le dir wt F ha⟩ := Subtype.ext rfl
        rw [real_inner_smul_right, iha, hsm, LinearPMap.map_smul, real_inner_smul_right]
  have hchar : ∀ v : (weightedPort dir wt).domain,
      ((v : (weightedPort dir wt).domain) : PortCoord J) ∈ portStage (J := J) F →
      ⟪((u : (weightedPort dir wt).domain) : PortCoord J),
        ((v : (weightedPort dir wt).domain) : PortCoord J)⟫
        = ⟪z, weightedPort dir wt v⟫ := by
    intro v hv
    have h := hgen (v : PortCoord J) hv
    have hvv : (⟨(v : PortCoord J), portStage_le dir wt F hv⟩ :
        (weightedPort dir wt).domain) = v := Subtype.ext rfl
    rw [hvv] at h
    exact h
  rw [portGram_eq_of_coLift (weightedPort dir wt) (portStage (J := J) F)
    (portStage_le dir wt F) z u humem hchar]
  have hval : weightedPort dir wt u = portMass dir wt (portWitness dir wt F z) :=
    weightedPort_apply dir wt (portWitness dir wt F z) ⟨portWitness dir wt F z, rfl⟩
  rw [hval, portWitness, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [portMass_single, smul_smul]
  congr 1
  ring

end WeightedPort

end HTGeometry.ConstraintMotiveRelativity
