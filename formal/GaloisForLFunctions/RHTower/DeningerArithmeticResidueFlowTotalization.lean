import Mathlib

/-!
# Two-term mapping fiber for Deninger arithmetic cohomology

A chain endomorphism of a two-term residue complex has a three-term mapping-fiber
totalization.  This is the two-term algebraic prototype for the Weil--Arakelov specialization
`Fib(Theta - n)` of Deninger's missing dynamical coefficient complex.  Transverse flow is a
chain endomorphism; it is not itself the leafwise cohomological differential.

No zeta function, zero, spectral coordinate, positivity premise, or RH hypothesis occurs here.
-/

namespace RHTower

section ResidueFlow

variable {R A0 A1 : Type*}
variable [CommRing R]
variable [AddCommGroup A0] [Module R A0]
variable [AddCommGroup A1] [Module R A1]

/-- Degree-zero differential in the residue--flow total complex. -/
def deningerResidueFlowD0
    (residue : A0 →ₗ[R] A1) (flow0 : A0 →ₗ[R] A0) :
    A0 →ₗ[R] A1 × A0 :=
  residue.prod flow0

/-- Degree-one differential in the residue--flow total complex. -/
def deningerResidueFlowD1
    (residue : A0 →ₗ[R] A1) (flow1 : A1 →ₗ[R] A1) :
    A1 × A0 →ₗ[R] A1 where
  toFun x := flow1 x.1 - residue x.2
  map_add' x y := by
    simp only [Prod.fst_add, Prod.snd_add, map_add]
    abel
  map_smul' c x := by
    simp only [Prod.smul_fst, Prod.smul_snd, map_smul]
    exact (smul_sub c (flow1 x.1) (residue x.2)).symm

@[simp]
theorem deningerResidueFlowD0_apply
    (residue : A0 →ₗ[R] A1) (flow0 : A0 →ₗ[R] A0) (a : A0) :
    deningerResidueFlowD0 residue flow0 a =
      (residue a, flow0 a) :=
  rfl

@[simp]
theorem deningerResidueFlowD1_apply
    (residue : A0 →ₗ[R] A1) (flow1 : A1 →ₗ[R] A1)
    (x : A1 × A0) :
    deningerResidueFlowD1 residue flow1 x =
      flow1 x.1 - residue x.2 :=
  rfl

/--
Residue naturality of the leafwise flow is exactly the condition making the total differential
square to zero.
-/
theorem deningerResidueFlowD1_comp_D0
    (residue : A0 →ₗ[R] A1)
    (flow0 : A0 →ₗ[R] A0)
    (flow1 : A1 →ₗ[R] A1)
    (hcomm : flow1.comp residue = residue.comp flow0) :
    (deningerResidueFlowD1 residue flow1).comp
        (deningerResidueFlowD0 residue flow0) = 0 := by
  apply LinearMap.ext
  intro a
  have ha := LinearMap.congr_fun hcomm a
  change flow1 (residue a) - residue (flow0 a) = 0
  exact sub_eq_zero.mpr ha

/-- Degree-zero cohomology of the two-term mapping-fiber total complex. -/
abbrev DeningerResidueFlowH0
    (residue : A0 →ₗ[R] A1) (flow0 : A0 →ₗ[R] A0) :=
  LinearMap.ker (deningerResidueFlowD0 residue flow0)

/-- Degree-one cohomology of the two-term mapping-fiber total complex. -/
abbrev DeningerResidueFlowH1
    (residue : A0 →ₗ[R] A1)
    (flow0 : A0 →ₗ[R] A0)
    (flow1 : A1 →ₗ[R] A1) :=
  LinearMap.ker (deningerResidueFlowD1 residue flow1) ⧸
    (LinearMap.range (deningerResidueFlowD0 residue flow0)).comap
      (LinearMap.ker (deningerResidueFlowD1 residue flow1)).subtype

/-- Degree-two cohomology of the two-term mapping-fiber total complex. -/
abbrev DeningerResidueFlowH2
    (residue : A0 →ₗ[R] A1) (flow1 : A1 →ₗ[R] A1) :=
  A1 ⧸ LinearMap.range (deningerResidueFlowD1 residue flow1)

/-- Degree-zero cocycles are simultaneous residue and flow invariants. -/
theorem deningerResidueFlow_ker_D0
    (residue : A0 →ₗ[R] A1) (flow0 : A0 →ₗ[R] A0) :
    LinearMap.ker (deningerResidueFlowD0 residue flow0) =
      LinearMap.ker residue ⊓ LinearMap.ker flow0 := by
  ext a
  simp [deningerResidueFlowD0]

/-- A middle cochain is closed exactly when its residue and flow boundaries agree. -/
theorem deningerResidueFlow_mem_ker_D1
    (residue : A0 →ₗ[R] A1) (flow1 : A1 →ₗ[R] A1)
    (x : A1 × A0) :
    x ∈ LinearMap.ker (deningerResidueFlowD1 residue flow1) ↔
      flow1 x.1 = residue x.2 := by
  simp [deningerResidueFlowD1, sub_eq_zero]

/-- Middle coboundaries are precisely pairs of residue and flow boundaries of one source. -/
theorem deningerResidueFlow_mem_range_D0
    (residue : A0 →ₗ[R] A1) (flow0 : A0 →ₗ[R] A0)
    (x : A1 × A0) :
    x ∈ LinearMap.range (deningerResidueFlowD0 residue flow0) ↔
      ∃ a : A0, residue a = x.1 ∧ flow0 a = x.2 := by
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨a, rfl, rfl⟩
  · rintro ⟨a, ha1, ha0⟩
    refine ⟨a, ?_⟩
    ext
    · exact ha1
    · exact ha0

/--
Top coboundaries are exactly the sum of the flow image and the residue image.
-/
theorem deningerResidueFlow_range_D1
    (residue : A0 →ₗ[R] A1) (flow1 : A1 →ₗ[R] A1) :
    LinearMap.range (deningerResidueFlowD1 residue flow1) =
      LinearMap.range flow1 ⊔ LinearMap.range residue := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    rw [Submodule.mem_sup]
    refine ⟨flow1 x.1, ⟨x.1, rfl⟩,
      -residue x.2, ⟨-x.2, by simp⟩, ?_⟩
    rw [deningerResidueFlowD1_apply]
    exact (sub_eq_add_neg _ _).symm
  · rw [Submodule.mem_sup]
    rintro ⟨u, ⟨b, rfl⟩, v, ⟨a, rfl⟩, huv⟩
    refine ⟨(b, -a), ?_⟩
    simp only [deningerResidueFlowD1_apply, map_neg, sub_neg_eq_add]
    exact huv

end ResidueFlow

end RHTower
