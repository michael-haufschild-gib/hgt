import Mathlib

/-!
# Conductor gluing and integral invariant-cycle specialization

This file formalizes two dependency-closed mechanisms extracted from `s6.pdf`:

* the linear Mayer--Vietoris pullback behind Lemma 10.3: normalized data whose conductor
  restriction vanishes glues uniquely with zero conductor component, and a nonzero normalized
  section gives a nonzero hidden class;
* the final integral step in Appendix B: equivariant specialization lands in monodromy
  invariants, while saturation plus rational cofinality upgrades the inclusion to equality.

The doubling map `Z -> Z` is the sharp firewall.  It lands in the invariants of identity
monodromy and is rationally cofinal there, but its image is the proper subgroup `2Z` because the
image is not saturated.  Thus equal rational rank cannot replace the paper's saturation proof.

No existence of an Xi degeneration or conductor-to-nearby-cycle regulator is asserted here.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

universe uR uN uD uC uS uM

/-- Linear Mayer--Vietoris data for normalization/conductor gluing. -/
structure ConductorGluingDiagram
    (R : Type uR) [CommRing R]
    (N : Type uN) (D : Type uD) (C : Type uC)
    [AddCommGroup N] [Module R N]
    [AddCommGroup D] [Module R D]
    [AddCommGroup C] [Module R C] where
  normalizationRestriction : N →ₗ[R] C
  conductorPullback : D →ₗ[R] C

namespace ConductorGluingDiagram

variable {R : Type uR} [CommRing R]
variable {N : Type uN} {D : Type uD} {C : Type uC}
variable [AddCommGroup N] [Module R N]
variable [AddCommGroup D] [Module R D]
variable [AddCommGroup C] [Module R C]

/-- Difference map in the conductor Mayer--Vietoris square. -/
def gluingDifferential (G : ConductorGluingDiagram R N D C) :
    (N × D) →ₗ[R] C where
  toFun p := G.normalizationRestriction p.1 - G.conductorPullback p.2
  map_add' p q := by simp; abel
  map_smul' r p := by simp [smul_sub]

/-- Compatible normalization/conductor pairs. -/
abbrev GluedSections (G : ConductorGluingDiagram R N D C) :=
  LinearMap.ker G.gluingDifferential

/-- Normalization component of a glued section. -/
def normalizationProjection (G : ConductorGluingDiagram R N D C) :
    G.GluedSections →ₗ[R] N where
  toFun s := s.1.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Conductor component of a glued section. -/
def conductorProjection (G : ConductorGluingDiagram R N D C) :
    G.GluedSections →ₗ[R] D where
  toFun s := s.1.2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Canonical hidden class from a normalized section vanishing on the conductor. -/
def hiddenSection (G : ConductorGluingDiagram R N D C)
    (n : N) (hn : G.normalizationRestriction n = 0) : G.GluedSections :=
  ⟨(n, 0), by simp [gluingDifferential, hn]⟩

@[simp]
theorem normalizationProjection_hiddenSection
    (G : ConductorGluingDiagram R N D C)
    (n : N) (hn : G.normalizationRestriction n = 0) :
    G.normalizationProjection (G.hiddenSection n hn) = n := rfl

@[simp]
theorem conductorProjection_hiddenSection
    (G : ConductorGluingDiagram R N D C)
    (n : N) (hn : G.normalizationRestriction n = 0) :
    G.conductorProjection (G.hiddenSection n hn) = 0 := rfl

/-- The normalized/conductor pair determines the glued section uniquely. -/
theorem existsUnique_hiddenSection
    (G : ConductorGluingDiagram R N D C)
    (n : N) (hn : G.normalizationRestriction n = 0) :
    ∃! s : G.GluedSections,
      G.normalizationProjection s = n ∧ G.conductorProjection s = 0 := by
  refine ⟨G.hiddenSection n hn, by simp, ?_⟩
  intro s hs
  apply Subtype.ext
  apply Prod.ext
  · exact hs.1
  · exact hs.2

/-- Nonzero normalized data gives a nonzero hidden conductor class. -/
theorem hiddenSection_ne_zero
    (G : ConductorGluingDiagram R N D C)
    (n : N) (hn : G.normalizationRestriction n = 0) (hne : n ≠ 0) :
    G.hiddenSection n hn ≠ 0 := by
  intro hzero
  apply hne
  have := congrArg G.normalizationProjection hzero
  simpa using this

end ConductorGluingDiagram

/-! ## Universal nodal Picard--Lefschetz lattice

For one ordinary node, choose an oriented vanishing-cycle basis of nearby first homology.  The
Picard--Lefschetz transformation is `(a, b) ↦ (a + b, b)`.  The normalization-conductor connecting
generator specializes to `(1, 0)`.  The following coefficient-level model proves, over any
commutative ring, that its full specialization line is exactly the monodromy-fixed line.

This is the exact cellular lattice calculation, not a construction of a regulator from a concrete
analytic family into this lattice.  That natural comparison remains separate data.
-/

section UniversalNodalLattice

variable (A : Type*) [CommRing A]

/-- Picard--Lefschetz monodromy for one oriented ordinary node. -/
def universalNodePicardLefschetzMonodromy :
    (A × A) →ₗ[A] (A × A) where
  toFun v := (v.1 + v.2, v.2)
  map_add' v w := by
    ext <;> simp [add_left_comm, add_comm]
  map_smul' a v := by
    ext <;> simp [mul_add]

/-- Specialization of the oriented normalization-conductor connecting coefficient. -/
def universalNodeConductorSpecialization : A →ₗ[A] (A × A) where
  toFun a := (a, 0)
  map_add' a b := by simp
  map_smul' a b := by simp

/-- Monodromy-invariant line in the nearby two-cycle lattice. -/
def universalNodeMonodromyInvariants : Submodule A (A × A) :=
  LinearMap.ker (universalNodePicardLefschetzMonodromy A - LinearMap.id)

@[simp]
theorem universalNodePicardLefschetzMonodromy_apply (v : A × A) :
    universalNodePicardLefschetzMonodromy A v = (v.1 + v.2, v.2) := rfl

@[simp]
theorem universalNodeConductorSpecialization_apply (a : A) :
    universalNodeConductorSpecialization A a = (a, 0) := rfl

/-- Fixed vectors are exactly multiples of the vanishing-cycle direction. -/
@[simp]
theorem mem_universalNodeMonodromyInvariants_iff (v : A × A) :
    v ∈ universalNodeMonodromyInvariants A ↔ v.2 = 0 := by
  rw [universalNodeMonodromyInvariants, LinearMap.mem_ker]
  simp only [LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]
  constructor
  · intro h
    have hfirst := congrArg Prod.fst h
    simpa using hfirst
  · intro h
    apply Prod.ext
    · simp [h]
    · rfl

/-- The conductor specialization loses no coefficient. -/
theorem universalNodeConductorSpecialization_injective :
    Function.Injective (universalNodeConductorSpecialization A) := by
  intro a b hab
  exact congrArg Prod.fst hab

/-- Exact local invariant-cycle theorem for the universal ordinary-node lattice. -/
theorem universalNodeConductorSpecialization_range_eq_monodromyInvariants :
    LinearMap.range (universalNodeConductorSpecialization A) =
      universalNodeMonodromyInvariants A := by
  ext v
  rw [mem_universalNodeMonodromyInvariants_iff]
  constructor
  · rintro ⟨a, rfl⟩
    rfl
  · intro hv
    exact ⟨v.1, Prod.ext rfl hv.symm⟩

/-- A nonzero conductor coefficient gives a nonzero nearby invariant class. -/
theorem universalNodeConductorSpecialization_ne_zero
    {a : A} (ha : a ≠ 0) :
    universalNodeConductorSpecialization A a ≠ 0 := by
  exact (universalNodeConductorSpecialization_injective A).ne ha

/-- Every specialized conductor coefficient is fixed by Picard--Lefschetz monodromy. -/
theorem universalNodeConductorSpecialization_monodromy_fixed (a : A) :
    universalNodePicardLefschetzMonodromy A
        (universalNodeConductorSpecialization A a) =
      universalNodeConductorSpecialization A a := by
  simp

end UniversalNodalLattice

section IntegralSpecialization

variable {S : Type uS} {M : Type uM}
variable [AddCommGroup S] [AddCommGroup M]

/-- Integral monodromy-invariant submodule. -/
def monodromyInvariants (T : M →ₗ[ℤ] M) : Submodule ℤ M :=
  LinearMap.ker (T - LinearMap.id)

/-- Integral saturation: no nonzero positive integer multiple enters without its source. -/
def IntegerSaturated (A : Submodule ℤ M) : Prop :=
  ∀ (n : ℕ) (x : M), 0 < n → n • x ∈ A → x ∈ A

/-- Every element of `B` has a nonzero integral multiple in `A`. -/
def RationallyCofinalIn (A B : Submodule ℤ M) : Prop :=
  A ≤ B ∧ ∀ x ∈ B, ∃ n : ℕ, 0 < n ∧ n • x ∈ A

/-- Saturation upgrades rational cofinality to integral equality. -/
theorem eq_of_integerSaturated_of_rationallyCofinalIn
    {A B : Submodule ℤ M}
    (hsat : IntegerSaturated A) (hcofinal : RationallyCofinalIn A B) :
    A = B := by
  apply le_antisymm hcofinal.1
  intro x hx
  obtain ⟨n, hn, hnx⟩ := hcofinal.2 x hx
  exact hsat n x hn hnx

/-- Equivariance with trivial source monodromy. -/
def SpecializationLandsInInvariants
    (sp : S →ₗ[ℤ] M) (T : M →ₗ[ℤ] M) : Prop :=
  T.comp sp = sp

/-- Every equivariant specialization class is monodromy invariant. -/
theorem specialization_range_le_monodromyInvariants
    (sp : S →ₗ[ℤ] M) (T : M →ₗ[ℤ] M)
    (hinvariant : SpecializationLandsInInvariants sp T) :
    LinearMap.range sp ≤ monodromyInvariants T := by
  rintro y ⟨x, rfl⟩
  rw [monodromyInvariants, LinearMap.mem_ker]
  change T (sp x) - sp x = 0
  rw [← LinearMap.comp_apply, hinvariant, sub_self]

/-- Paper's final integral step: invariant inclusion, saturation, and rational cofinality give equality. -/
theorem specialization_range_eq_monodromyInvariants
    (sp : S →ₗ[ℤ] M) (T : M →ₗ[ℤ] M)
    (hinvariant : SpecializationLandsInInvariants sp T)
    (hsaturated : IntegerSaturated (LinearMap.range sp))
    (hcofinal : ∀ y ∈ monodromyInvariants T,
      ∃ n : ℕ, 0 < n ∧ n • y ∈ LinearMap.range sp) :
    LinearMap.range sp = monodromyInvariants T := by
  apply eq_of_integerSaturated_of_rationallyCofinalIn hsaturated
  exact ⟨specialization_range_le_monodromyInvariants sp T hinvariant, hcofinal⟩

/-- Minimal integral countermodel: multiplication by two. -/
def integerDoublingSpecialization : ℤ →ₗ[ℤ] ℤ :=
  2 • LinearMap.id

@[simp]
theorem integerDoublingSpecialization_apply (x : ℤ) :
    integerDoublingSpecialization x = 2 * x := by
  simp [integerDoublingSpecialization]

@[simp]
theorem monodromyInvariants_id :
    monodromyInvariants (LinearMap.id : ℤ →ₗ[ℤ] ℤ) = ⊤ := by
  ext x
  simp [monodromyInvariants]

theorem one_not_mem_integerDoublingSpecialization_range :
    (1 : ℤ) ∉ LinearMap.range integerDoublingSpecialization := by
  rintro ⟨x, hx⟩
  simp only [integerDoublingSpecialization_apply] at hx
  omega

/-- Doubling lands in invariants for identity monodromy. -/
theorem integerDoublingSpecialization_landsInInvariants :
    SpecializationLandsInInvariants integerDoublingSpecialization
      (LinearMap.id : ℤ →ₗ[ℤ] ℤ) := by
  simp [SpecializationLandsInInvariants]

/-- Doubling is rationally cofinal in all identity-monodromy invariants. -/
theorem integerDoublingSpecialization_rationallyCofinal :
    ∀ y ∈ monodromyInvariants (LinearMap.id : ℤ →ₗ[ℤ] ℤ),
      ∃ n : ℕ, 0 < n ∧ n • y ∈ LinearMap.range integerDoublingSpecialization := by
  intro y _
  refine ⟨2, by omega, ?_⟩
  refine ⟨y, ?_⟩
  simp [integerDoublingSpecialization]

/-- Equal rational rank and invariant landing do not imply integral equality. -/
theorem integerDoublingSpecialization_range_ne_invariants :
    LinearMap.range integerDoublingSpecialization ≠
      monodromyInvariants (LinearMap.id : ℤ →ₗ[ℤ] ℤ) := by
  intro heq
  apply one_not_mem_integerDoublingSpecialization_range
  rw [heq, monodromyInvariants_id]
  trivial

/-- The precise failed hypothesis in the doubling countermodel is saturation. -/
theorem integerDoublingSpecialization_range_not_integerSaturated :
    ¬ IntegerSaturated (LinearMap.range integerDoublingSpecialization) := by
  intro hsat
  apply one_not_mem_integerDoublingSpecialization_range
  apply hsat 2 1 (by omega)
  refine ⟨1, ?_⟩
  simp [integerDoublingSpecialization]

end IntegralSpecialization

end

end GaloisForLFunctions.HTGeometry
