import Mathlib.RepresentationTheory.Invariants
import Mathlib.Analysis.Complex.Basic
import Mathlib.RepresentationTheory.Irreducible
import Mathlib.Topology.Algebra.OpenSubgroup

/-! Smooth vectors form a subrepresentation. In particular the
smooth vectors in the algebraic dual carry the contragredient. -/

noncomputable section

namespace Representation

variable {G V : Type*} [Group G] [AddCommGroup V] [Module ℂ V]
  (ρ : Representation ℂ G V)

/-- The subspace fixed by a subgroup. -/
def restrictedInvariants (K : Subgroup G) : Submodule ℂ V :=
  invariants (k := ℂ) (G := K) (V := V) (ρ.comp K.subtype)

/-- The subgroup fixing a vector. -/
def vectorStabilizer (v : V) : Subgroup G where
  carrier := {g | ρ g v = v}
  one_mem' := by simp
  mul_mem' := fun {g h} hg hh => by
    change ρ (g * h) v = v
    rw [map_mul, Module.End.mul_apply, show ρ h v = v from hh]
    exact hg
  inv_mem' := fun {g} hg => by
    change ρ g⁻¹ v = v
    nth_rw 1 [← show ρ g v = v from hg]
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

@[simp] theorem mem_vectorStabilizer (v : V) (g : G) :
    g ∈ ρ.vectorStabilizer v ↔ ρ g v = v := Iff.rfl

variable [TopologicalSpace G] [IsTopologicalGroup G]

theorem isOpen_vectorStabilizer_of_open_subgroup {v : V}
    {H : Subgroup G} (hH : IsOpen (H : Set G)) (hv : ∀ g ∈ H, ρ g v = v) :
    IsOpen (ρ.vectorStabilizer v : Set G) :=
  Subgroup.isOpen_mono (fun g hg => hv g hg) hH

/-- The submodule of vectors with open stabilizer. -/
def smoothVectors : Submodule ℂ V where
  carrier := {v | IsOpen (ρ.vectorStabilizer v : Set G)}
  zero_mem' := by
    change IsOpen {g | ρ g (0 : V) = 0}
    simp
  add_mem' := fun {v w} hv hw => by
    apply ρ.isOpen_vectorStabilizer_of_open_subgroup (H := ρ.vectorStabilizer v ⊓ ρ.vectorStabilizer w)
      (hv.inter hw)
    intro g hg
    rw [map_add, (ρ.mem_vectorStabilizer v g).mp hg.1, (ρ.mem_vectorStabilizer w g).mp hg.2]
  smul_mem' := fun c v hv => by
    apply ρ.isOpen_vectorStabilizer_of_open_subgroup (H := ρ.vectorStabilizer v) hv
    intro g hg
    rw [map_smul, (ρ.mem_vectorStabilizer v g).mp hg]

theorem mem_smoothVectors (v : V) :
    v ∈ ρ.smoothVectors ↔ IsOpen {g : G | ρ g v = v} := Iff.rfl

theorem apply_mem_smoothVectors (a : G) {v : V} (hv : v ∈ ρ.smoothVectors) :
    ρ a v ∈ ρ.smoothVectors := by
  have he : {g : G | ρ g (ρ a v) = ρ a v} =
      (fun g => a⁻¹ * g * a) ⁻¹' {g : G | ρ g v = v} := by
    ext g
    simp only [Set.mem_setOf_eq, Set.mem_preimage, map_mul, Module.End.mul_apply]
    constructor
    · intro h
      rw [h, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
    · intro h
      have h' := congrArg (ρ a) h
      rwa [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply] at h'
  rw [mem_smoothVectors, he]
  exact ((ρ.mem_smoothVectors v).mp hv).preimage (by fun_prop)

/-- The action restricted to the vectors with open stabilizer. -/
def smoothPart : Representation ℂ G (ρ.smoothVectors) :=
  (⟨ρ.smoothVectors, ρ.apply_mem_smoothVectors⟩ : Subrepresentation ρ).toRepresentation

@[simp] theorem smoothPart_val (g : G) (v : ρ.smoothVectors) : (ρ.smoothPart g v : V) = ρ g v := rfl

theorem smooth_smoothPart (v : ρ.smoothVectors) : IsOpen {g : G | ρ.smoothPart g v = v} := by
  have he : {g : G | ρ.smoothPart g v = v} = {g : G | ρ g v.val = v.val} :=
    Set.ext fun g => Subtype.ext_iff
  rw [he]
  exact (ρ.mem_smoothVectors _).mp v.2

theorem smooth_subrepresentation (U : Subrepresentation ρ)
    (hρ : ∀ v : V, IsOpen {g : G | ρ g v = v}) (v : U.toSubmodule) :
    IsOpen {g : G | U.toRepresentation g v = v} := by
  have he : {g : G | U.toRepresentation g v = v} = {g : G | ρ g v.val = v.val} :=
    Set.ext fun g => Subtype.ext_iff
  rw [he]
  exact hρ _

/-- The smooth part of the inverse-transpose action on the dual. -/
def smoothDual : Representation ℂ G (ρ.dual.smoothVectors) := ρ.dual.smoothPart

@[simp] theorem smoothDual_apply (g : G) (f : ρ.dual.smoothVectors) (v : V) :
    (ρ.smoothDual g f : Module.Dual ℂ V) v = (f : Module.Dual ℂ V) (ρ g⁻¹ v) := rfl

end Representation

#print axioms Representation.smooth_smoothPart
#print axioms Representation.smoothDual_apply
