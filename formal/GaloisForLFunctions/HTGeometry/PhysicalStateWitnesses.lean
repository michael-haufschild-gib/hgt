import GaloisForLFunctions.HTGeometry.FrozenConstraint

/-!
# Physical states exist

A physical state is a vector annihilated by the constraint, so the physical states are exactly the
kernel of the constraint operator.  The zero vector is one for every constraint, and the class is
closed under the linear operations — so the Ward-value laws, which are conditioned on being physical
for two constraints at once, always have the zero state to run on, and a whole subspace whenever the
two kernels meet.
-/

namespace GaloisForLFunctions

variable {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]

/-- Being a physical state is membership in the kernel of the constraint. -/
theorem physicalState_iff_mem_ker (C : Module.End R M) (ψ : M) :
    PhysicalState C ψ ↔ ψ ∈ LinearMap.ker C := Iff.rfl

/-- **The zero vector is physical for every constraint.** -/
theorem physicalState_zero (C : Module.End R M) : PhysicalState C (0 : M) := by
  rw [PhysicalState, map_zero]

/-- Physical states are closed under addition. -/
theorem PhysicalState.add {C : Module.End R M} {ψ φ : M} (hψ : PhysicalState C ψ)
    (hφ : PhysicalState C φ) : PhysicalState C (ψ + φ) := by
  rw [PhysicalState, map_add, hψ, hφ, add_zero]

/-- Physical states are closed under scalars. -/
theorem PhysicalState.smul {C : Module.End R M} {ψ : M} (hψ : PhysicalState C ψ) (r : R) :
    PhysicalState C (r • ψ) := by
  rw [PhysicalState, map_smul, hψ, smul_zero]

/-- **The zero state is jointly physical for any two constraints**, so the joint hypothesis of the
Ward-value laws is never vacuous. -/
theorem physicalState_zero_and (C D : Module.End R M) :
    PhysicalState C (0 : M) ∧ PhysicalState D (0 : M) :=
  ⟨physicalState_zero C, physicalState_zero D⟩

end GaloisForLFunctions
