import Mathlib

/-!
# A reusable Higgs-mechanism interface

A Higgs mechanism here consists of a group action, a selected vacuum, and a nonnegative
gauge-invariant potential vanishing at that vacuum.  Its unbroken symmetry is definitionally the
vacuum stabilizer.  This is the algebraic core shared by continuous, finite, Abelian, and
non-Abelian examples; no differentiability or field equation is built into the interface.

`orbitWellPotential` gives every group action a canonical discrete invariant potential.  It is
useful for exposing symmetry-breaking patterns already present in the corpus, while smooth models
should supply their own potentials.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- Group action with a selected zero-energy vacuum and nonnegative invariant potential. -/
structure HiggsMechanism (G X : Type*) [Group G] [MulAction G X] where
  vacuum : X
  potential : X → ℝ
  gauge_invariant : ∀ (g : G) (x : X), potential (g • x) = potential x
  vacuum_zero : potential vacuum = 0
  potential_nonneg : ∀ x, 0 ≤ potential x

namespace HiggsMechanism

variable {G X : Type*} [Group G] [MulAction G X]

/-- Residual gauge group fixing the selected vacuum. -/
def unbroken (M : HiggsMechanism G X) : Subgroup G :=
  MulAction.stabilizer G M.vacuum

/-- Gauge orbit of the selected vacuum. -/
def vacuumOrbit (M : HiggsMechanism G X) : Set X :=
  MulAction.orbit G M.vacuum

/-- Complete symmetry breaking: only the identity fixes the vacuum. -/
def IsFullyBroken (M : HiggsMechanism G X) : Prop :=
  M.unbroken = ⊥

/-- Partial symmetry breaking: residual group is nontrivial and proper. -/
def IsPartiallyBroken (M : HiggsMechanism G X) : Prop :=
  M.unbroken ≠ ⊥ ∧ M.unbroken ≠ ⊤

/-- No symmetry breaking: every gauge transformation fixes the vacuum. -/
def IsUnbroken (M : HiggsMechanism G X) : Prop :=
  M.unbroken = ⊤

/-- Every point on the selected vacuum orbit has zero potential. -/
theorem potential_eq_zero_of_mem_vacuumOrbit
    (M : HiggsMechanism G X) {x : X} (hx : x ∈ M.vacuumOrbit) :
    M.potential x = 0 := by
  rw [vacuumOrbit, MulAction.mem_orbit_iff] at hx
  obtain ⟨g, rfl⟩ := hx
  rw [M.gauge_invariant, M.vacuum_zero]

/-- Selected vacuum is a global minimum. -/
theorem vacuum_is_globalMinimum (M : HiggsMechanism G X) (x : X) :
    M.potential M.vacuum ≤ M.potential x := by
  rw [M.vacuum_zero]
  exact M.potential_nonneg x

/-- Discrete two-level potential whose zero set is one prescribed gauge orbit. -/
noncomputable def orbitWellPotential (v : X) (x : X) : ℝ := by
  classical
  exact if x ∈ MulAction.orbit G v then 0 else 1

/-- Orbit membership is invariant under the group action. -/
theorem mem_orbit_smul_iff (v x : X) (g : G) :
    g • x ∈ MulAction.orbit G v ↔ x ∈ MulAction.orbit G v := by
  simp only [MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨h, hh⟩
    refine ⟨g⁻¹ * h, ?_⟩
    rw [mul_smul, hh, inv_smul_smul]
  · rintro ⟨h, hh⟩
    refine ⟨g * h, ?_⟩
    rw [mul_smul, hh]

/-- Canonical orbit-well potential is gauge invariant. -/
theorem orbitWellPotential_gauge_invariant (v x : X) (g : G) :
    orbitWellPotential (G := G) v (g • x) = orbitWellPotential (G := G) v x := by
  rw [orbitWellPotential, orbitWellPotential, mem_orbit_smul_iff]

/-- Canonical orbit-well potential vanishes at its selected vacuum. -/
theorem orbitWellPotential_vacuum (v : X) :
    orbitWellPotential (G := G) v v = 0 := by
  rw [orbitWellPotential, if_pos]
  exact MulAction.mem_orbit_iff.mpr ⟨1, one_smul G v⟩

/-- Canonical orbit-well potential is nonnegative. -/
theorem orbitWellPotential_nonneg (v x : X) :
    0 ≤ orbitWellPotential (G := G) v x := by
  rw [orbitWellPotential]
  split_ifs <;> norm_num

/-- Zero set of canonical orbit-well potential is exactly selected vacuum orbit. -/
theorem orbitWellPotential_eq_zero_iff (v x : X) :
    orbitWellPotential (G := G) v x = 0 ↔ x ∈ MulAction.orbit G v := by
  rw [orbitWellPotential]
  by_cases hx : x ∈ MulAction.orbit G v <;> simp [hx]

/-- Every action and selected point carry a canonical discrete Higgs mechanism. -/
def canonicalOrbitWell (v : X) : HiggsMechanism G X where
  vacuum := v
  potential := orbitWellPotential (G := G) v
  gauge_invariant := fun g x => orbitWellPotential_gauge_invariant v x g
  vacuum_zero := orbitWellPotential_vacuum (G := G) v
  potential_nonneg := orbitWellPotential_nonneg (G := G) v

end HiggsMechanism

end GaloisForLFunctions.HTGeometry
