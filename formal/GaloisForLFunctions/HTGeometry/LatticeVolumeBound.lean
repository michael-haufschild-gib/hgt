import GaloisForLFunctions.HTGeometry.LatticeWellRounded
import Mathlib.Analysis.InnerProductSpace.Orientation

/-!
# Hadamard's bound for the shortest vectors of a lattice

The volume spanned by `n` shortest vectors of a lattice is at most `m ^ n`, where `m` is the length
of a shortest vector.  For a **well-rounded** lattice `n` independent shortest vectors exist, so the
covolume of the sublattice they generate — and hence the covolume of the lattice itself, which
divides it — is at most `m ^ n`.  Together with Minkowski's upper bound `m ≤ γ_n · covolume^{1/n}`
this pins the minimum of a well-rounded unimodular lattice into a fixed interval, which is the
source of the compactness of the well-rounded locus.

* `abs_volumeForm_latticeMinimalVectors_le` : **Hadamard's bound at the minimum.**
-/

namespace GaloisForLFunctions.HTGeometry

open Module

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Fact (finrank ℝ E = n)]

/-- **Hadamard's bound at the minimum.**  A family of shortest vectors spans a volume of at most
`m ^ n`. -/
theorem abs_volumeForm_latticeMinimalVectors_le (o : Orientation ℝ E (Fin n))
    {L : Submodule ℤ E} {m : ℝ} {v : Fin n → E}
    (hv : ∀ i, v i ∈ latticeMinimalVectors L m) :
    |o.volumeForm v| ≤ m ^ n := by
  refine le_trans (o.abs_volumeForm_apply_le v) ?_
  have : ∀ i : Fin n, ‖v i‖ = m := fun i => (hv i).2.2
  simp [this]

end GaloisForLFunctions.HTGeometry
