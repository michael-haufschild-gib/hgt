import GaloisForLFunctions.RHTower.Artin.ArtinLocalEulerFactor
import GaloisForLFunctions.HTGeometry.IdealInertiaConjugation

/-!
# Conjugation transport for Artin Frobenius--inertia data

For an ideal acted on by a group, conjugating both an inertia element and the ideal transports the
inertia subgroup exactly.  The second theorem specializes this to the decomposition stabilizers
used by the local Artin Euler polynomial.

This is the first algebraic component of prime-choice independence.  It does not yet construct
the conjugacy of invariant-space Frobenius maps or prove equality of local Euler polynomials.
-/

open scoped Pointwise

noncomputable section

universe u

namespace GaloisForLFunctions

variable {S G : Type u}
variable [CommRing S] [Group G] [MulSemiringAction G S]

/-- The natural equivalence between decomposition stabilizers maps their actual inertia
subgroups exactly. -/
theorem inertia_map_stabilizer_conj (τ : G) (Q : Ideal S) :
    (Q.inertia (MulAction.stabilizer G Q)).map
      (MulAction.stabilizerEquivStabilizer (show τ • Q = τ • Q from rfl)).toMonoidHom =
      (τ • Q).inertia (MulAction.stabilizer G (τ • Q)) := by
  ext σ
  rw [Subgroup.mem_map_equiv, ← Ideal.coe_mem_inertia, ← Ideal.coe_mem_inertia,
    ← inertia_map_conj]
  rw [Subgroup.mem_map_equiv]
  rw [MulAction.stabilizerEquivStabilizer_symm_apply]
  simp only [MulAut.conj_apply, MulAut.conj_symm_apply, inv_inv]

end GaloisForLFunctions
