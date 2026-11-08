import GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap.NarainPartition

/-!
# Mirror symmetry of the Narain partition

Swapping one momentum and winding coordinate preserves spin and exchanges the target quadratic forms. Reindexing the literal partition yields target symmetry.
-/

open Complex RHTower
open GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap
set_option autoImplicit false
noncomputable section
namespace GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap

/-- Exchanging momentum and winding in the first coordinate exchanges the target moduli. -/
def mirrorCharge : ((ℤ × ℤ) × (ℤ × ℤ)) ≃ ((ℤ × ℤ) × (ℤ × ℤ)) where
  toFun q := ((q.2.1, q.1.2), (q.1.1, q.2.2))
  invFun q := ((q.2.1, q.1.2), (q.1.1, q.2.2))
  left_inv q := by rcases q with ⟨⟨a, b⟩, ⟨c, d⟩⟩; rfl
  right_inv q := by rcases q with ⟨⟨a, b⟩, ⟨c, d⟩⟩; rfl

theorem chargeSpin_mirrorCharge (q : (ℤ × ℤ) × (ℤ × ℤ)) :
    chargeSpin (mirrorCharge q) = chargeSpin q := by
  rcases q with ⟨⟨a, b⟩, ⟨c, d⟩⟩
  simp only [mirrorCharge, Equiv.coe_fn_mk, chargeSpin]
  ring

/-- Mirror charge exchange preserves the full mass after swapping the two target moduli. -/
theorem narainMassSq_mirror (ρ σ : D4BMUpperHalfPlaneCoordinate)
    (q : (ℤ × ℤ) × (ℤ × ℤ)) :
    narainMassSq σ ρ (mirrorCharge q) = narainMassSq ρ σ q := by
  rcases q with ⟨⟨a, b⟩, ⟨c, d⟩⟩
  simp only [mirrorCharge, Equiv.coe_fn_mk, narainMassSq, targetQuadratic]
  field_simp [ρ.y_pos.ne', σ.y_pos.ne']
  ring

theorem narainPartitionTerm_mirror (ρ σ : D4BMUpperHalfPlaneCoordinate)
    (x y : ℝ) (q : (ℤ × ℤ) × (ℤ × ℤ)) :
    narainPartitionTerm σ ρ x y (mirrorCharge q) = narainPartitionTerm ρ σ x y q := by
  rw [narainPartitionTerm, narainPartitionTerm, narainBoltzmann, narainBoltzmann,
    narainMassSq_mirror, chargeSpin_mirrorCharge]

/-- The actual partition is symmetric in its two target moduli. -/
theorem narainPartition_mirror (ρ σ : D4BMUpperHalfPlaneCoordinate) (x y : ℝ) :
    narainPartition ρ σ x y = narainPartition σ ρ x y := by
  rw [narainPartition, narainPartition]
  congr 1
  calc
    _ = ∑' q, narainPartitionTerm σ ρ x y (mirrorCharge q) :=
      tsum_congr fun q => (narainPartitionTerm_mirror ρ σ x y q).symm
    _ = _ := mirrorCharge.tsum_eq (narainPartitionTerm σ ρ x y)

#print axioms narainMassSq_mirror
#print axioms narainPartition_mirror
end GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap
