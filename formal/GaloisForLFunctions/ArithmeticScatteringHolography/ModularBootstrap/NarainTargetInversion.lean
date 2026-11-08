import GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap.NarainPartition
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMEisensteinModularGeneratorInvariance

/-!
# Target inversion of the Narain partition

A quarter-turn momentum-winding exchange preserves spin and intertwines
the masses at inverse area moduli. Reindexing gives exact partition invariance.
-/

open Complex RHTower
set_option autoImplicit false
noncomputable section
namespace GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap

/-- Momentum-winding exchange with the quarter-turn required by the area convention. -/
def targetInversionCharge : ((ℤ × ℤ) × (ℤ × ℤ)) ≃ ((ℤ × ℤ) × (ℤ × ℤ)) where
  toFun q := ((q.2.2, -q.2.1), (q.1.2, -q.1.1))
  invFun q := ((-q.2.2, q.2.1), (-q.1.2, q.1.1))
  left_inv q := by rcases q with ⟨⟨a,b⟩,⟨c,d⟩⟩; simp
  right_inv q := by rcases q with ⟨⟨a,b⟩,⟨c,d⟩⟩; simp

theorem chargeSpin_targetInversionCharge (q : (ℤ × ℤ) × (ℤ × ℤ)) :
    chargeSpin (targetInversionCharge q) = chargeSpin q := by
  simp only [targetInversionCharge, Equiv.coe_fn_mk, chargeSpin]
  ring

theorem narainMassSq_targetInversion (ρ σ : D4BMUpperHalfPlaneCoordinate)
    (q : (ℤ × ℤ) × (ℤ × ℤ)) :
    narainMassSq (d4BMEisensteinInvertCoordinate ρ) σ (targetInversionCharge q) = narainMassSq ρ σ q := by
  have hR : ρ.x ^ 2 + ρ.y ^ 2 ≠ 0 :=
    (add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_pos ρ.y_pos)).ne'
  dsimp only [narainMassSq, targetQuadratic, d4BMEisensteinInvertCoordinate, targetInversionCharge,
    Equiv.coe_fn_mk]
  push_cast
  field_simp [hR, ρ.y_pos.ne', σ.y_pos.ne']
  ring

/-- Target modular inversion preserves each term after an explicit charge permutation. -/
theorem narainPartitionTerm_targetInversion (ρ σ : D4BMUpperHalfPlaneCoordinate)
    (x y : ℝ) (q : (ℤ × ℤ) × (ℤ × ℤ)) :
    narainPartitionTerm (d4BMEisensteinInvertCoordinate ρ) σ x y (targetInversionCharge q) =
      narainPartitionTerm ρ σ x y q := by
  simp only [narainPartitionTerm, narainBoltzmann, narainMassSq_targetInversion,
    chargeSpin_targetInversionCharge]

/-- The area modulus has exact modular inversion symmetry. -/
theorem narainPartition_targetInversion (ρ σ : D4BMUpperHalfPlaneCoordinate) (x y : ℝ) :
    narainPartition (d4BMEisensteinInvertCoordinate ρ) σ x y = narainPartition ρ σ x y := by
  unfold narainPartition
  congr 1
  rw [← targetInversionCharge.tsum_eq (narainPartitionTerm (d4BMEisensteinInvertCoordinate ρ) σ x y)]
  exact tsum_congr fun q => narainPartitionTerm_targetInversion ρ σ x y q

#print axioms narainMassSq_targetInversion
#print axioms narainPartition_targetInversion
end GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap
