import GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap.NarainPoissonTerms
import GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap.NarainTargetInversion

/-!
# Narain triality and worldsheet inversion

Momentum Poisson summation exchanges the area and worldsheet moduli.
Absolute convergence permits both charge-sum rearrangements. Combining
this exchange with target charge duality gives modular inversion.
-/

open Complex RHTower
open GaloisForLFunctions.HTGeometry.IntegerLatticePoisson
open GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap
set_option autoImplicit false
noncomputable section
namespace GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap

/-- The dual momentum-winding charge in the exchanged Narain sum. -/
def trialityCharge : ((ℤ × ℤ) × (ℤ × ℤ)) ≃ ((ℤ × ℤ) × (ℤ × ℤ)) where
  toFun q := ((q.1.2, -q.1.1), (-q.2.1, -q.2.2))
  invFun q := ((-q.1.2, q.1.1), (-q.2.1, -q.2.2))
  left_inv q := by rcases q with ⟨⟨a,b⟩,⟨c,d⟩⟩; simp
  right_inv q := by rcases q with ⟨⟨a,b⟩,⟨c,d⟩⟩; simp

/-- Poisson summation in momentum, with winding fixed. -/
theorem narainPartitionTerm_tsum_momentum (ρ σ τ : D4BMUpperHalfPlaneCoordinate)
    (w : ℤ × ℤ) :
    (∑' n : ℤ × ℤ, narainPartitionTerm ρ σ τ.x τ.y (n, w)) =
      ((ρ.y / τ.y : ℝ) : ℂ) *
        ∑' m : ℤ × ℤ, narainPartitionTerm τ σ ρ.x ρ.y (trialityCharge (m, w)) := by
  have ht : 0 < τ.y / (ρ.y * σ.y) := div_pos τ.y_pos (mul_pos ρ.y_pos σ.y_pos)
  have hp := gaussian_theta_characteristics (targetLatticeEquiv σ) ht
    (targetLatticeEquiv σ (ρ.x • integerPairVector (w.2, -w.1)))
    (τ.x • inverseAdjoint (targetLatticeEquiv σ) (integerPairVector w))
  simp only [latticeScale_targetLatticeEquiv, finrank_euclideanSpace_fin] at hp
  norm_num only [Nat.cast_ofNat, div_self (two_ne_zero : (2 : ℝ) ≠ 0),
    Real.rpow_neg_one] at hp
  simp only [Complex.real_smul] at hp
  have hc : ((σ.y⁻¹ : ℝ) : ℂ) * (((τ.y / (ρ.y * σ.y))⁻¹ : ℝ) : ℂ) =
      ((ρ.y / τ.y : ℝ) : ℂ) := by
    push_cast
    field_simp [Complex.ofReal_ne_zero.mpr σ.y_pos.ne',
      Complex.ofReal_ne_zero.mpr τ.y_pos.ne']
  simp only [← mul_assoc, hc] at hp
  calc
    _ = narainWindingWeight ρ σ τ w *
        (∑' n : ℤ × ℤ, gaussianModulation (Real.pi * (τ.y / (ρ.y * σ.y)))
          (τ.x • inverseAdjoint (targetLatticeEquiv σ) (integerPairVector w))
          (targetLatticeEquiv σ (integerPairVector n) +
            targetLatticeEquiv σ (ρ.x • integerPairVector (w.2, -w.1)))) := by
      simp only [narainPartitionTerm_eq_gaussian, tsum_mul_left]
    _ = _ := by
      rw [tsum_integerPairVector (fun v =>
        gaussianModulation (Real.pi * (τ.y / (ρ.y * σ.y)))
          (τ.x • inverseAdjoint (targetLatticeEquiv σ) (integerPairVector w))
          (targetLatticeEquiv σ v +
            targetLatticeEquiv σ (ρ.x • integerPairVector (w.2, -w.1)))), hp,
        ← tsum_integerPairVector (fun v =>
          latticePhase (targetLatticeEquiv σ (ρ.x • integerPairVector (w.2, -w.1)))
            (inverseAdjoint (targetLatticeEquiv σ) v) *
          gaussianKernel (Real.pi / (τ.y / (ρ.y * σ.y)))
            (inverseAdjoint (targetLatticeEquiv σ) v -
              τ.x • inverseAdjoint (targetLatticeEquiv σ) (integerPairVector w)))]
      simp only [trialityCharge, Equiv.coe_fn_mk, narainPartitionTerm_eq_dual_gaussian,
        tsum_mul_left]
      ring

private theorem tsum_charge_reverse (f : ((ℤ × ℤ) × (ℤ × ℤ)) → ℂ)
    (hf : Summable f) :
    (∑' w : ℤ × ℤ, ∑' n : ℤ × ℤ, f (n, w)) = ∑' q, f q := by
  calc
    _ = ∑' q : ((ℤ × ℤ) × (ℤ × ℤ)), f q.swap := hf.prod_symm.tsum_prod.symm
    _ = _ := (Equiv.prodComm (ℤ × ℤ) (ℤ × ℤ)).tsum_eq f

private theorem tsum_trialityCharge (f : ((ℤ × ℤ) × (ℤ × ℤ)) → ℂ) :
    (∑' q, f (trialityCharge q)) = ∑' q, f q := trialityCharge.tsum_eq f

private theorem narainPartitionTerm_tsum_triality (ρ σ τ : D4BMUpperHalfPlaneCoordinate) :
    (∑' q, narainPartitionTerm ρ σ τ.x τ.y q) =
      ((ρ.y / τ.y : ℝ) : ℂ) * ∑' q, narainPartitionTerm τ σ ρ.x ρ.y q := by
  have hs := summable_narainPartitionTerm ρ σ τ.x τ.y_pos
  have hd : Summable (fun q => narainPartitionTerm τ σ ρ.x ρ.y (trialityCharge q)) :=
    (summable_narainPartitionTerm τ σ ρ.x ρ.y_pos).comp_injective trialityCharge.injective
  rw [← tsum_charge_reverse (narainPartitionTerm ρ σ τ.x τ.y) hs]
  simp only [narainPartitionTerm_tsum_momentum, tsum_mul_left]
  rw [tsum_charge_reverse (fun q => narainPartitionTerm τ σ ρ.x ρ.y (trialityCharge q)) hd,
    tsum_trialityCharge (narainPartitionTerm τ σ ρ.x ρ.y)]

/-- Exchanging the area and worldsheet moduli preserves the actual partition function. -/
theorem narainPartition_triality (ρ σ τ : D4BMUpperHalfPlaneCoordinate) :
    narainPartition ρ σ τ.x τ.y = narainPartition τ σ ρ.x ρ.y := by
  rw [narainPartition, narainPartition, narainPartitionTerm_tsum_triality]
  push_cast
  field_simp [Complex.ofReal_ne_zero.mpr τ.y_pos.ne']

/-- Modular inversion follows from triality and target charge duality. -/
theorem narainPartition_worldsheetInversion (ρ σ τ : D4BMUpperHalfPlaneCoordinate) :
    narainPartition ρ σ (d4BMEisensteinInvertCoordinate τ).x
      (d4BMEisensteinInvertCoordinate τ).y = narainPartition ρ σ τ.x τ.y := by
  rw [narainPartition_triality, narainPartition_targetInversion,
    narainPartition_triality τ σ ρ]

#print axioms narainPartition_triality
#print axioms narainPartition_worldsheetInversion
end GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap
