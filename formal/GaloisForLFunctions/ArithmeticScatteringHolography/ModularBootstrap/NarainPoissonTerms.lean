import GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap.NarainPoissonCoordinates
import GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap.NarainPartition

/-!
# Gaussian characteristics of the Narain momentum sum

The momentum and dual momentum summands are affine Gaussian kernels for the
target lattice. Their exact phases identify the exchange of area and worldsheet
moduli under Poisson summation.
-/

open Complex RHTower
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.IntegerLatticePoisson
open GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap
set_option autoImplicit false
noncomputable section
namespace GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap

local notation "E" => EuclideanSpace ℝ (Fin 2)

/-- The winding Gaussian left outside momentum Poisson summation. -/
def narainWindingWeight (ρ σ τ : D4BMUpperHalfPlaneCoordinate) (w : ℤ × ℤ) : ℂ :=
  Complex.exp (-(Real.pi * τ.y * ρ.y / σ.y *
    targetQuadratic σ ((w.2 : ℝ), -(w.1 : ℝ)) : ℝ))

private theorem inner_target_dual (σ : D4BMUpperHalfPlaneCoordinate) (p q : ℤ × ℤ) :
    inner ℝ (targetLatticeEquiv σ (integerPairVector p))
      (inverseAdjoint (targetLatticeEquiv σ) (integerPairVector q)) =
      (p.1 : ℝ) * q.1 + (p.2 : ℝ) * q.2 := by
  rw [inverseAdjoint, ContinuousLinearMap.adjoint_inner_right]
  change inner ℝ ((targetLatticeEquiv σ).symm
    (targetLatticeEquiv σ (integerPairVector p))) (integerPairVector q) = _
  rw [ContinuousLinearEquiv.symm_apply_apply, inner_integerPairVector]

private theorem norm_target_affine_sq (ρ σ : D4BMUpperHalfPlaneCoordinate)
    (n w : ℤ × ℤ) :
    ‖targetLatticeEquiv σ (integerPairVector n) +
      targetLatticeEquiv σ (ρ.x • integerPairVector (w.2, -w.1))‖ ^ 2 =
      targetQuadratic σ ((n.1 : ℝ) + ρ.x * w.2, (n.2 : ℝ) - ρ.x * w.1) := by
  rw [← map_add, norm_targetLatticeEquiv_sq]
  simp [integerPairVector, sub_eq_add_neg]

private theorem norm_target_dual_shift_sq (σ τ : D4BMUpperHalfPlaneCoordinate)
    (m w : ℤ × ℤ) :
    ‖inverseAdjoint (targetLatticeEquiv σ) (integerPairVector m) -
      τ.x • inverseAdjoint (targetLatticeEquiv σ) (integerPairVector w)‖ ^ 2 =
      (((m.1 : ℝ) - τ.x * w.1 + σ.x * ((m.2 : ℝ) - τ.x * w.2)) ^ 2 +
        σ.y ^ 2 * ((m.2 : ℝ) - τ.x * w.2) ^ 2) / σ.y ^ 2 := by
  rw [← map_smul, ← map_sub, norm_inverseAdjoint_targetLatticeEquiv_sq]
  simp [integerPairVector]

/-- The momentum summand has exactly the affine Gaussian characteristics. -/
theorem narainPartitionTerm_eq_gaussian (ρ σ τ : D4BMUpperHalfPlaneCoordinate)
    (n w : ℤ × ℤ) :
    narainPartitionTerm ρ σ τ.x τ.y (n, w) =
      narainWindingWeight ρ σ τ w *
        gaussianModulation (Real.pi * (τ.y / (ρ.y * σ.y)))
          (τ.x • inverseAdjoint (targetLatticeEquiv σ) (integerPairVector w))
          (targetLatticeEquiv σ (integerPairVector n) +
            targetLatticeEquiv σ (ρ.x • integerPairVector (w.2, -w.1))) := by
  have hphase : inner ℝ
      (targetLatticeEquiv σ (integerPairVector n) +
        targetLatticeEquiv σ (ρ.x • integerPairVector (w.2, -w.1)))
      (τ.x • inverseAdjoint (targetLatticeEquiv σ) (integerPairVector w)) =
        τ.x * ((n.1 : ℝ) * w.1 + (n.2 : ℝ) * w.2) := by
    rw [real_inner_smul_right, inner_add_left, inner_target_dual,
      inner_target_shift_winding, add_zero]
  simp only [narainPartitionTerm, narainBoltzmann, fourierChar,
    Complex.ofReal_exp, narainWindingWeight, gaussianModulation, latticePhase,
    IntegerLatticePoisson.gaussianKernel, ← Complex.ofReal_pow, hphase,
    norm_target_affine_sq, ← Complex.exp_add]
  congr 1
  dsimp only [narainMassSq, chargeSpin]
  push_cast
  field_simp [Complex.ofReal_ne_zero.mpr ρ.y_pos.ne',
    Complex.ofReal_ne_zero.mpr σ.y_pos.ne']
  ring

/-- Momentum Poisson summation exchanges the area and worldsheet moduli. -/
theorem narainPartitionTerm_eq_dual_gaussian (ρ σ τ : D4BMUpperHalfPlaneCoordinate)
    (m w : ℤ × ℤ) :
    narainPartitionTerm τ σ ρ.x ρ.y ((m.2, -m.1), (-w.1, -w.2)) =
      narainWindingWeight ρ σ τ w *
        (latticePhase (targetLatticeEquiv σ (ρ.x • integerPairVector (w.2, -w.1)))
          (inverseAdjoint (targetLatticeEquiv σ) (integerPairVector m)) *
        IntegerLatticePoisson.gaussianKernel (Real.pi / (τ.y / (ρ.y * σ.y)))
          (inverseAdjoint (targetLatticeEquiv σ) (integerPairVector m) -
            τ.x • inverseAdjoint (targetLatticeEquiv σ) (integerPairVector w))) := by
  simp only [narainPartitionTerm, narainBoltzmann, fourierChar,
    Complex.ofReal_exp, narainWindingWeight, latticePhase, IntegerLatticePoisson.gaussianKernel,
    ← Complex.ofReal_pow, inner_target_shift_dual, norm_target_dual_shift_sq, ← Complex.exp_add]
  congr 1
  dsimp only [narainMassSq, targetQuadratic, chargeSpin]
  push_cast
  field_simp [Complex.ofReal_ne_zero.mpr ρ.y_pos.ne',
    Complex.ofReal_ne_zero.mpr σ.y_pos.ne', Complex.ofReal_ne_zero.mpr τ.y_pos.ne']
  ring

#print axioms narainPartitionTerm_eq_gaussian
#print axioms narainPartitionTerm_eq_dual_gaussian
end GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap
