import GaloisForLFunctions.HTGeometry.KerrLowFrequencyGammaCollapse
import GaloisForLFunctions.HTGeometry.KerrNewmanChargedScalarGammaBoundary
import GaloisForLFunctions.HTGeometry.ClockDynamicsUnderdetermination
import GaloisForLFunctions.HTGeometry.ContinuumChronometricGravity

/-!
# Kerr, Kerr--Newman, Einstein-form, and Belinski--Zakharov algebraic bridges

This module formalizes exact algebraic interfaces, not the full differential-geometric proof that
Kerr--Newman solves the Einstein--Maxwell equations.  It gives the Boyer--Lindquist `4 × 4`
metric, identifies the stationary `t--φ` Killing block, proves its denominator-cleared determinant
law, and proves that constant and one-pole unipotent `SL(2, ℝ)` congruences preserve that
determinant and symmetry.  It also formalizes rank-one residues and a nonconstant two-coordinate
nilpotent Lax pair satisfying the zero-curvature equation.  This is a BZ-type algebraic sector,
not a proof of the full spectral-parameter soliton construction or the reduced Einstein--Maxwell
equations.

It also identifies the existing low-frequency Kerr response Gamma ratios with exact
Kerr--Newman response-gap specializations.  These are response-theory identities; they do not
identify the corresponding spacetime metrics.

Finally, the effective-stress identities are tautological unit-coupling Einstein-form equations.
They make precise that a metric and a chosen Einstein tensor do not by themselves select matter;
they do not calculate curvature or establish a physical source model.
-/

open Filter Set Topology Function Complex
open scoped BigOperators Matrix

namespace GaloisForLFunctions.HTGeometry

open Bottcher Polynomial

noncomputable section

open scoped UnivMeroFieldInstances

/-- The low-frequency Kerr right response is the neutral Kerr--Newman Gamma response at the
odd integral effective multipole gap. -/
theorem kerrLowFrequencyRightGammaRatioMero_eq_kerrNewmanNeutral
    (ell : ℕ) :
    kerrLowFrequencyRightGammaRatioMero ell =
      kerrNewmanChargedScalarGammaResponseMero (2 * (ell : ℂ) + 1) := by
  unfold kerrLowFrequencyRightGammaRatioMero
    kerrNewmanChargedScalarGammaResponseMero
  congr 2 <;> ring

/-- The spin-weighted Kerr left response is the same Kerr--Newman Gamma family at its shifted
effective multipole gap. -/
theorem kerrLowFrequencyLeftGammaRatioMero_eq_kerrNewmanGap
    (ell : ℕ) (s : ℤ) :
    kerrLowFrequencyLeftGammaRatioMero ell s =
      kerrNewmanChargedScalarGammaResponseMero
        (2 * (ell : ℂ) + 1 - 2 * (s : ℂ)) := by
  unfold kerrLowFrequencyLeftGammaRatioMero
    kerrNewmanChargedScalarGammaResponseMero
  congr 2 <;> ring

/-- Consequently the Kerr right response has the exact finite Pochhammer normal form already
proved for the neutral Kerr--Newman sector. -/
theorem kerrLowFrequencyRightGammaRatioMero_eq_pochhammer
    (ell : ℕ) :
    kerrLowFrequencyRightGammaRatioMero ell =
      algebraMap (RatFunc ℂ) (meroField Set.univ)
        (gammaOrbitNatFactor (-(ell : ℂ)) (2 * ell + 1)) := by
  rw [kerrLowFrequencyRightGammaRatioMero_eq_kerrNewmanNeutral]
  exact kerrNewmanNeutralScalarGammaResponseMero_eq_pochhammer ell

/-- Standard Boyer--Lindquist quantity `Σ = r² + a² cos² θ`. -/
def kerrNewmanSigma (spin radius polar : ℝ) : ℝ :=
  radius ^ 2 + spin ^ 2 * Real.cos polar ^ 2

/-- Standard Boyer--Lindquist quantity `Δ = r² - 2Mr + a² + Q²`. -/
def kerrNewmanDelta (mass spin charge radius : ℝ) : ℝ :=
  radius ^ 2 - 2 * mass * radius + spin ^ 2 + charge ^ 2

/-- The stationary `t--φ` Killing block of the Boyer--Lindquist Kerr--Newman metric. -/
def kerrNewmanKillingBlock
    (mass spin charge radius polar : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![
    -(kerrNewmanDelta mass spin charge radius - spin ^ 2 * Real.sin polar ^ 2) /
      kerrNewmanSigma spin radius polar,
    -spin * Real.sin polar ^ 2 * (2 * mass * radius - charge ^ 2) /
      kerrNewmanSigma spin radius polar;
    -spin * Real.sin polar ^ 2 * (2 * mass * radius - charge ^ 2) /
      kerrNewmanSigma spin radius polar,
    Real.sin polar ^ 2 * ((radius ^ 2 + spin ^ 2) ^ 2 -
      spin ^ 2 * kerrNewmanDelta mass spin charge radius * Real.sin polar ^ 2) /
      kerrNewmanSigma spin radius polar
  ]

/-- The Killing block is symmetric. -/
theorem kerrNewmanKillingBlock_transpose
    (mass spin charge radius polar : ℝ) :
    Matrix.transpose (kerrNewmanKillingBlock mass spin charge radius polar) =
      kerrNewmanKillingBlock mass spin charge radius polar := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- The standard Killing-block determinant identity in an unconditional cleared-denominator form.
This includes the coordinate-singular locus where Lean's division is totalized. -/
theorem kerrNewmanKillingBlock_det_cleared
    (mass spin charge radius polar : ℝ) :
    kerrNewmanSigma spin radius polar ^ 2 *
        (kerrNewmanKillingBlock mass spin charge radius polar).det =
      -kerrNewmanDelta mass spin charge radius * Real.sin polar ^ 2 *
        kerrNewmanSigma spin radius polar ^ 2 := by
  rw [Matrix.det_fin_two]
  simp [kerrNewmanKillingBlock]
  by_cases hSigma : kerrNewmanSigma spin radius polar = 0
  · simp [hSigma]
  · field_simp [hSigma]
    have htrig : Real.sin polar ^ 2 = 1 - Real.cos polar ^ 2 := by
      nlinarith [Real.sin_sq_add_cos_sq polar]
    rw [htrig]
    simp only [kerrNewmanDelta, kerrNewmanSigma]
    ring

/-- Kerr--Newman metric in Boyer--Lindquist coordinates `(t, r, θ, φ)`, with signature
`(-,+,+,+)` and units `G = c = 1`.  At the coordinate singular locus Lean's totalized division
keeps this algebraic representative globally defined. -/
def kerrNewmanBoyerLindquistMetric
    (mass spin charge radius polar : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  let killing := kerrNewmanKillingBlock mass spin charge radius polar
  !![
    killing 0 0, 0, 0, killing 0 1;
    0, kerrNewmanSigma spin radius polar /
      kerrNewmanDelta mass spin charge radius, 0, 0;
    0, 0, kerrNewmanSigma spin radius polar, 0;
    killing 1 0, 0, 0, killing 1 1
  ]

/-- Kerr is the charge-zero Kerr--Newman specialization. -/
def kerrBoyerLindquistMetric (mass spin radius polar : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  kerrNewmanBoyerLindquistMetric mass spin 0 radius polar

/-- At unit radius on the equatorial slice, the zero mass--spin--charge Kerr--Newman metric is
the corpus's standard Minkowski metric.  This anchors the Boyer--Lindquist representative to the
existing chronometric metric interface. -/
theorem kerrNewmanBoyerLindquistMetric_flatLimit :
    kerrNewmanBoyerLindquistMetric 0 0 0 1 (Real.pi / 2) = minkowskiMetric4 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [kerrNewmanBoyerLindquistMetric, kerrNewmanKillingBlock,
      kerrNewmanSigma, kerrNewmanDelta, minkowskiMetric4]

/-- The full Kerr--Newman metric is symmetric. -/
theorem kerrNewmanBoyerLindquistMetric_transpose
    (mass spin charge radius polar : ℝ) :
    Matrix.transpose (kerrNewmanBoyerLindquistMetric mass spin charge radius polar) =
      kerrNewmanBoyerLindquistMetric mass spin charge radius polar := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- The charge-zero Kerr specialization remains symmetric. -/
theorem kerrBoyerLindquistMetric_transpose
    (mass spin radius polar : ℝ) :
    Matrix.transpose (kerrBoyerLindquistMetric mass spin radius polar) =
      kerrBoyerLindquistMetric mass spin radius polar := by
  exact kerrNewmanBoyerLindquistMetric_transpose mass spin 0 radius polar

/-- Inclusion of the stationary and axial Killing directions into `(t, r, θ, φ)`. -/
def kerrNewmanKillingIndices : Fin 2 → Fin 4 := ![0, 3]

/-- Extracting the `t--φ` sector of the full metric recovers the declared Killing block. -/
theorem kerrNewmanBoyerLindquistMetric_killingBlock
    (mass spin charge radius polar : ℝ) :
    Matrix.submatrix
      (kerrNewmanBoyerLindquistMetric mass spin charge radius polar)
      kerrNewmanKillingIndices kerrNewmanKillingIndices =
      kerrNewmanKillingBlock mass spin charge radius polar := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- The same extraction specializes exactly to Kerr. -/
theorem kerrBoyerLindquistMetric_killingBlock
    (mass spin radius polar : ℝ) :
    Matrix.submatrix
      (kerrBoyerLindquistMetric mass spin radius polar)
      kerrNewmanKillingIndices kerrNewmanKillingIndices =
      kerrNewmanKillingBlock mass spin 0 radius polar :=
  kerrNewmanBoyerLindquistMetric_killingBlock mass spin 0 radius polar

/-- A constant unipotent `SL(2, ℝ)` dressing matrix.  This is the constant algebraic shadow of a
Belinski--Zakharov dressing matrix. -/
def belinskiZakharovUnipotentDressing (parameter : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1, parameter; 0, 1]

/-- Congruence dressing of a stationary two-Killing metric block. -/
def belinskiZakharovDressing
    (dressing metric : Matrix (Fin 2) (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  dressing * metric * Matrix.transpose dressing

/-- The quadratic form carried by a stationary two-Killing metric block. -/
def belinskiZakharovKillingQuadratic
    (metric : Matrix (Fin 2) (Fin 2) ℝ) (vector : Fin 2 → ℝ) : ℝ :=
  dotProduct vector (metric *ᵥ vector)

/-- BZ congruence dressing transports the Killing quadratic form along the transposed dressing.
Consequently its null directions are carried by an explicit linear transformation. -/
theorem belinskiZakharovDressing_killingQuadratic
    (dressing metric : Matrix (Fin 2) (Fin 2) ℝ) (vector : Fin 2 → ℝ) :
    belinskiZakharovKillingQuadratic (belinskiZakharovDressing dressing metric) vector =
      belinskiZakharovKillingQuadratic metric (Matrix.transpose dressing *ᵥ vector) := by
  simp [belinskiZakharovKillingQuadratic, belinskiZakharovDressing, dotProduct,
    Matrix.mulVec, Matrix.mul_apply, Fin.sum_univ_two]
  ring

/-- The elementary dressing is unimodular. -/
theorem belinskiZakharovUnipotentDressing_det (parameter : ℝ) :
    (belinskiZakharovUnipotentDressing parameter).det = 1 := by
  simp [belinskiZakharovUnipotentDressing, Matrix.det_fin_two]

/-- A rank-at-most-one BZ residue written as a column times a row. -/
def belinskiZakharovRankOneResidue
    (column row : Fin 2 → ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.vecMulVec column row

/-- Every column--row BZ residue has zero determinant.  Exact rank one would additionally require
the two factors to be nonzero, which is intentionally not assumed here. -/
theorem belinskiZakharovRankOneResidue_det
    (column row : Fin 2 → ℝ) : (belinskiZakharovRankOneResidue column row).det = 0 := by
  rw [Matrix.det_fin_two]
  simp [belinskiZakharovRankOneResidue, Matrix.vecMulVec]
  ring

/-- The canonical nilpotent rank-one residue used by the unipotent spectral dressing. -/
def belinskiZakharovNilpotentResidue (residue : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![0, residue; 0, 0]

/-- The canonical residue has the declared column--row factorization. -/
theorem belinskiZakharovNilpotentResidue_eq_rankOne (residue : ℝ) :
    belinskiZakharovNilpotentResidue residue =
      belinskiZakharovRankOneResidue ![residue, 0] ![0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [belinskiZakharovNilpotentResidue, belinskiZakharovRankOneResidue,
      Matrix.vecMulVec]

/-- The canonical rank-one residue squares to zero. -/
theorem belinskiZakharovNilpotentResidue_sq (residue : ℝ) :
    belinskiZakharovNilpotentResidue residue *
        belinskiZakharovNilpotentResidue residue = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [belinskiZakharovNilpotentResidue, Matrix.mul_apply, Fin.sum_univ_two]

/-- A one-pole unipotent spectral dressing.  At the pole this totalized algebraic model equals
the identity, so every theorem below is unconditional. -/
def belinskiZakharovOnePoleDressing (spectral pole residue : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  belinskiZakharovUnipotentDressing (residue / (spectral - pole))

/-- Every one-pole unipotent dressing is unimodular. -/
theorem belinskiZakharovOnePoleDressing_det (spectral pole residue : ℝ) :
    (belinskiZakharovOnePoleDressing spectral pole residue).det = 1 :=
  belinskiZakharovUnipotentDressing_det _

/-- Same-pole unipotent dressings add their residues. -/
theorem belinskiZakharovOnePoleDressing_compose
    (spectral pole residue₁ residue₂ : ℝ) :
    belinskiZakharovOnePoleDressing spectral pole residue₁ *
        belinskiZakharovOnePoleDressing spectral pole residue₂ =
      belinskiZakharovOnePoleDressing spectral pole (residue₁ + residue₂) := by
  ext i j
  fin_cases i <;> fin_cases j
  all_goals
    simp [belinskiZakharovOnePoleDressing, belinskiZakharovUnipotentDressing,
      Matrix.mul_apply, Fin.sum_univ_two]
  all_goals ring

/-- Opposite same-pole residues give inverse dressings. -/
theorem belinskiZakharovOnePoleDressing_cancel
    (spectral pole residue : ℝ) :
    belinskiZakharovOnePoleDressing spectral pole residue *
        belinskiZakharovOnePoleDressing spectral pole (-residue) = 1 := by
  rw [belinskiZakharovOnePoleDressing_compose]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [belinskiZakharovOnePoleDressing, belinskiZakharovUnipotentDressing]

/-- A one-pole dressing is identity plus its explicit rank-one nilpotent residue. -/
theorem belinskiZakharovOnePoleDressing_eq_one_add_residue
    (spectral pole residue : ℝ) :
    belinskiZakharovOnePoleDressing spectral pole residue = 1 +
      belinskiZakharovNilpotentResidue (residue / (spectral - pole)) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [belinskiZakharovOnePoleDressing, belinskiZakharovUnipotentDressing,
      belinskiZakharovNilpotentResidue]

/-- Entrywise partial derivative in the radial coordinate.  This coordinatewise definition builds
the finite-matrix derivative layer missing from the pre-existing Lax API. -/
def belinskiZakharovPartialRho
    (F : ℝ → ℝ → Matrix (Fin 2) (Fin 2) ℝ) (rho z : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  fun i j => deriv (fun r => F r z i j) rho

/-- Entrywise partial derivative in the axial coordinate. -/
def belinskiZakharovPartialZ
    (F : ℝ → ℝ → Matrix (Fin 2) (Fin 2) ℝ) (rho z : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  fun i j => deriv (fun w => F rho w i j) z

/-- The zero-curvature residual `∂ρ V - ∂z U + [U,V]` of a two-coordinate BZ-type Lax pair. -/
def belinskiZakharovZeroCurvature
    (U V : ℝ → ℝ → Matrix (Fin 2) (Fin 2) ℝ) (rho z : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  belinskiZakharovPartialRho V rho z - belinskiZakharovPartialZ U rho z +
    U rho z * V rho z - V rho z * U rho z

/-- A nonconstant nilpotent Lax coefficient in the axial coordinate. -/
def belinskiZakharovNilpotentLaxU
    (residue : ℝ) : ℝ → ℝ → Matrix (Fin 2) (Fin 2) ℝ :=
  fun _ z => z • belinskiZakharovNilpotentResidue residue

/-- A nonconstant nilpotent Lax coefficient in the radial coordinate. -/
def belinskiZakharovNilpotentLaxV
    (residue : ℝ) : ℝ → ℝ → Matrix (Fin 2) (Fin 2) ℝ :=
  fun rho _ => rho • belinskiZakharovNilpotentResidue residue

/-- The radial derivative of the nilpotent `V` coefficient is its residue. -/
theorem belinskiZakharovPartialRho_nilpotentLaxV (residue rho z : ℝ) :
    belinskiZakharovPartialRho (belinskiZakharovNilpotentLaxV residue) rho z =
      belinskiZakharovNilpotentResidue residue := by
  ext i j
  change deriv (fun r : ℝ => r * belinskiZakharovNilpotentResidue residue i j) rho =
    belinskiZakharovNilpotentResidue residue i j
  simpa only [id_eq, one_mul] using
    ((hasDerivAt_id rho).mul_const (belinskiZakharovNilpotentResidue residue i j)).deriv

/-- The axial derivative of the nilpotent `U` coefficient is its residue. -/
theorem belinskiZakharovPartialZ_nilpotentLaxU (residue rho z : ℝ) :
    belinskiZakharovPartialZ (belinskiZakharovNilpotentLaxU residue) rho z =
      belinskiZakharovNilpotentResidue residue := by
  ext i j
  change deriv (fun w : ℝ => w * belinskiZakharovNilpotentResidue residue i j) z =
    belinskiZakharovNilpotentResidue residue i j
  simpa only [id_eq, one_mul] using
    ((hasDerivAt_id z).mul_const (belinskiZakharovNilpotentResidue residue i j)).deriv

/-- A nonconstant rank-one BZ-type Lax pair satisfies the exact zero-curvature equation. -/
theorem belinskiZakharovNilpotentLax_zeroCurvature (residue rho z : ℝ) :
    belinskiZakharovZeroCurvature
      (belinskiZakharovNilpotentLaxU residue)
      (belinskiZakharovNilpotentLaxV residue) rho z = 0 := by
  unfold belinskiZakharovZeroCurvature
  rw [belinskiZakharovPartialRho_nilpotentLaxV,
    belinskiZakharovPartialZ_nilpotentLaxU]
  have hUV : belinskiZakharovNilpotentLaxU residue rho z *
      belinskiZakharovNilpotentLaxV residue rho z = 0 := by
    simp only [belinskiZakharovNilpotentLaxU, belinskiZakharovNilpotentLaxV]
    rw [Matrix.smul_mul, Matrix.mul_smul, belinskiZakharovNilpotentResidue_sq]
    simp
  have hVU : belinskiZakharovNilpotentLaxV residue rho z *
      belinskiZakharovNilpotentLaxU residue rho z = 0 := by
    simp only [belinskiZakharovNilpotentLaxU, belinskiZakharovNilpotentLaxV]
    rw [Matrix.smul_mul, Matrix.mul_smul, belinskiZakharovNilpotentResidue_sq]
    simp
  rw [hUV, hVU]
  abel

/-- Congruence dressing changes a metric-block determinant by the square of the dressing
determinant. -/
theorem belinskiZakharovDressing_det
    (dressing metric : Matrix (Fin 2) (Fin 2) ℝ) :
    (belinskiZakharovDressing dressing metric).det =
      dressing.det ^ 2 * metric.det := by
  simp [belinskiZakharovDressing, Matrix.det_mul, pow_two]
  ring

/-- Constant unipotent dressing preserves symmetry of the Kerr--Newman Killing block. -/
theorem belinskiZakharovDressedKerrNewmanKillingBlock_transpose
    (parameter mass spin charge radius polar : ℝ) :
    Matrix.transpose (belinskiZakharovDressing (belinskiZakharovUnipotentDressing parameter)
      (kerrNewmanKillingBlock mass spin charge radius polar)) =
    belinskiZakharovDressing (belinskiZakharovUnipotentDressing parameter)
      (kerrNewmanKillingBlock mass spin charge radius polar) := by
  simp only [belinskiZakharovDressing, Matrix.transpose_mul,
    Matrix.transpose_transpose, kerrNewmanKillingBlock_transpose]
  rw [Matrix.mul_assoc]

/-- Constant unipotent dressing preserves the Kerr--Newman Killing-block determinant. -/
theorem belinskiZakharovDressedKerrNewmanKillingBlock_det
    (parameter mass spin charge radius polar : ℝ) :
    (belinskiZakharovDressing (belinskiZakharovUnipotentDressing parameter)
      (kerrNewmanKillingBlock mass spin charge radius polar)).det =
    (kerrNewmanKillingBlock mass spin charge radius polar).det := by
  rw [belinskiZakharovDressing_det, belinskiZakharovUnipotentDressing_det]
  ring

/-- One-pole unipotent spectral dressing preserves symmetry of the Kerr--Newman Killing block. -/
theorem belinskiZakharovOnePoleDressedKerrNewmanKillingBlock_transpose
    (spectral pole residue mass spin charge radius polar : ℝ) :
    Matrix.transpose (belinskiZakharovDressing
      (belinskiZakharovOnePoleDressing spectral pole residue)
      (kerrNewmanKillingBlock mass spin charge radius polar)) =
    belinskiZakharovDressing (belinskiZakharovOnePoleDressing spectral pole residue)
      (kerrNewmanKillingBlock mass spin charge radius polar) := by
  simp only [belinskiZakharovDressing, Matrix.transpose_mul,
    Matrix.transpose_transpose, kerrNewmanKillingBlock_transpose]
  rw [Matrix.mul_assoc]

/-- One-pole unipotent spectral dressing preserves the Kerr--Newman Killing-block determinant. -/
theorem belinskiZakharovOnePoleDressedKerrNewmanKillingBlock_det
    (spectral pole residue mass spin charge radius polar : ℝ) :
    (belinskiZakharovDressing (belinskiZakharovOnePoleDressing spectral pole residue)
      (kerrNewmanKillingBlock mass spin charge radius polar)).det =
    (kerrNewmanKillingBlock mass spin charge radius polar).det := by
  rw [belinskiZakharovDressing_det, belinskiZakharovOnePoleDressing_det]
  ring

/-- The determinant-normalization law of the Kerr--Newman Killing block survives constant
unipotent BZ-style dressing. -/
theorem belinskiZakharovDressedKerrNewmanKillingBlock_det_cleared
    (parameter mass spin charge radius polar : ℝ) :
    kerrNewmanSigma spin radius polar ^ 2 *
        (belinskiZakharovDressing (belinskiZakharovUnipotentDressing parameter)
          (kerrNewmanKillingBlock mass spin charge radius polar)).det =
      -kerrNewmanDelta mass spin charge radius * Real.sin polar ^ 2 *
        kerrNewmanSigma spin radius polar ^ 2 := by
  rw [belinskiZakharovDressedKerrNewmanKillingBlock_det]
  exact kerrNewmanKillingBlock_det_cleared mass spin charge radius polar

/-- The Kerr--Newman determinant normalization also survives the one-pole spectral dressing. -/
theorem belinskiZakharovOnePoleDressedKerrNewmanKillingBlock_det_cleared
    (spectral pole residue mass spin charge radius polar : ℝ) :
    kerrNewmanSigma spin radius polar ^ 2 *
        (belinskiZakharovDressing (belinskiZakharovOnePoleDressing spectral pole residue)
          (kerrNewmanKillingBlock mass spin charge radius polar)).det =
      -kerrNewmanDelta mass spin charge radius * Real.sin polar ^ 2 *
        kerrNewmanSigma spin radius polar ^ 2 := by
  rw [belinskiZakharovOnePoleDressedKerrNewmanKillingBlock_det]
  exact kerrNewmanKillingBlock_det_cleared mass spin charge radius polar

/-- The determinant preservation specializes from Kerr--Newman to Kerr. -/
theorem belinskiZakharovDressedKerrKillingBlock_det
    (parameter mass spin radius polar : ℝ) :
    (belinskiZakharovDressing (belinskiZakharovUnipotentDressing parameter)
      (kerrNewmanKillingBlock mass spin 0 radius polar)).det =
    (kerrNewmanKillingBlock mass spin 0 radius polar).det :=
  belinskiZakharovDressedKerrNewmanKillingBlock_det
    parameter mass spin 0 radius polar

/-- The unit-coupling effective stress tensor of the stationary Kerr--Newman Killing block. -/
def kerrNewmanKillingEffectiveStress
    (cosmological : ℝ) (einstein : Matrix (Fin 2) (Fin 2) ℝ)
    (mass spin charge radius polar : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  effectiveStressTensor (K := ℝ) (Tensor := Matrix (Fin 2) (Fin 2) ℝ) 1 cosmological einstein
    (kerrNewmanKillingBlock mass spin charge radius polar)

/-- Unit-coupling Einstein-form identity for the Killing block. -/
theorem kerrNewmanKillingBlock_einsteinEquation
    (cosmological : ℝ) (einstein : Matrix (Fin 2) (Fin 2) ℝ)
    (mass spin charge radius polar : ℝ) :
    einstein + cosmological • kerrNewmanKillingBlock mass spin charge radius polar =
      kerrNewmanKillingEffectiveStress cosmological einstein mass spin charge radius polar := by
  simp [kerrNewmanKillingEffectiveStress, effectiveStressTensor]

/-- The unit-coupling effective stress tensor of the full Kerr--Newman metric. -/
def kerrNewmanEffectiveStress
    (cosmological : ℝ) (einstein : Matrix (Fin 4) (Fin 4) ℝ)
    (mass spin charge radius polar : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  effectiveStressTensor (K := ℝ) (Tensor := Matrix (Fin 4) (Fin 4) ℝ) 1 cosmological einstein
    (kerrNewmanBoyerLindquistMetric mass spin charge radius polar)

/-- Unit-coupling Einstein-form identity for the full Kerr--Newman metric. -/
theorem kerrNewmanBoyerLindquistMetric_einsteinEquation
    (cosmological : ℝ) (einstein : Matrix (Fin 4) (Fin 4) ℝ)
    (mass spin charge radius polar : ℝ) :
    einstein + cosmological • kerrNewmanBoyerLindquistMetric mass spin charge radius polar =
      kerrNewmanEffectiveStress cosmological einstein mass spin charge radius polar := by
  simp [kerrNewmanEffectiveStress, effectiveStressTensor]

/-- The full Einstein-form identity specializes exactly from Kerr--Newman to Kerr. -/
theorem kerrBoyerLindquistMetric_einsteinEquation
    (cosmological : ℝ) (einstein : Matrix (Fin 4) (Fin 4) ℝ)
    (mass spin radius polar : ℝ) :
    einstein + cosmological • kerrBoyerLindquistMetric mass spin radius polar =
      kerrNewmanEffectiveStress cosmological einstein mass spin 0 radius polar := by
  exact kerrNewmanBoyerLindquistMetric_einsteinEquation
    cosmological einstein mass spin 0 radius polar

end

end GaloisForLFunctions.HTGeometry
