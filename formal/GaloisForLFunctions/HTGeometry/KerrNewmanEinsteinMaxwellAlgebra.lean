import GaloisForLFunctions.HTGeometry.KerrNewmanBelinskiZakharovBridge

/-!
# Algebraic Einstein--Maxwell data on the flat Kerr--Newman background

This module adds an explicit canonical electromagnetic two-form and its mixed stress tensor in the
`(-,+,+,+)` frame already selected by the flat Kerr--Newman limit.  It proves the algebraic
Maxwell/Rainich identities and an exact Einstein-form decomposition.  It does not calculate the
curvature of Kerr--Newman or prove the Einstein--Maxwell field equations for that metric.
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix
open scoped Matrix

/-- Signature signs of the flat Kerr--Newman orthonormal frame. -/
def kerrNewmanFlatFrameSign : Fin 4 → ℝ := ![-1, 1, 1, 1]

/-- The frame signs are the diagonal entries of the existing flat Kerr--Newman metric. -/
theorem kerrNewmanFlatFrameSign_eq_flatMetricDiagonal (i : Fin 4) :
    kerrNewmanFlatFrameSign i =
      kerrNewmanBoyerLindquistMetric 0 0 0 1 (Real.pi / 2) i i := by
  rw [kerrNewmanBoyerLindquistMetric_flatLimit]
  fin_cases i <;>
    norm_num [kerrNewmanFlatFrameSign, minkowskiMetric4]

/-- A canonical electromagnetic two-form with parallel electric and magnetic amplitudes. -/
def kerrNewmanCanonicalMaxwellTwoForm
    (electric magnetic : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![0, electric, 0, 0;
     -electric, 0, 0, 0;
     0, 0, 0, magnetic;
     0, 0, -magnetic, 0]

/-- The canonical electromagnetic tensor is antisymmetric. -/
theorem kerrNewmanCanonicalMaxwellTwoForm_transpose (electric magnetic : ℝ) :
    (kerrNewmanCanonicalMaxwellTwoForm electric magnetic)ᵀ =
      -kerrNewmanCanonicalMaxwellTwoForm electric magnetic := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [kerrNewmanCanonicalMaxwellTwoForm, Matrix.transpose_apply]

/-- Raise both indices using the flat Kerr--Newman frame signs. -/
def kerrNewmanRaiseBothIndices
    (F : Matrix (Fin 4) (Fin 4) ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  fun i j => kerrNewmanFlatFrameSign i * kerrNewmanFlatFrameSign j * F i j

/-- Lorentzian quadratic invariant `FₘₙF⁽ᵐⁿ⁾`. -/
def kerrNewmanTwoFormQuadraticInvariant (F : Matrix (Fin 4) (Fin 4) ℝ) : ℝ :=
  ∑ i, ∑ j, kerrNewmanRaiseBothIndices F i j * F i j

/-- Mixed Maxwell stress tensor in the flat Kerr--Newman frame. -/
noncomputable def kerrNewmanMaxwellStressMixed
    (F : Matrix (Fin 4) (Fin 4) ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  fun i j =>
    (∑ r, kerrNewmanRaiseBothIndices F i r * F j r) -
      (1 / 4 : ℝ) * (1 : Matrix (Fin 4) (Fin 4) ℝ) i j *
        kerrNewmanTwoFormQuadraticInvariant F

/-- Nonnegative energy-density magnitude of the canonical field. -/
noncomputable def kerrNewmanCanonicalMaxwellStressMagnitude
    (electric magnetic : ℝ) : ℝ :=
  (electric ^ 2 + magnetic ^ 2) / 2

/-- Canonical mixed Maxwell stress: negative on its Lorentzian principal plane and positive on its
spacelike complement. -/
noncomputable def kerrNewmanCanonicalMaxwellStress
    (electric magnetic : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  let rho := kerrNewmanCanonicalMaxwellStressMagnitude electric magnetic
  !![-rho, 0, 0, 0;
     0, -rho, 0, 0;
     0, 0, rho, 0;
     0, 0, 0, rho]

/-- Direct invariant calculation for the canonical Maxwell two-form. -/
theorem kerrNewmanCanonicalMaxwellTwoForm_invariant (electric magnetic : ℝ) :
    kerrNewmanTwoFormQuadraticInvariant (kerrNewmanCanonicalMaxwellTwoForm electric magnetic) =
      2 * (magnetic ^ 2 - electric ^ 2) := by
  simp [kerrNewmanTwoFormQuadraticInvariant, kerrNewmanRaiseBothIndices,
    kerrNewmanCanonicalMaxwellTwoForm, kerrNewmanFlatFrameSign, Fin.sum_univ_succ]
  ring

/-- The canonical two-form realizes its declared mixed Maxwell stress tensor. -/
theorem kerrNewmanMaxwellStressMixed_canonical (electric magnetic : ℝ) :
    kerrNewmanMaxwellStressMixed (kerrNewmanCanonicalMaxwellTwoForm electric magnetic) =
      kerrNewmanCanonicalMaxwellStress electric magnetic := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [kerrNewmanMaxwellStressMixed, kerrNewmanCanonicalMaxwellStress,
      kerrNewmanCanonicalMaxwellStressMagnitude, kerrNewmanTwoFormQuadraticInvariant,
      kerrNewmanRaiseBothIndices, kerrNewmanCanonicalMaxwellTwoForm,
      kerrNewmanFlatFrameSign, Fin.sum_univ_succ] <;> ring

/-- The canonical Maxwell stress obeys the algebraic Rainich square law. -/
theorem kerrNewmanCanonicalMaxwellStress_sq (electric magnetic : ℝ) :
    kerrNewmanCanonicalMaxwellStress electric magnetic *
        kerrNewmanCanonicalMaxwellStress electric magnetic =
      kerrNewmanCanonicalMaxwellStressMagnitude electric magnetic ^ 2 •
        (1 : Matrix (Fin 4) (Fin 4) ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, kerrNewmanCanonicalMaxwellStress,
      kerrNewmanCanonicalMaxwellStressMagnitude, Fin.sum_univ_succ] <;> ring

/-- The canonical Maxwell stress can be nilpotent only when both electromagnetic amplitudes
vanish.  Thus it cannot be identified with a nonzero nilpotent BZ residue. -/
theorem kerrNewmanCanonicalMaxwellStress_sq_eq_zero_iff
    (electric magnetic : ℝ) :
    kerrNewmanCanonicalMaxwellStress electric magnetic *
        kerrNewmanCanonicalMaxwellStress electric magnetic = 0 ↔
      electric = 0 ∧ magnetic = 0 := by
  constructor
  · intro h
    have h00 := congrFun (congrFun h 0) 0
    simp [Matrix.mul_apply, kerrNewmanCanonicalMaxwellStress,
      kerrNewmanCanonicalMaxwellStressMagnitude, Fin.sum_univ_succ] at h00
    have hsum : electric ^ 2 + magnetic ^ 2 = 0 := by
      nlinarith [sq_nonneg (electric ^ 2 + magnetic ^ 2)]
    have helectricSq : electric ^ 2 = 0 := by
      nlinarith [sq_nonneg magnetic]
    have hmagneticSq : magnetic ^ 2 = 0 := by
      nlinarith [sq_nonneg electric]
    exact ⟨(sq_eq_zero_iff).mp helectricSq, (sq_eq_zero_iff).mp hmagneticSq⟩
  · rintro ⟨rfl, rfl⟩
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [kerrNewmanCanonicalMaxwellStress,
        kerrNewmanCanonicalMaxwellStressMagnitude]

/-- The canonical Maxwell stress is tracefree. -/
theorem kerrNewmanCanonicalMaxwellStress_trace (electric magnetic : ℝ) :
    Matrix.trace (kerrNewmanCanonicalMaxwellStress electric magnetic) = 0 := by
  simp [Matrix.trace, kerrNewmanCanonicalMaxwellStress,
    kerrNewmanCanonicalMaxwellStressMagnitude, Fin.sum_univ_succ]
  ring

/-- The canonical energy density is nonnegative in the `(-,+,+,+)` convention. -/
theorem kerrNewmanCanonicalMaxwellStress_energy_nonneg (electric magnetic : ℝ) :
    0 ≤ -kerrNewmanCanonicalMaxwellStress electric magnetic 0 0 := by
  simp [kerrNewmanCanonicalMaxwellStress, kerrNewmanCanonicalMaxwellStressMagnitude]
  positivity

/-- An Einstein-tensor representative whose Einstein-form source is the canonical Maxwell stress
on the flat Kerr--Newman background.  This is an algebraic construction, not a curvature result. -/
noncomputable def kerrNewmanFlatLimitCanonicalEinsteinTensor
    (cosmological electric magnetic : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  kerrNewmanCanonicalMaxwellStress electric magnetic - cosmological •
    kerrNewmanBoyerLindquistMetric 0 0 0 1 (Real.pi / 2)

/-- Closed unit-coupling Einstein-form equation for the explicit flat-background Maxwell source. -/
theorem kerrNewmanFlatLimit_canonicalMaxwellEinsteinEquation
    (cosmological electric magnetic : ℝ) :
    kerrNewmanFlatLimitCanonicalEinsteinTensor cosmological electric magnetic +
        cosmological • kerrNewmanBoyerLindquistMetric 0 0 0 1 (Real.pi / 2) =
      kerrNewmanCanonicalMaxwellStress electric magnetic := by
  simp [kerrNewmanFlatLimitCanonicalEinsteinTensor]

/-- A basis-free rank-one scalar endomorphism, suitable for scalar-source contributions to an
Einstein--Maxwell decomposition. -/
def einsteinMaxwellRankOneEndomorphism
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (functional : E →ₗ[ℝ] ℝ) (vector : E) : Module.End ℝ E :=
  functional.smulRight vector

/-- A rank-one scalar endomorphism squares to its contraction times itself. -/
theorem einsteinMaxwellRankOneEndomorphism_sq
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (functional : E →ₗ[ℝ] ℝ) (vector : E) :
    einsteinMaxwellRankOneEndomorphism functional vector *
        einsteinMaxwellRankOneEndomorphism functional vector =
      functional vector • einsteinMaxwellRankOneEndomorphism functional vector := by
  ext y
  simp [einsteinMaxwellRankOneEndomorphism, smul_smul, mul_comm]

/-- In finite free dimension, the rank-one square coefficient is its trace. -/
theorem einsteinMaxwellRankOneEndomorphism_sq_eq_trace_smul
    {E : Type*} [AddCommGroup E] [Module ℝ E] [Module.Free ℝ E] [Module.Finite ℝ E]
    (functional : E →ₗ[ℝ] ℝ) (vector : E) :
    einsteinMaxwellRankOneEndomorphism functional vector *
        einsteinMaxwellRankOneEndomorphism functional vector =
      LinearMap.trace ℝ E (einsteinMaxwellRankOneEndomorphism functional vector) •
        einsteinMaxwellRankOneEndomorphism functional vector := by
  rw [einsteinMaxwellRankOneEndomorphism_sq]
  simp [einsteinMaxwellRankOneEndomorphism]

end GaloisForLFunctions.HTGeometry
