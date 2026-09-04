import Mathlib

/-!
# Spin-torsion correlator scaling

The separated vacuum correlator has a negative sign, quadratic family multiplicity, inverse-volume
dependence, and inverse-sixth separation dependence.  Encoding positive physical parameters by
exponentials makes the strict sign theorem unconditional.  The finite-density correction depends
only on the dimensionless product of chemical potential and separation; its evenness and reciprocal
scale invariance are exact.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- Channel-reduced separated spin-torsion correlator. -/
def vacuumSpinTorsionCorrelator (dR family volume separation : ℝ) : ℝ :=
  -12 * dR * family ^ 2 / (Real.pi ^ 4 * volume * separation ^ 6)

/-- The separated correlator is strictly negative for positive dimension, family scale, volume,
and separation. -/
theorem vacuumSpinTorsionCorrelator_exp_neg (d n v r : ℝ) :
    vacuumSpinTorsionCorrelator (Real.exp d) (Real.exp n) (Real.exp v) (Real.exp r) < 0 := by
  unfold vacuumSpinTorsionCorrelator
  apply div_neg_of_neg_of_pos
  · have h : 0 < 12 * Real.exp d * Real.exp n ^ 2 := by positivity
    nlinarith
  · positivity

/-- No chiral families give no zero-mode correlator. -/
theorem vacuumSpinTorsionCorrelator_zero_family (dR volume separation : ℝ) :
    vacuumSpinTorsionCorrelator dR 0 volume separation = 0 := by
  simp [vacuumSpinTorsionCorrelator]

/-- The correlator cannot distinguish orientation of the signed family coordinate. -/
theorem vacuumSpinTorsionCorrelator_neg_family (dR family volume separation : ℝ) :
    vacuumSpinTorsionCorrelator dR (-family) volume separation =
      vacuumSpinTorsionCorrelator dR family volume separation := by
  simp [vacuumSpinTorsionCorrelator]

/-- Family rescaling acts quadratically on the correlator. -/
theorem vacuumSpinTorsionCorrelator_family_scale
    (dR family volume separation scale : ℝ) :
    vacuumSpinTorsionCorrelator dR (scale * family) volume separation =
      scale ^ 2 * vacuumSpinTorsionCorrelator dR family volume separation := by
  unfold vacuumSpinTorsionCorrelator
  ring

/-- A log-separation translation acts with weight `-6`. -/
theorem vacuumSpinTorsionCorrelator_logSeparationShift
    (dR family volume r shift : ℝ) :
    vacuumSpinTorsionCorrelator dR family volume (Real.exp (r + shift)) =
      Real.exp (-6 * shift) *
        vacuumSpinTorsionCorrelator dR family volume (Real.exp r) := by
  unfold vacuumSpinTorsionCorrelator
  rw [Real.exp_add, mul_pow]
  rw [show Real.exp shift ^ 6 = Real.exp (6 * shift) by
    simpa using (Real.exp_nat_mul shift 6).symm]
  rw [show -6 * shift = -(6 * shift) by ring, Real.exp_neg]
  field_simp [Real.exp_ne_zero]

/-- Radius dependence of the six-dimensional product volume, up to its fixed geometric constant. -/
def compactificationVolumeShape (a1 a2 : ℝ) : ℝ := a1 ^ 2 * a2 ^ 4

/-- Independent radius dilations have bidegree `(2,4)`. -/
theorem compactificationVolumeShape_scale (a1 a2 s t : ℝ) :
    compactificationVolumeShape (s * a1) (t * a2) =
      s ^ 2 * t ^ 4 * compactificationVolumeShape a1 a2 := by
  unfold compactificationVolumeShape
  ring

/-- Family-weighted inverse-volume binding term in the radion potential. -/
def spinTorsionRadionTerm (C family a1 a2 : ℝ) : ℝ :=
  -C * family ^ 2 / compactificationVolumeShape a1 a2

/-- On the isotropic ray the torsion term has inverse-sixth homogeneity. -/
theorem spinTorsionRadionTerm_isotropic (C family d : ℝ) :
    spinTorsionRadionTerm C family d d = -C * family ^ 2 / d ^ 6 := by
  unfold spinTorsionRadionTerm compactificationVolumeShape
  ring

/-- A common log-radius translation acts on the torsion term with weight `-6`. -/
theorem spinTorsionRadionTerm_logDiagonalShift (C family x y shift : ℝ) :
    spinTorsionRadionTerm C family (Real.exp (x + shift)) (Real.exp (y + shift)) =
      Real.exp (-6 * shift) *
        spinTorsionRadionTerm C family (Real.exp x) (Real.exp y) := by
  unfold spinTorsionRadionTerm compactificationVolumeShape
  simp only [Real.exp_add, mul_pow]
  rw [show -6 * shift = -(6 * shift) by ring, Real.exp_neg]
  rw [show Real.exp (6 * shift) = Real.exp shift ^ 6 by
    simpa using Real.exp_nat_mul shift 6]
  field_simp [Real.exp_ne_zero]

/-- Dimensionless finite-density correction from the two radial Wightman blocks. -/
def finiteDensityCorrectionShape (x : ℝ) : ℝ :=
  ((Real.sin x - x * Real.cos x) ^ 2 -
    (2 - 2 * Real.cos x - x * Real.sin x) ^ 2) / 4

/-- Density correction vanishes at zero occupation scale. -/
theorem finiteDensityCorrectionShape_zero : finiteDensityCorrectionShape 0 = 0 := by
  simp [finiteDensityCorrectionShape]

/-- The density correction is insensitive to simultaneous orientation reversal. -/
theorem finiteDensityCorrectionShape_even (x : ℝ) :
    finiteDensityCorrectionShape (-x) = finiteDensityCorrectionShape x := by
  simp only [finiteDensityCorrectionShape, Real.sin_neg, Real.cos_neg]
  ring

/-- Finite-density correction as a function of chemical potential and separation. -/
def finiteDensityCorrectionRatio (mu separation : ℝ) : ℝ :=
  finiteDensityCorrectionShape (mu * separation)

/-- Reciprocal rescaling of chemical potential and separation preserves the correction. -/
theorem finiteDensityCorrectionRatio_reciprocalScale (mu separation shift : ℝ) :
    finiteDensityCorrectionRatio (mu * Real.exp shift)
        (separation * Real.exp (-shift)) =
      finiteDensityCorrectionRatio mu separation := by
  unfold finiteDensityCorrectionRatio
  congr 1
  rw [Real.exp_neg]
  field_simp [Real.exp_ne_zero]

/-- Zero chemical potential gives zero correction at every separation. -/
theorem finiteDensityCorrectionRatio_zero_mu (separation : ℝ) :
    finiteDensityCorrectionRatio 0 separation = 0 := by
  simp [finiteDensityCorrectionRatio, finiteDensityCorrectionShape]

end GaloisForLFunctions.HTGeometry
