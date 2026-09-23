import GaloisForLFunctions.RHTower.XiSourceBoundaryOrientationConservation
import GaloisForLFunctions.RHTower.CCMUniversalWeilSourceReconstruction

/-!
# Singular continued-source realization of Xi source entropy

The imaginary reciprocal-square divisor coordinate is the signed square root of the local
source-entropy orientation density.  It therefore defines a canonical square-summable vector on
the multiplicity-exact Xi divisor.  Critical-line reflection negates this vector, its Hilbert norm
is the global reflected source-entropy energy, and its unconditional Weil square is the negative
of that energy.

The universal continued prime--Gamma reconstruction theorem then supplies explicit finite,
pairwise-separated source packets converging to this vector, with exact source energies converging
to the negative conserved source-entropy energy.  This realizes the singular-completion arm of the
source--boundary law.  The packet sequence is still selected through target-side Hilbert closure;
no source-only sign theorem or RH is asserted.
-/

open Complex Filter Topology
open scoped BigOperators

namespace RHTower

noncomputable section

/-- The signed reciprocal-square orientation test on the centered spectral plane. -/
def xiSourceEntropyOrientationTest (z : ℂ) : ℂ :=
  (((z⁻¹ ^ (2 : ℕ)).im : ℝ) : ℂ)

/-- The source-entropy orientation test is square-summable on the complete Xi divisor. -/
theorem xiSourceEntropyOrientationTest_squareSummable :
    XiWeilSquareSummable xiSourceEntropyOrientationTest := by
  unfold XiWeilSquareSummable
  exact summable_xiThermalOrientationTerm.congr (fun q => by
    change (xiZeroCopyReciprocalSquare q).im ^ (2 : ℕ) =
      ‖(((xiZeroCopyReciprocalSquare q).im : ℝ) : ℂ)‖ ^ (2 : ℕ)
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs])

/-- The canonical signed source-entropy orientation vector. -/
def xiSourceEntropyOrientationVector :
    lp (fun _ : XiZeroCopy => ℂ) 2 :=
  xiWeilEvaluationLp xiSourceEntropyOrientationTest
    xiSourceEntropyOrientationTest_squareSummable

@[simp] theorem xiSourceEntropyOrientationVector_apply (q : XiZeroCopy) :
    xiSourceEntropyOrientationVector q =
      (((xiZeroCopyReciprocalSquare q).im : ℝ) : ℂ) := by
  rfl

/-- The local signed vector coordinate is the source entropy times the invariant vertical
amplitude.  Squaring this identity gives the previously established local density law. -/
theorem xiSourceEntropyOrientationVector_apply_eq_sourceEntropyAmplitude
    (q : XiZeroCopy) :
    xiSourceEntropyOrientationVector q =
      ((-riemannReflectedSourceEntropy (q.1 : ℂ) *
          (q.1 : ℂ).im /
        (((q.1 : ℂ).re - 1 / 2) ^ (2 : ℕ) +
          (q.1 : ℂ).im ^ (2 : ℕ)) ^ (2 : ℕ) : ℝ) : ℂ) := by
  rw [xiSourceEntropyOrientationVector_apply]
  congr 1
  have hentropy :
      riemannReflectedSourceEntropy (q.1 : ℂ) =
        -2 * ((q.1 : ℂ).re - 1 / 2) := by
    rw [riemannReflectedSourceEntropy_eq_neg_sourceCayleyRate]
    simp only [GaloisForLFunctions.HTGeometry.sourceCayleyTransverseRate,
      sub_re, one_re]
    ring
  rw [xiZeroCopyReciprocalSquare_im_formula, hentropy]
  ring

/-- The squared Hilbert norm of the signed orientation vector is exactly the global conserved
source-entropy energy. -/
theorem norm_sq_xiSourceEntropyOrientationVector :
    ‖xiSourceEntropyOrientationVector‖ ^ (2 : ℕ) =
      xiSourceEntropyOrientationEnergy := by
  rw [HilbertSchmidt.lp_norm_sq_eq,
    xiSourceEntropyOrientationEnergy_eq_thermalOrientationEnergy,
    xiThermalOrientationEnergy]
  apply tsum_congr
  intro q
  simp [xiSourceEntropyOrientationVector_apply, Complex.norm_real,
    Real.norm_eq_abs, sq_abs]

/-- Critical-line reflection negates the signed source-entropy coordinate. -/
theorem xiSourceEntropyOrientationCoordinate_lineConj (q : XiZeroCopy) :
    xiSourceEntropyOrientationVector (xiZeroCopyLineConjEquiv q) =
      -xiSourceEntropyOrientationVector q := by
  simp [xiSourceEntropyOrientationVector_apply,
    xiZeroCopyReciprocalSquare, xiSpectralPoint_lineConj,
    ← map_inv₀, ← map_pow]

/-- The conserved source-entropy vector is an exact `(-1)`-eigenvector of unconditional Xi
critical-line reflection. -/
theorem xiWeilLineConjLp_xiSourceEntropyOrientationVector :
    xiWeilLineConjLp xiSourceEntropyOrientationVector =
      -xiSourceEntropyOrientationVector := by
  apply Subtype.ext
  funext q
  rw [xiWeilLineConjLp_apply]
  exact xiSourceEntropyOrientationCoordinate_lineConj q

/-- The unconditional Xi--Weil square of the source-entropy vector is exactly the negative
conserved source-entropy energy. -/
theorem xiWeilHilbertQuadratic_xiSourceEntropyOrientationVector :
    xiWeilHilbertQuadratic xiSourceEntropyOrientationVector =
      -xiSourceEntropyOrientationEnergy := by
  rw [xiWeilHilbertQuadratic, xiWeilLineConjLinearIsometry_apply,
    xiWeilLineConjLp_xiSourceEntropyOrientationVector, inner_neg_left,
    neg_re]
  congr 1
  exact (inner_self_eq_norm_sq (𝕜 := ℂ)
    xiSourceEntropyOrientationVector).trans
      norm_sq_xiSourceEntropyOrientationVector

/-- The diagonal Weil value of the source-entropy orientation test is the negative conserved
source-entropy energy. -/
theorem xiWeilPolarization_sourceEntropyOrientationTest :
    (xiWeilPolarization xiSourceEntropyOrientationTest
      xiSourceEntropyOrientationTest).re =
        -xiSourceEntropyOrientationEnergy := by
  rw [← xiWeilHilbertQuadratic_evaluation_eq_polarization_re
      xiSourceEntropyOrientationTest
      xiSourceEntropyOrientationTest_squareSummable]
  exact xiWeilHilbertQuadratic_xiSourceEntropyOrientationVector

/-- **Singular source realization of conserved orientation.**  Explicit finite,
pairwise-separated continued prime--Gamma packets converge to the canonical source-entropy
orientation vector, while their exact source energies converge to the negative global conserved
source-entropy energy. -/
theorem xiSourceEntropyOrientationEnergy_separatedContinuedSource_reconstruction :
    ∃ P : ℕ → XiSeparatedContinuedCauchyPacket,
      Tendsto (fun n => (P n).evaluation) atTop
        (nhds xiSourceEntropyOrientationVector) ∧
      Tendsto (fun n => (P n).sourceEnergy) atTop
        (nhds (-xiSourceEntropyOrientationEnergy)) := by
  simpa only [xiSourceEntropyOrientationVector,
    xiWeilPolarization_sourceEntropyOrientationTest] using
    xiWeilPolarization_separatedContinuedSource_reconstruction
      xiSourceEntropyOrientationTest
      xiSourceEntropyOrientationTest_squareSummable

/-- The source-entropy packet energies have a strictly negative limit exactly when RH fails. -/
theorem sourceEntropySeparatedPacketLimit_neg_iff_not_riemannHypothesis :
    -xiSourceEntropyOrientationEnergy < 0 ↔ ¬RiemannHypothesis := by
  rw [neg_lt_zero,
    xiSourceEntropyOrientationEnergy_eq_thermalOrientationEnergy]
  constructor
  · intro hpos hRH
    rw [xiThermalOrientationEnergy_eq_zero_iff_rh.mpr hRH] at hpos
    exact lt_irrefl 0 hpos
  · intro hnot
    exact lt_of_le_of_ne xiThermalOrientationEnergy_nonneg
      (fun hzero =>
        hnot (xiThermalOrientationEnergy_eq_zero_iff_rh.mp hzero.symm))

end

end RHTower
