import GaloisForLFunctions.RHTower.XiShiftedChristoffelSourceWallTraceRenormalizationNoGo
import GaloisForLFunctions.RHTower.XiShiftedCanonicalAdmissionTerminalCurvatureRecession

/-!
# Arcsine-vacuum renormalization of the adaptive shifted-Xi source

The one-coordinate Gaussian defect is not the full deterministic background.  On the exact
shifted-arcsine positive tower, the adaptive Gaussian-visible bulk contributes a second linearly
growing account.  Invisible next-edge and visible Gauss accounts sum to `n+3/8`, the exact
coordinate-dilation-invariant source vacuum.

Subtracting this full vacuum defines a signed, admission-sensitive arithmetic deviation.  It
vanishes on every coordinate-dilated arcsine model, tends to zero at every fixed shifted-Xi degree,
and leaves all strict-frontier contact residues unchanged.
-/

open Filter Matrix Polynomial Set Topology

namespace RHTower

noncomputable section

namespace XiShiftedCanonicalAdmission

/-- Full current-Christoffel source vacuum selected by the shifted-arcsine admission. -/
def arcsineVacuumSourceCounterterm (n : ℕ) : ℝ :=
  (n : ℝ) + 3 / 8

/-- Gaussian-visible part of the arcsine vacuum after the sole invisible edge is removed. -/
def arcsineVisibleGaussVacuumCounterterm (n : ℕ) : ℝ :=
  (15 * (n : ℝ) + 5) / 16

/-- Exact two-account vacuum split: invisible newborn edge plus visible adaptive Gauss bulk. -/
theorem arcsineVacuumSourceCounterterm_eq_dimensionTax_add_visibleGauss
    (n : ℕ) :
    arcsineVacuumSourceCounterterm n =
      xiShiftedChristoffelSourceWallDimensionTax n +
        arcsineVisibleGaussVacuumCounterterm n := by
  unfold arcsineVacuumSourceCounterterm arcsineVisibleGaussVacuumCounterterm
    xiShiftedChristoffelSourceWallDimensionTax
  ring

/-- Exact adaptive Jacobi energy of the shifted-arcsine positive moment tower. -/
theorem adaptiveOrthoJacobiEnergy_normalizedCentralBinom_eq_arcsineVacuum
    {n : ℕ} (hn : 0 < n) :
    HTGeometry.adaptiveOrthoJacobiEnergy
        GaloisForLFunctions.HTGeometry.normalizedCentralBinom n =
      arcsineVacuumSourceCounterterm n := by
  let s := GaloisForLFunctions.HTGeometry.normalizedCentralBinom
  have hsource :=
    HTGeometry.momentFunctional_adaptiveOrthoSourcePolynomial_eq_jacobiEnergy
      GaloisForLFunctions.HTGeometry.normalizedCentralBinom_positiveMomentForm hn
  have hvac :=
    XiShiftedArcsineAdmission.momentFunctional_adaptiveShear_amplitude_eq_norm_mul_linear
      (Nat.ne_of_gt hn)
  have hamp := monicOrtho_normalizedCentralBinom_eq_arc_amplitude n
  change HTGeometry.monicOrtho s n =
    XiShiftedArcsineAdmission.amplitude n at hamp
  have hpoly :
      xiShiftedBoundaryAdaptiveShearPolynomial (XiShiftedArcsineAdmission.amplitude n) =
        HTGeometry.adaptiveOrthoSourcePolynomial s n := by
    rw [← hamp]
    simp only [xiShiftedBoundaryAdaptiveShearPolynomial,
      xiShiftedBoundaryShiftedEuler, HTGeometry.adaptiveOrthoSourcePolynomial,
      C_1, one_mul]
  have hnormEq :
      HTGeometry.momentFunctional s ((XiShiftedArcsineAdmission.amplitude n) ^ 2) =
        HTGeometry.monicOrthoNormSq s n := by
    rw [← hamp]
    unfold HTGeometry.monicOrthoNormSq
    rw [HTGeometry.momentInner_self]
  have hnorm : 0 < HTGeometry.monicOrthoNormSq s n := by
    dsimp only [s]
    exact HTGeometry.monicOrthoNormSq_pos
      GaloisForLFunctions.HTGeometry.normalizedCentralBinom_positiveMomentForm n
  rw [hpoly, hnormEq, hsource] at hvac
  unfold arcsineVacuumSourceCounterterm
  have hfactor :
      HTGeometry.monicOrthoNormSq s n *
          (HTGeometry.adaptiveOrthoJacobiEnergy s n - ((n : ℝ) + 3 / 8)) = 0 := by
    nlinarith
  have hzero := (mul_eq_zero.mp hfactor).resolve_left (ne_of_gt hnorm)
  linarith

/-- Exact scale-completed adaptive Gaussian bulk on the shifted-arcsine tower.  The supposedly
renormalized positive wall still grows linearly with degree. -/
theorem arcsineScaleCompletedAdaptiveGaussBulk_eq_visibleVacuum
    {n : ℕ} (hn : 0 < n) :
    HTGeometry.adaptiveOrthoGaussAggregate
          GaloisForLFunctions.HTGeometry.normalizedCentralBinom n /
        (16 * HTGeometry.monicOrthoNormSq
            GaloisForLFunctions.HTGeometry.normalizedCentralBinom n *
          HTGeometry.monicOrthoBeta
            GaloisForLFunctions.HTGeometry.normalizedCentralBinom (n + 1)) =
      arcsineVisibleGaussVacuumCounterterm n := by
  let s := GaloisForLFunctions.HTGeometry.normalizedCentralBinom
  have hpos :=
    GaloisForLFunctions.HTGeometry.normalizedCentralBinom_positiveMomentForm
  let hbelow : HTGeometry.PositiveMomentFormBelow s (n + 2) :=
    ⟨fun p hp _ => hpos.pos_of_ne_zero p hp⟩
  have haggregate := HTGeometry.adaptiveOrthoGaussAggregate_eq_visibleJacobiEnergy
    hbelow hn (le_refl (n + 2))
  have henergy := adaptiveOrthoJacobiEnergy_normalizedCentralBinom_eq_arcsineVacuum hn
  have hbeta := monicOrthoBeta_normalizedCentralBinom_of_two_le
    (show 2 ≤ n + 1 by omega)
  have hnorm : 0 < HTGeometry.monicOrthoNormSq s n :=
    HTGeometry.monicOrthoNormSq_pos hpos n
  unfold arcsineVisibleGaussVacuumCounterterm arcsineVacuumSourceCounterterm at *
  dsimp only [s] at haggregate hnorm ⊢
  rw [haggregate, henergy, hbeta]
  field_simp [ne_of_gt hnorm]
  ring

/-- Actual signed arithmetic deviation after subtracting the full arcsine source vacuum. -/
def arcsineCenteredScaleCompletedRelativeArithmeticSource (w : ℝ) (n : ℕ) : ℝ :=
  scaleCompletedRelativeArithmeticSource w n - arcsineVacuumSourceCounterterm n

/-- Fixed-degree shifted-Xi recession is exactly zero after full vacuum subtraction. -/
theorem tendsto_arcsineCenteredScaleCompletedRelativeArithmeticSource
    {n : ℕ} (hn : n ≠ 0) :
    Tendsto (fun w : ℝ =>
      arcsineCenteredScaleCompletedRelativeArithmeticSource w n)
      atTop (nhds 0) := by
  have h := tendsto_scaleCompletedRelativeArithmeticSource hn
  simpa [arcsineCenteredScaleCompletedRelativeArithmeticSource,
    arcsineVacuumSourceCounterterm] using h.sub_const ((n : ℝ) + 3 / 8)

/-- Every nonzero coordinate dilation of the positive arcsine tower has identically zero centered
source after current Christoffel completion. -/
theorem coordinateDilated_arcsineCenteredScaleCompletedSource_eq_zero
    {r : ℝ} (hr : r ≠ 0) {n : ℕ} (hn : n ≠ 0) :
    (HTGeometry.momentFunctional
          (XiShiftedArcsineAdmission.coordinateDilatedMoment r)
          (xiShiftedBoundaryAdaptiveShearPolynomial
            (XiShiftedArcsineAdmission.coordinateDilatedAmplitude r n)) /
        HTGeometry.momentFunctional
          (XiShiftedArcsineAdmission.coordinateDilatedMoment r)
          ((XiShiftedArcsineAdmission.coordinateDilatedAmplitude r n) ^ 2)) /
        XiShiftedArcsineAdmission.coordinateDilatedAdmissionChristoffelScaleSq r n -
      arcsineVacuumSourceCounterterm n = 0 := by
  rw [XiShiftedArcsineAdmission.coordinateDilated_scaleCompletedSource_eq hr hn]
  simp [arcsineVacuumSourceCounterterm]

end XiShiftedCanonicalAdmission

/-- Full arcsine-vacuum-centered actual Christoffel source wall. -/
def xiShiftedCanonicalAdmissionArcsineCenteredChristoffelSourceWall
    (y : ℝ) (n : ℕ) : ℝ :=
  xiShiftedCanonicalAdmissionChristoffelSourceWall y n -
    XiShiftedCanonicalAdmission.arcsineVacuumSourceCounterterm n

/-- Full centering equals minimal observer-defect renormalization minus visible Gaussian vacuum. -/
theorem xiShiftedCanonicalAdmissionArcsineCenteredChristoffelSourceWall_eq
    (y : ℝ) (n : ℕ) :
    xiShiftedCanonicalAdmissionArcsineCenteredChristoffelSourceWall y n =
      xiShiftedCanonicalAdmissionRenormalizedChristoffelSourceWall y n -
        XiShiftedCanonicalAdmission.arcsineVisibleGaussVacuumCounterterm n := by
  rw [xiShiftedCanonicalAdmissionArcsineCenteredChristoffelSourceWall,
    xiShiftedCanonicalAdmissionRenormalizedChristoffelSourceWall,
    XiShiftedCanonicalAdmission.arcsineVacuumSourceCounterterm_eq_dimensionTax_add_visibleGauss]
  ring

/-- Intrinsic contact scaling of the full arcsine-vacuum-centered source wall. -/
def xiShiftedStrictFrontierAllContactScaledArcsineCenteredSourceWall
    (n d : ℕ) (u : ℝ) : ℝ :=
  u ^ d * xiShiftedCanonicalAdmissionArcsineCenteredChristoffelSourceWall
    (xiShiftedHigherBlockTerminalFrontier (n + 1) + u) (n + 1)

/-- **Vacuum subtraction preserves arithmetic contact.**  Every exact finite positive
strict-frontier residue survives full arcsine centering unchanged. -/
theorem tendsto_xiShiftedStrictFrontierAllContactScaledArcsineCenteredSourceWall
    {n d : ℕ} (hne : (xiShiftedHigherBlockFailureSet n).Nonempty)
    (hstrict : xiShiftedHigherBlockTerminalFrontier n <
      xiShiftedHigherBlockTerminalFrontier (n + 1))
    (hd : 0 < d)
    (hzero : ∀ k < 2 * (n + 2) + d,
      xiShiftedStrictFrontierPadeDefect n k = 0)
    (hsigned : 0 < (-1 : ℝ) ^ d *
      xiShiftedStrictFrontierPadeDefect n (2 * (n + 2) + d)) :
    Tendsto (xiShiftedStrictFrontierAllContactScaledArcsineCenteredSourceWall n d)
      (𝓝[>] (0 : ℝ))
      (𝓝 (xiShiftedStrictFrontierAllContactSourceWallResidue n d)) := by
  have hwall := tendsto_xiShiftedStrictFrontierAllContactScaledSourceWall
    hne hstrict hd hzero hsigned
  have hcounterFull : Tendsto
      (fun u : ℝ => u ^ d *
        XiShiftedCanonicalAdmission.arcsineVacuumSourceCounterterm (n + 1))
      (𝓝 (0 : ℝ)) (𝓝 0) := by
    have hp : Tendsto (fun u : ℝ => u ^ d) (𝓝 (0 : ℝ)) (𝓝 0) := by
      have hid : Tendsto (fun u : ℝ => u) (𝓝 (0 : ℝ)) (𝓝 0) := tendsto_id
      simpa [Nat.ne_of_gt hd] using hid.pow d
    simpa using hp.mul_const
      (XiShiftedCanonicalAdmission.arcsineVacuumSourceCounterterm (n + 1))
  have hcounter : Tendsto
      (fun u : ℝ => u ^ d *
        XiShiftedCanonicalAdmission.arcsineVacuumSourceCounterterm (n + 1))
      (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    hcounterFull.mono_left nhdsWithin_le_nhds
  have hsub : Tendsto
      (fun u : ℝ =>
        xiShiftedStrictFrontierAllContactScaledSourceWall n d u -
          u ^ d * XiShiftedCanonicalAdmission.arcsineVacuumSourceCounterterm (n + 1))
      (𝓝[>] (0 : ℝ))
      (𝓝 (xiShiftedStrictFrontierAllContactSourceWallResidue n d)) := by
    simpa using hwall.sub hcounter
  exact hsub.congr' (Filter.Eventually.of_forall fun u => by
    unfold xiShiftedStrictFrontierAllContactScaledArcsineCenteredSourceWall
      xiShiftedStrictFrontierAllContactScaledSourceWall
      xiShiftedCanonicalAdmissionArcsineCenteredChristoffelSourceWall
    ring)

end

end RHTower
