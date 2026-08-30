import GaloisForLFunctions.RHTower.HedenmalmCriticalFeatureTranslatedPhaseSourceSelection

/-!
# One-cell averaging for translated HCF lattices

Translation averaging removes every nonzero Fourier alias before any divisor scalarization.  The
complete HCF periodization has exact mean `2π` over one translation cell.  Consequently every
finite translated lattice has cell average at most `2π`, with no Fourier-envelope loss.
-/

open Complex Filter Topology Set MeasureTheory
open GaloisForLFunctions.HTGeometry
open scoped BigOperators

namespace RHTower

noncomputable section

/-- The complete HCF boundary periodization has exact zero-mode mean over one translation cell. -/
theorem integral_Ioc_criticalFeatureRealBoundaryPeriodization_add_sub_two_pi_eq_zero
    (x : ℝ) :
    (∫ theta in Ioc (0 : ℝ) 1,
      (criticalFeatureRealBoundaryPeriodization (x + theta) - 2 * Real.pi)) = 0 := by
  let mu : Measure ℝ := Measure.dirac x
  let g : ℝ → ℝ := fun _ => 1
  have hg : Integrable g mu := by
    exact integrable_const 1
  have hpoint (theta : ℝ) :
      criticalFeatureRealBoundaryPeriodization (x + theta) - 2 * Real.pi =
        (criticalFeatureSourceNonzeroFourierAliasAtPhase
          (theta : UnitAddCircle) mu g).re := by
    have h :=
      ofReal_integral_criticalFeatureRealBoundaryPeriodization_add_mul_sub_zeroMode_eq_aliasAtPhase
        theta mu hg
    have hre := congrArg Complex.re h
    simpa [mu, g] using hre
  let F : UnitAddCircle → ℂ := fun theta =>
    criticalFeatureSourceNonzeroFourierAliasAtPhase theta mu g
  have hFcont : Continuous F :=
    continuous_criticalFeatureSourceNonzeroFourierAliasAtPhase mu hg
  have hFint : Integrable F GaloisForLFunctions.unitCircleHaar := by
    rw [← integrableOn_univ]
    exact hFcont.continuousOn.integrableOn_compact isCompact_univ
  have hpre := AddCircle.integral_preimage (1 : ℝ) 0 (fun theta => (F theta).re)
  have hvol : (volume : Measure UnitAddCircle) =
      GaloisForLFunctions.unitCircleHaar := by
    rw [AddCircle.volume_eq_smul_haarAddCircle]
    simp
  rw [hvol] at hpre
  have hmean : (∫ theta : UnitAddCircle, (F theta).re
      ∂GaloisForLFunctions.unitCircleHaar) = 0 := by
    have hre := Complex.reCLM.integral_comp_comm hFint
    change (∫ theta : UnitAddCircle, Complex.reCLM (F theta)
      ∂GaloisForLFunctions.unitCircleHaar) =
        Complex.reCLM (∫ theta : UnitAddCircle, F theta
          ∂GaloisForLFunctions.unitCircleHaar) at hre
    rw [integral_criticalFeatureSourceNonzeroFourierAliasAtPhase_eq_zero mu hg] at hre
    simpa using hre
  calc
    (∫ theta in Ioc (0 : ℝ) 1,
        (criticalFeatureRealBoundaryPeriodization (x + theta) - 2 * Real.pi)) =
        ∫ theta in Ioc (0 : ℝ) 1, (F (theta : UnitAddCircle)).re := by
      apply integral_congr_ae
      filter_upwards with theta
      exact hpoint theta
    _ = ∫ theta : UnitAddCircle, (F theta).re
        ∂GaloisForLFunctions.unitCircleHaar := by
      simpa using hpre
    _ = 0 := hmean

/-- Translation averaging kills every nonzero HCF Fourier mode after pairing against an arbitrary
integrable signed source.  This is the source-level zero-mode identity needed for pole--Gamma
densities; no positivity or divisor representation of `g` is used. -/
theorem integral_Ioc_integral_criticalFeatureRealBoundaryPeriodization_add_mul_sub_zeroMode_eq_zero
    (mu : Measure ℝ) {g : ℝ → ℝ} (hg : Integrable g mu) :
    (∫ theta in Ioc (0 : ℝ) 1,
      ((∫ x, criticalFeatureRealBoundaryPeriodization (x + theta) * g x ∂mu) -
        2 * Real.pi * ∫ x, g x ∂mu)) = 0 := by
  have hpoint (theta : ℝ) :
      (∫ x, criticalFeatureRealBoundaryPeriodization (x + theta) * g x ∂mu) -
          2 * Real.pi * ∫ x, g x ∂mu =
        (criticalFeatureSourceNonzeroFourierAliasAtPhase
          (theta : UnitAddCircle) mu g).re := by
    have h :=
      ofReal_integral_criticalFeatureRealBoundaryPeriodization_add_mul_sub_zeroMode_eq_aliasAtPhase
        theta mu hg
    have hre := congrArg Complex.re h
    simpa using hre
  let F : UnitAddCircle → ℂ := fun theta =>
    criticalFeatureSourceNonzeroFourierAliasAtPhase theta mu g
  have hFcont : Continuous F :=
    continuous_criticalFeatureSourceNonzeroFourierAliasAtPhase mu hg
  have hFint : Integrable F GaloisForLFunctions.unitCircleHaar := by
    rw [← integrableOn_univ]
    exact hFcont.continuousOn.integrableOn_compact isCompact_univ
  have hpre := AddCircle.integral_preimage (1 : ℝ) 0 (fun theta => (F theta).re)
  have hvol : (volume : Measure UnitAddCircle) =
      GaloisForLFunctions.unitCircleHaar := by
    rw [AddCircle.volume_eq_smul_haarAddCircle]
    simp
  rw [hvol] at hpre
  have hmean : (∫ theta : UnitAddCircle, (F theta).re
      ∂GaloisForLFunctions.unitCircleHaar) = 0 := by
    have hre := Complex.reCLM.integral_comp_comm hFint
    change (∫ theta : UnitAddCircle, Complex.reCLM (F theta)
      ∂GaloisForLFunctions.unitCircleHaar) =
        Complex.reCLM (∫ theta : UnitAddCircle, F theta
          ∂GaloisForLFunctions.unitCircleHaar) at hre
    rw [integral_criticalFeatureSourceNonzeroFourierAliasAtPhase_eq_zero mu hg] at hre
    simpa using hre
  calc
    (∫ theta in Ioc (0 : ℝ) 1,
      ((∫ x, criticalFeatureRealBoundaryPeriodization (x + theta) * g x ∂mu) -
        2 * Real.pi * ∫ x, g x ∂mu)) =
        ∫ theta in Ioc (0 : ℝ) 1, (F (theta : UnitAddCircle)).re := by
      apply integral_congr_ae
      filter_upwards with theta
      exact hpoint theta
    _ = ∫ theta : UnitAddCircle, (F theta).re
        ∂GaloisForLFunctions.unitCircleHaar := by
      simpa using hpre
    _ = 0 := hmean

/-- Canonical specialization: averaging the translated full-lattice pole--Gamma observable gives
exactly its zero-frequency source observable. -/
theorem integral_Ioc_criticalFeatureCanonicalCoreFullPoleGammaObservableAtPhase_sub_zeroMode_eq_zero
    (n : ℕ) :
    (∫ theta in Ioc (0 : ℝ) 1,
      (criticalFeatureCanonicalCoreFullPoleGammaObservableAtPhase n
          (criticalFeatureCanonicalRegularLatticeSummedDisplacementData n).displacement theta -
        criticalFeatureCanonicalCorePoleGammaZeroMode n
          (criticalFeatureCanonicalRegularLatticeSummedDisplacementData n).displacement)) = 0 := by
  have h :=
    integral_Ioc_integral_criticalFeatureRealBoundaryPeriodization_add_mul_sub_zeroMode_eq_zero
      (volume.restrict (criticalFeatureCanonicalCore n))
      (integrableOn_criticalFeatureCanonicalRegularPoleGammaDensity n)
  simpa only [criticalFeatureCanonicalCoreFullPoleGammaObservableAtPhase,
    criticalFeatureCanonicalCorePoleGammaZeroMode,
    criticalFeaturePoleGammaZeroModeObservable,
    criticalFeatureCanonicalCore] using h

/-- For fixed observation height, a finite translated HCF lattice varies continuously in phase. -/
theorem continuous_criticalFeatureTranslatedFiniteRealBoundaryLatticeWeight_phase
    (K : Finset ℤ) (x : ℝ) :
    Continuous (fun theta : ℝ =>
      criticalFeatureTranslatedFiniteRealBoundaryLatticeWeight theta K x) := by
  rw [show (fun theta : ℝ =>
      criticalFeatureTranslatedFiniteRealBoundaryLatticeWeight theta K x) =
      fun theta => criticalFeatureFiniteRealBoundaryLatticeWeight K (x + theta) by
    funext theta
    exact criticalFeatureTranslatedFiniteRealBoundaryLatticeWeight_eq_add theta K x]
  exact (continuous_criticalFeatureFiniteRealBoundaryLatticeWeight K).comp
    (continuous_const.add continuous_id)

/-- Averaging any finite translated HCF lattice over one phase cell costs at most its exact zero
mode `2π`.  No nonzero Fourier envelope survives this averaging. -/
theorem integral_Ioc_criticalFeatureTranslatedFiniteRealBoundaryLatticeWeight_le_two_pi
    (K : Finset ℤ) (x : ℝ) :
    (∫ theta in Ioc (0 : ℝ) 1,
      criticalFeatureTranslatedFiniteRealBoundaryLatticeWeight theta K x) ≤
      2 * Real.pi := by
  let f : ℝ → ℝ := fun theta =>
    criticalFeatureTranslatedFiniteRealBoundaryLatticeWeight theta K x
  let p : ℝ → ℝ := fun theta =>
    criticalFeatureRealBoundaryPeriodization (x + theta)
  have hfcont : Continuous f :=
    continuous_criticalFeatureTranslatedFiniteRealBoundaryLatticeWeight_phase K x
  have hpcont : Continuous p :=
    continuous_criticalFeatureRealBoundaryPeriodization.comp
      (continuous_const.add continuous_id)
  have hf : IntegrableOn f (Ioc (0 : ℝ) 1) :=
    (hfcont.integrableOn_Icc : IntegrableOn f (Icc (0 : ℝ) 1)).mono_set Ioc_subset_Icc_self
  have hp : IntegrableOn p (Ioc (0 : ℝ) 1) :=
    (hpcont.integrableOn_Icc : IntegrableOn p (Icc (0 : ℝ) 1)).mono_set Ioc_subset_Icc_self
  have hc : IntegrableOn (fun _ : ℝ => 2 * Real.pi) (Ioc (0 : ℝ) 1) :=
    integrableOn_const (by simp)
  have hmono :
      (∫ theta in Ioc (0 : ℝ) 1, (f theta - 2 * Real.pi)) ≤
        ∫ theta in Ioc (0 : ℝ) 1, (p theta - 2 * Real.pi) := by
    apply integral_mono (hf.sub hc) (hp.sub hc)
    intro theta
    exact sub_le_sub_right
      (criticalFeatureTranslatedFiniteRealBoundaryLatticeWeight_le_periodization theta K x)
      (2 * Real.pi)
  rw [integral_Ioc_criticalFeatureRealBoundaryPeriodization_add_sub_two_pi_eq_zero x] at hmono
  change (∫ theta in Ioc (0 : ℝ) 1, (f theta - 2 * Real.pi)) ≤ 0 at hmono
  rw [integral_sub hf hc] at hmono
  simpa [f] using hmono

/-- The averaged finite canonical observable has no hidden Fourier loss: after restoring exactly
the source contribution of the omitted lattice centers, only the zero mode remains.  This identity
is formed before any divisor scalarization. -/
theorem integral_Ioc_criticalFeatureCanonicalCoreTranslatedFinite_sub_zeroMode_add_omitted_eq_zero
    (n : ℕ) :
    (∫ theta in Ioc (0 : ℝ) 1,
      ((criticalFeatureCanonicalCoreTranslatedFinitePoleGammaObservable n
          (criticalFeatureCanonicalRegularLatticeSummedDisplacementData n).displacement theta -
        criticalFeatureCanonicalCorePoleGammaZeroMode n
          (criticalFeatureCanonicalRegularLatticeSummedDisplacementData n).displacement) +
        criticalFeatureCanonicalTranslatedInteriorOmittedAlias n
          (criticalFeatureCanonicalRegularLatticeSummedDisplacementData n).displacement theta)) =
      0 := by
  calc
    (∫ theta in Ioc (0 : ℝ) 1,
      ((criticalFeatureCanonicalCoreTranslatedFinitePoleGammaObservable n
          (criticalFeatureCanonicalRegularLatticeSummedDisplacementData n).displacement theta -
        criticalFeatureCanonicalCorePoleGammaZeroMode n
          (criticalFeatureCanonicalRegularLatticeSummedDisplacementData n).displacement) +
        criticalFeatureCanonicalTranslatedInteriorOmittedAlias n
          (criticalFeatureCanonicalRegularLatticeSummedDisplacementData n).displacement theta)) =
        ∫ theta in Ioc (0 : ℝ) 1,
          (criticalFeatureCanonicalCoreFullPoleGammaObservableAtPhase n
              (criticalFeatureCanonicalRegularLatticeSummedDisplacementData n).displacement theta -
            criticalFeatureCanonicalCorePoleGammaZeroMode n
              (criticalFeatureCanonicalRegularLatticeSummedDisplacementData n).displacement) := by
      apply integral_congr_ae
      filter_upwards with theta
      rw [criticalFeatureCanonicalTranslatedInteriorOmittedAlias]
      ring
    _ = 0 :=
      integral_Ioc_criticalFeatureCanonicalCoreFullPoleGammaObservableAtPhase_sub_zeroMode_eq_zero n

end

end RHTower
