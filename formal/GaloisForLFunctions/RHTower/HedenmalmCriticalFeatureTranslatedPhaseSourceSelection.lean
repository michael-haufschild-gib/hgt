import GaloisForLFunctions.RHTower.HedenmalmCriticalFeatureCanonicalPhaseSourceDecomposition

/-!
# Source-selected translation for the HCF lattice

Haar averaging of the exact source Fourier alias gives more than an averaged estimate: at every
canonical height there is a real translation for which the full-periodization pole--Gamma
observable is at least its zero mode.  This is the sign required by the Plemelj covariance, where
the physical core observable is subtracted.

The finite lattice below has centers `k - theta`.  Its complete integer sum is exactly the HCF
periodization evaluated at `x + theta`; this fixes the phase convention before any receiver is
attached.  At the selected phase, the nonzero Fourier alias disappears from the one-sided core
budget.  Only the literal omitted-center source term remains.
-/

open Complex Filter Topology Set MeasureTheory
open GaloisForLFunctions.HTGeometry
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Finite HCF lattice with source phase `theta`; its geometric centers are `k - theta`. -/
def criticalFeatureTranslatedFiniteRealBoundaryLatticeWeight
    (theta : ℝ) (K : Finset ℤ) (x : ℝ) : ℝ :=
  ∑ k ∈ K, criticalFeatureRealBoundaryWeight ((k : ℝ) - theta) x

theorem criticalFeatureTranslatedFiniteRealBoundaryLatticeWeight_eq_add
    (theta : ℝ) (K : Finset ℤ) (x : ℝ) :
    criticalFeatureTranslatedFiniteRealBoundaryLatticeWeight theta K x =
      criticalFeatureFiniteRealBoundaryLatticeWeight K (x + theta) := by
  unfold criticalFeatureTranslatedFiniteRealBoundaryLatticeWeight
    criticalFeatureFiniteRealBoundaryLatticeWeight
  apply Finset.sum_congr rfl
  intro k hk
  unfold criticalFeatureRealBoundaryWeight
  congr 2
  ring

theorem continuous_criticalFeatureTranslatedFiniteRealBoundaryLatticeWeight
    (theta : ℝ) (K : Finset ℤ) :
    Continuous (criticalFeatureTranslatedFiniteRealBoundaryLatticeWeight theta K) := by
  rw [show criticalFeatureTranslatedFiniteRealBoundaryLatticeWeight theta K =
      fun x => criticalFeatureFiniteRealBoundaryLatticeWeight K (x + theta) by
    funext x
    exact criticalFeatureTranslatedFiniteRealBoundaryLatticeWeight_eq_add theta K x]
  exact (continuous_criticalFeatureFiniteRealBoundaryLatticeWeight K).comp
    (continuous_id.add continuous_const)

theorem criticalFeatureTranslatedFiniteRealBoundaryLatticeWeight_nonnegative
    (theta : ℝ) (K : Finset ℤ) (x : ℝ) :
    0 ≤ criticalFeatureTranslatedFiniteRealBoundaryLatticeWeight theta K x := by
  rw [criticalFeatureTranslatedFiniteRealBoundaryLatticeWeight_eq_add]
  exact criticalFeatureFiniteRealBoundaryLatticeWeight_nonnegative K (x + theta)

theorem criticalFeatureTranslatedFiniteRealBoundaryLatticeWeight_le_nine
    (theta : ℝ) (K : Finset ℤ) (x : ℝ) :
    criticalFeatureTranslatedFiniteRealBoundaryLatticeWeight theta K x ≤ 9 := by
  rw [criticalFeatureTranslatedFiniteRealBoundaryLatticeWeight_eq_add]
  exact criticalFeatureFiniteRealBoundaryLatticeWeight_le_nine K (x + theta)

theorem summable_criticalFeatureRealBoundaryWeight_translatedCenters
    (theta x : ℝ) :
    Summable (fun k : ℤ =>
      criticalFeatureRealBoundaryWeight ((k : ℝ) - theta) x) := by
  refine (summable_criticalFeatureRealBoundaryWeight_integerCenters (x + theta)).congr ?_
  intro k
  unfold criticalFeatureRealBoundaryWeight
  congr 2
  ring

/-- Exact phase convention: centers `k - theta` generate `periodization (x + theta)`. -/
theorem tsum_criticalFeatureRealBoundaryWeight_translatedCenters
    (theta x : ℝ) :
    (∑' k : ℤ, criticalFeatureRealBoundaryWeight ((k : ℝ) - theta) x) =
      criticalFeatureRealBoundaryPeriodization (x + theta) := by
  calc
    (∑' k : ℤ, criticalFeatureRealBoundaryWeight ((k : ℝ) - theta) x) =
        ∑' k : ℤ, criticalFeatureRealBoundaryWeight (k : ℝ) (x + theta) := by
      apply tsum_congr
      intro k
      unfold criticalFeatureRealBoundaryWeight
      congr 2
      ring
    _ = criticalFeatureRealBoundaryPeriodization (x + theta) :=
      tsum_criticalFeatureRealBoundaryWeight_integerCenters (x + theta)

theorem criticalFeatureTranslatedFiniteRealBoundaryLatticeWeight_le_periodization
    (theta : ℝ) (K : Finset ℤ) (x : ℝ) :
    criticalFeatureTranslatedFiniteRealBoundaryLatticeWeight theta K x ≤
      criticalFeatureRealBoundaryPeriodization (x + theta) := by
  rw [← tsum_criticalFeatureRealBoundaryWeight_translatedCenters theta x]
  exact (summable_criticalFeatureRealBoundaryWeight_translatedCenters theta x).sum_le_tsum K
    (fun k _hk => by
      unfold criticalFeatureRealBoundaryWeight
      positivity)

/-- Full-periodization pole--Gamma observable on the canonical core at source phase `theta`. -/
def criticalFeatureCanonicalCoreFullPoleGammaObservableAtPhase
    (n : ℕ) (eta theta : ℝ) : ℝ :=
  ∫ x in criticalFeatureCanonicalCore n,
    criticalFeatureRealBoundaryPeriodization (x + theta) *
      criticalFeaturePositiveShiftPoleGammaDensity eta x

/-- Exact canonical nonzero Fourier alias at source phase `theta`. -/
def criticalFeatureCanonicalRegularNonzeroFourierAliasAtPhase
    (n : ℕ) (theta : ℝ) : ℂ :=
  criticalFeatureSourceNonzeroFourierAliasAtPhase
    (theta : UnitAddCircle)
    (volume.restrict (criticalFeatureCanonicalCore n))
    (criticalFeaturePositiveShiftPoleGammaDensity
      (criticalFeatureCanonicalRegularLatticeSummedDisplacementData n).displacement)

/-- Translated canonical full-periodization error equals the phase-twisted source alias exactly. -/
theorem ofReal_criticalFeatureCanonicalCoreFullPoleGammaObservableAtPhase_sub_zeroMode_eq_alias
    (n : ℕ) (theta : ℝ) :
    ((criticalFeatureCanonicalCoreFullPoleGammaObservableAtPhase n
        (criticalFeatureCanonicalRegularLatticeSummedDisplacementData n).displacement theta -
      criticalFeatureCanonicalCorePoleGammaZeroMode n
        (criticalFeatureCanonicalRegularLatticeSummedDisplacementData n).displacement : ℝ) : ℂ) =
      criticalFeatureCanonicalRegularNonzeroFourierAliasAtPhase n theta := by
  have h :=
    ofReal_integral_criticalFeatureRealBoundaryPeriodization_add_mul_sub_zeroMode_eq_aliasAtPhase
      theta (volume.restrict (criticalFeatureCanonicalCore n))
      (integrableOn_criticalFeatureCanonicalRegularPoleGammaDensity n)
  rw [criticalFeatureCanonicalCoreFullPoleGammaObservableAtPhase,
    criticalFeatureCanonicalCorePoleGammaZeroMode,
    criticalFeaturePoleGammaZeroModeObservable]
  change
    (((∫ x in criticalFeatureCanonicalCore n,
        criticalFeatureRealBoundaryPeriodization (x + theta) *
          criticalFeaturePositiveShiftPoleGammaDensity
            (criticalFeatureCanonicalRegularLatticeSummedDisplacementData n).displacement x) -
      2 * Real.pi * ∫ x in criticalFeatureCanonicalCore n,
        criticalFeaturePositiveShiftPoleGammaDensity
          (criticalFeatureCanonicalRegularLatticeSummedDisplacementData n).displacement x : ℝ) : ℂ) = _
  simpa only [criticalFeatureCanonicalRegularNonzeroFourierAliasAtPhase] using h

/-- Source data choose a real phase at which the full physical core dominates its zero mode. -/
theorem exists_criticalFeatureCanonicalDealiasingPhase
    (n : ℕ) :
    ∃ theta : ℝ,
      criticalFeatureCanonicalCorePoleGammaZeroMode n
          (criticalFeatureCanonicalRegularLatticeSummedDisplacementData n).displacement ≤
        criticalFeatureCanonicalCoreFullPoleGammaObservableAtPhase n
          (criticalFeatureCanonicalRegularLatticeSummedDisplacementData n).displacement theta := by
  obtain ⟨theta, htheta⟩ :=
    exists_real_criticalFeatureSourceAliasPhase_re_nonneg
      (volume.restrict (criticalFeatureCanonicalCore n))
      (integrableOn_criticalFeatureCanonicalRegularPoleGammaDensity n)
  refine ⟨theta, ?_⟩
  have heq :=
    ofReal_criticalFeatureCanonicalCoreFullPoleGammaObservableAtPhase_sub_zeroMode_eq_alias
      n theta
  have hre := congrArg Complex.re heq
  simp only [ofReal_re] at hre
  change 0 ≤ (criticalFeatureCanonicalRegularNonzeroFourierAliasAtPhase n theta).re at htheta
  linarith

/-- Canonical source-selected real phase.  Definition contains no zero or divisor data. -/
def criticalFeatureCanonicalDealiasingPhase (n : ℕ) : ℝ :=
  Classical.choose (exists_criticalFeatureCanonicalDealiasingPhase n)

theorem criticalFeatureCanonicalDealiasingPhase_spec (n : ℕ) :
    criticalFeatureCanonicalCorePoleGammaZeroMode n
        (criticalFeatureCanonicalRegularLatticeSummedDisplacementData n).displacement ≤
      criticalFeatureCanonicalCoreFullPoleGammaObservableAtPhase n
        (criticalFeatureCanonicalRegularLatticeSummedDisplacementData n).displacement
        (criticalFeatureCanonicalDealiasingPhase n) :=
  Classical.choose_spec (exists_criticalFeatureCanonicalDealiasingPhase n)

/-- Finite translated-lattice pole--Gamma observable on the canonical core. -/
def criticalFeatureCanonicalCoreTranslatedFinitePoleGammaObservable
    (n : ℕ) (eta theta : ℝ) : ℝ :=
  ∫ x in criticalFeatureCanonicalCore n,
    criticalFeatureTranslatedFiniteRealBoundaryLatticeWeight theta
        (criticalFeatureCanonicalLatticeWindow n) x *
      criticalFeaturePositiveShiftPoleGammaDensity eta x

/-- Literal source contribution omitted by the finite translated lattice. -/
def criticalFeatureCanonicalTranslatedInteriorOmittedAlias
    (n : ℕ) (eta theta : ℝ) : ℝ :=
  criticalFeatureCanonicalCoreFullPoleGammaObservableAtPhase n eta theta -
    criticalFeatureCanonicalCoreTranslatedFinitePoleGammaObservable n eta theta

/-- At the selected phase, the one-sided finite-core error pays no nonzero Fourier-alias norm. -/
theorem neg_criticalFeatureCanonicalCoreTranslatedFinitePoleGammaObservable_sub_zeroMode_le_omitted
    (n : ℕ) :
    -(criticalFeatureCanonicalCoreTranslatedFinitePoleGammaObservable n
        (criticalFeatureCanonicalRegularLatticeSummedDisplacementData n).displacement
        (criticalFeatureCanonicalDealiasingPhase n) -
      criticalFeatureCanonicalCorePoleGammaZeroMode n
        (criticalFeatureCanonicalRegularLatticeSummedDisplacementData n).displacement) ≤
      |criticalFeatureCanonicalTranslatedInteriorOmittedAlias n
        (criticalFeatureCanonicalRegularLatticeSummedDisplacementData n).displacement
        (criticalFeatureCanonicalDealiasingPhase n)| := by
  have hphase := criticalFeatureCanonicalDealiasingPhase_spec n
  have habs := le_abs_self
    (criticalFeatureCanonicalTranslatedInteriorOmittedAlias n
      (criticalFeatureCanonicalRegularLatticeSummedDisplacementData n).displacement
      (criticalFeatureCanonicalDealiasingPhase n))
  rw [criticalFeatureCanonicalTranslatedInteriorOmittedAlias] at habs ⊢
  linarith

end

end RHTower
