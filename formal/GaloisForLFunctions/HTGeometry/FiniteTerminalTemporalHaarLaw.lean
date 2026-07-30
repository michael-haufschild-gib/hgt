import GaloisForLFunctions.HTGeometry.FiniteTemporalCascadeStabilizationLaw
import GaloisForLFunctions.HTGeometry.ObserverTemporalPhaseSupportLaw

/-!
# Terminal projective Haar law for finite analytic spectra

Every finite analytic spectrum has a last temporal birth. Beyond one finite
inverse-power horizon, every active projective phase character is completely
dephased and every exact character remains identically one. Thus the
projective Fourier transform of the limiting phase law is the Haar transform
of the terminal observable phase quotient.
-/

open Filter MeasureTheory Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Terminal projective Haar transform: exact relations have coefficient
one and every active character has coefficient zero. -/
def terminalProjectiveHaarCoefficient
    {d : Type*} [Fintype d]
    (series : d → FormalMultilinearSeries ℂ ℂ ℂ)
    (k : ProjectiveCharacter d) : ℂ :=
  by
    classical
    exact
      if SpectralCharacterActive (spectralTaylorJet series) k
      then 0 else 1

/-- **Finite terminal temporal Haar law.** Every finite analytic real
spectrum has one finite horizon order after which the unique limiting phase
law has terminal projective Haar coefficients at every later
inverse-power horizon. -/
theorem exists_terminalProjectiveHaar_horizon
    {d : Type*} [Fintype d]
    (energy : d → ℂ → ℂ)
    (series : d → FormalMultilinearSeries ℂ ℂ ℂ)
    (henergy : ∀ i, HasFPowerSeriesAt (energy i) (series i) 0)
    (omega : ℝ → d → ℝ)
    (hreal : ∀ i, ∀ᶠ (g : ℝ) in 𝓝[>] (0 : ℝ),
      energy i (g : ℂ) = (omega g i : ℂ)) :
    ∃ R : ℕ, ∀ r, R ≤ r → ∀ {τ : ℝ}, 0 < τ →
      ∃! μ : ProbabilityMeasure (UnitAddTorus d),
        Tendsto
          (fun g =>
            finiteTorusPhaseProbabilityMeasure
              (omega g) (τ / g ^ r))
          (𝓝[>] 0) (𝓝 μ) ∧
        ∀ k : ProjectiveCharacter d,
          (∫ x, UnitAddTorus.mFourier
              (finiteCharacterOfProjective k) x
            ∂(μ : Measure (UnitAddTorus d))) =
            terminalProjectiveHaarCoefficient series k := by
  obtain ⟨R, hR⟩ :=
    exists_spectralConstraintFiltration_stabilization
      (spectralTaylorJet series)
  refine ⟨R, fun r hRr τ hτ => ?_⟩
  obtain ⟨μ, hμ, hμunique⟩ :=
    existsUnique_finiteAnalyticTemporalPhaseSupport
      energy series henergy omega hreal r hτ
  refine ⟨μ, ⟨hμ.1, ?_⟩, ?_⟩
  · intro k
    by_cases hactive :
        SpectralCharacterActive (spectralTaylorJet series) k
    · have hnotmem :
          k ∉ spectralConstraintFiltration
            (spectralTaylorJet series) R := by
        rw [mem_stabilizedConstraint_iff_not_active
          (spectralTaylorJet series) R hR k]
        exact not_not_intro hactive
      have hbirth_lt_R :
          spectralCharacterBirthOrder
              (spectralTaylorJet series) k hactive < R := by
        by_contra hnot
        have hRbirth :
            R ≤ spectralCharacterBirthOrder
              (spectralTaylorJet series) k hactive :=
          not_lt.mp hnot
        exact hnotmem
          ((mem_spectralConstraintFiltration_iff_le_birthOrder
            hactive R).mpr hRbirth)
      obtain ⟨c, hc, hwall⟩ :=
        finiteProjectivePhaseCoefficient_wallCrossing
          energy series henergy omega hreal k hactive hτ
      let coefficient :
          ProbabilityMeasure (UnitAddTorus d) → ℂ :=
        fun ρ =>
          ∫ x, UnitAddTorus.mFourier
              (finiteCharacterOfProjective k) x
            ∂(ρ : Measure (UnitAddTorus d))
      have hcoefficient :
          Tendsto
            (fun g =>
              coefficient
                (finiteTorusPhaseProbabilityMeasure
                  (omega g) (τ / g ^ r)))
            (𝓝[>] 0) (𝓝 (coefficient μ)) :=
        (continuous_integral_complex_continuousMap
          (UnitAddTorus.mFourier
            (finiteCharacterOfProjective k))).continuousAt.tendsto.comp
              hμ.1
      have hbirth_lt_r :
          spectralCharacterBirthOrder
              (spectralTaylorJet series) k hactive < r :=
        hbirth_lt_R.trans_le hRr
      have hzero :
          Tendsto
            (fun g =>
              coefficient
                (finiteTorusPhaseProbabilityMeasure
                  (omega g) (τ / g ^ r)))
            (𝓝[>] 0) (𝓝 0) := by
        simpa [coefficient, finiteProjectivePhaseCoefficient] using
          hwall.2.2 r hbirth_lt_r
      have heq : coefficient μ = 0 :=
        tendsto_nhds_unique hcoefficient hzero
      simpa [terminalProjectiveHaarCoefficient, hactive,
        coefficient] using heq
    · have hmem :
          k ∈ spectralConstraintFiltration
            (spectralTaylorJet series) (r + 1) :=
        (not_spectralCharacterActive_iff_forall_mem.mp hactive) _
      have hconstraint : phaseLawConstraint μ k :=
        (hμ.2 k).mpr hmem
      have hone :=
        (phaseLawConstraint_iff_integral_eq_one μ k).mp hconstraint
      simpa [terminalProjectiveHaarCoefficient, hactive] using hone
  · intro ν hν
    exact tendsto_nhds_unique hν.1 hμ.1

end

end GaloisForLFunctions.HTGeometry
