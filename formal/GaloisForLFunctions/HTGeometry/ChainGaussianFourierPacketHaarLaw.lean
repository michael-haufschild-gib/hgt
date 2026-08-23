import GaloisForLFunctions.HTGeometry.SortedGapRatioGlobalStrongExtremality
import GaloisForLFunctions.HTGeometry.ChainVwaSphereNull
import GaloisForLFunctions.HTGeometry.GaussianAffinePauliProjectiveGenericityLaw

open MeasureTheory ProbabilityTheory Metric Set

namespace GaloisForLFunctions.HTGeometry

noncomputable section

set_option linter.unusedSectionVars false

variable {N D n : ℕ} {P : Fin N → Matrix (Fin D) (Fin D) ℂ}

/-- Uniform translated-window Haar discrepancy for every finite Fourier
packet, at every strict multiplicative Sobolev exponent. -/
def HasMultiplicativeFourierPacketHaarLaw (y : Fin n → ℝ) : Prop :=
  ∀ eps : ℝ, 0 < eps →
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (a₀ : ℂ) (s : Finset (Fin n → ℤ)) (c : (Fin n → ℤ) → ℂ),
        (∀ q ∈ s, q ≠ 0) → ∀ u T : ℝ, 0 < T →
          ‖((1 / (T : ℂ)) *
              ∫ t in u..(u + T),
                (a₀ + ∑ q ∈ s, c q *
                  Complex.exp ((t : ℂ) *
                    (KleinbockMargulis.dotProd q y : ℂ) * Complex.I))) - a₀‖ ≤
            (2 * C / T) *
              KleinbockMargulis.multiplicativeFourierL1Cost s c eps

theorem hasMultiplicativeFourierPacketHaarLaw_of_not_vwma
    {y : Fin n → ℝ} (hy : ¬ KleinbockMargulis.VWMA y) :
    HasMultiplicativeFourierPacketHaarLaw y := by
  intro eps heps
  exact KleinbockMargulis.exists_global_finiteFourierPacketHaarDiscrepancy hy heps

/-- For every escaping Hermitian family, failure of the complete finite-
Fourier moving-window law is Lebesgue-null on the simple-spectrum locus. -/
theorem volume_not_hasMultiplicativeFourierPacketHaarLaw_sortedGapRatio_eq_zero
    [NeZero N]
    (hP : ∀ a, (P a).IsHermitian)
    (hS : SpectrumEscapesRealRelations (Set.range (spectralEnsembleMatrix P)))
    {anchor clock : Fin D} {ι : Fin n → Fin D} (hι : Function.Injective ι)
    (hanchor : ∀ k, ι k ≠ anchor) (hclock : ∀ k, ι k ≠ clock)
    (hac : anchor ≠ clock) :
    volume {x ∈ simpleEnsembleLocus hP |
      ¬ HasMultiplicativeFourierPacketHaarLaw
        (fun k => anchoredGapRatioMap
          (sortedEnsembleSpectrum hP x) anchor clock ι k)} = 0 := by
  refine measure_mono_null ?_
    (volume_vwma_sortedGapRatio_eq_zero hP hS hι hanchor hclock hac)
  rintro x ⟨hx, hfail⟩
  refine ⟨hx, ?_⟩
  by_contra hvwma
  exact hfail (hasMultiplicativeFourierPacketHaarLaw_of_not_vwma hvwma)

/-- **One-draw local-Hamiltonian Fourier law.**  A standard Gaussian draw of
one ordinary time-independent nearest-neighbour Pauli Hamiltonian has, almost
surely, simple spectrum and the complete finite-Fourier moving-window Haar law
for its projective spectral flow. -/
theorem chainGapRatio_hasMultiplicativeFourierPacketHaarLaw_ae_stdGaussian
    (k : ℕ)
    {anchor clock : Fin (2 ^ (k + 3))}
    {ι : Fin n → Fin (2 ^ (k + 3))}
    (hι : Function.Injective ι) (hanchor : ∀ j, ι j ≠ anchor)
    (hclock : ∀ j, ι j ≠ clock) (hac : anchor ≠ clock) :
    ∀ᵐ x ∂(stdGaussian
      (EuclideanSpace ℝ (Fin (Fintype.card (ChainLabel (k + 3)))))),
      WithLp.ofLp x ∈ simpleEnsembleLocus
        (chainPauliFin_isHermitian (k + 3)) ∧
      HasMultiplicativeFourierPacketHaarLaw
        (fun j => anchoredGapRatioMap
          (sortedEnsembleSpectrum (chainPauliFin_isHermitian (k + 3))
            (WithLp.ofLp x)) anchor clock ι j) := by
  classical
  let m := Fintype.card (ChainLabel (k + 3))
  let hP := chainPauliFin_isHermitian (k + 3)
  have hmp := PiLp.volume_preserving_ofLp (Fin m)
  have hnullSimple :
      (volume : Measure (EuclideanSpace ℝ (Fin m)))
        {x | WithLp.ofLp x ∉ simpleEnsembleLocus hP} = 0 := by
    have hsub :
        {θ : Fin m → ℝ | θ ∉ simpleEnsembleLocus hP} ⊆
          {θ | ¬ MaximallyProjectiveEnergy
            (isHermitian_spectralEnsembleMatrix hP θ).eigenvalues} := by
      intro θ hθ hmax
      exact hθ hmax.injective
    have hbase :
        (volume : Measure (Fin m → ℝ))
          {θ | θ ∉ simpleEnsembleLocus hP} = 0 :=
      measure_mono_null hsub (volume_notMaximallyProjective_chain_eq_zero k)
    have hpre :
        {x : EuclideanSpace ℝ (Fin m) |
          WithLp.ofLp x ∉ simpleEnsembleLocus hP} =
          WithLp.ofLp ⁻¹' {θ | θ ∉ simpleEnsembleLocus hP} := rfl
    rw [hpre, hmp.measure_preimage (NullMeasurableSet.of_null hbase), hbase]
  have hnullLaw :
      (volume : Measure (EuclideanSpace ℝ (Fin m)))
        {x | WithLp.ofLp x ∈ simpleEnsembleLocus hP ∧
          ¬ HasMultiplicativeFourierPacketHaarLaw
            (fun j => anchoredGapRatioMap
              (sortedEnsembleSpectrum hP (WithLp.ofLp x))
              anchor clock ι j)} = 0 := by
    have hbase :
        (volume : Measure (Fin m → ℝ))
          {θ ∈ simpleEnsembleLocus hP |
            ¬ HasMultiplicativeFourierPacketHaarLaw
              (fun j => anchoredGapRatioMap
                (sortedEnsembleSpectrum hP θ) anchor clock ι j)} = 0 :=
      volume_not_hasMultiplicativeFourierPacketHaarLaw_sortedGapRatio_eq_zero
        hP (chainPauliFin_spectrumEscapesRealRelations k)
        hι hanchor hclock hac
    have hpre :
        {x : EuclideanSpace ℝ (Fin m) |
          WithLp.ofLp x ∈ simpleEnsembleLocus hP ∧
            ¬ HasMultiplicativeFourierPacketHaarLaw
              (fun j => anchoredGapRatioMap
                (sortedEnsembleSpectrum hP (WithLp.ofLp x))
                anchor clock ι j)} =
          WithLp.ofLp ⁻¹' {θ ∈ simpleEnsembleLocus hP |
            ¬ HasMultiplicativeFourierPacketHaarLaw
              (fun j => anchoredGapRatioMap
                (sortedEnsembleSpectrum hP θ) anchor clock ι j)} := rfl
    rw [hpre, hmp.measure_preimage (NullMeasurableSet.of_null hbase), hbase]
  have hnullBad :
      (volume : Measure (EuclideanSpace ℝ (Fin m)))
        ({x | WithLp.ofLp x ∉ simpleEnsembleLocus hP} ∪
          {x | WithLp.ofLp x ∈ simpleEnsembleLocus hP ∧
            ¬ HasMultiplicativeFourierPacketHaarLaw
              (fun j => anchoredGapRatioMap
                (sortedEnsembleSpectrum hP (WithLp.ofLp x))
                anchor clock ι j)}) = 0 :=
    measure_union_null hnullSimple hnullLaw
  have hgauss :
      stdGaussian (EuclideanSpace ℝ (Fin m))
        ({x | WithLp.ofLp x ∉ simpleEnsembleLocus hP} ∪
          {x | WithLp.ofLp x ∈ simpleEnsembleLocus hP ∧
            ¬ HasMultiplicativeFourierPacketHaarLaw
              (fun j => anchoredGapRatioMap
                (sortedEnsembleSpectrum hP (WithLp.ofLp x))
                anchor clock ι j)}) = 0 :=
    (stdGaussian_absolutelyContinuous_volume_finEuclidean m) hnullBad
  refine MeasureTheory.ae_iff.mpr (measure_mono_null ?_ hgauss)
  intro x hx
  by_cases hs : WithLp.ofLp x ∈ simpleEnsembleLocus hP
  · exact Or.inr ⟨hs, fun hlaw => hx ⟨hs, hlaw⟩⟩
  · exact Or.inl hs

end

end GaloisForLFunctions.HTGeometry
