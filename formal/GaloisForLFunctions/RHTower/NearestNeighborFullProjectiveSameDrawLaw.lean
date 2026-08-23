import GaloisForLFunctions.HTGeometry.NearestNeighborPathSpectrumRealRelationEscape
import GaloisForLFunctions.RHTower.FullProjectiveChoiCircuitFirstReturnLaw
import GaloisForLFunctions.RHTower.FullProjectiveChoiPhysicalSpectrumLaw

/-!
# Exact same-draw growth and full-projective first return

The ordinary nearest-neighbour path ensemble used by the laboratory-time growth theorem is
reindexed onto its full finite Hilbert space.  Real-relation escape makes its complete sorted
gap-ratio packet strongly extremal.  Removing the resulting null exceptional set from the
positive-measure growth event leaves one fixed Hamiltonian with both properties.

The final theorem retains every spectral level, a positive physical clock gap, exact restoration
of the physical frequency packet, and the adaptive finite-target first-return law.  The latter
contains every padded finite circuit dictionary as a specialization.
-/

open scoped BigOperators
open Set MeasureTheory ProbabilityTheory
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.StaticLocalLaboratoryComplexityGrowthLaw

namespace RHTower

noncomputable section

/-- Canonical enumeration of the full `2L`-qubit nearest-neighbour carrier. -/
def nearestNeighborPathFinEquiv (L : ℕ) :
    Config (PairQubit L) ≃ Fin (2 ^ (L * 2)) :=
  (pairPathConfigurationEquiv L).trans (qubitConfigFin (L * 2))

/-- Exact nearest-neighbour generator after full-Hilbert-space enumeration. -/
def nearestNeighborPathFinGenerator (L : ℕ)
    (i : Fin (nearestNeighborPathLocalParameterCount L)) :
    Matrix (Fin (2 ^ (L * 2))) (Fin (2 ^ (L * 2))) ℂ :=
  Matrix.reindex (nearestNeighborPathFinEquiv L) (nearestNeighborPathFinEquiv L)
    (nearestNeighborPathLocalGenerator L i)

theorem nearestNeighborPathFinGenerator_isHermitian (L : ℕ)
    (i : Fin (nearestNeighborPathLocalParameterCount L)) :
    (nearestNeighborPathFinGenerator L i).IsHermitian := by
  exact (nearestNeighborPathLocalGenerator_isHermitian L i).reindex
    (nearestNeighborPathFinEquiv L)

/-- Reindexing changes neither draw nor Hamiltonian: coefficient vectors agree pointwise. -/
theorem spectralEnsembleMatrix_nearestNeighborPathFinGenerator
    (L : ℕ) (p : Fin (nearestNeighborPathLocalParameterCount L) → ℝ) :
    spectralEnsembleMatrix (nearestNeighborPathFinGenerator L) p =
      Matrix.reindex (nearestNeighborPathFinEquiv L) (nearestNeighborPathFinEquiv L)
        (nearestNeighborPathLocalHamiltonian L p) := by
  ext x y
  simp [spectralEnsembleMatrix, nearestNeighborPathFinGenerator,
    nearestNeighborPathLocalHamiltonian, realAffineMatrix, Matrix.reindex_apply,
    Matrix.sum_apply, Matrix.smul_apply, Complex.real_smul]

/-- The exact growth ensemble, not a larger surrogate, escapes every balanced real relation. -/
theorem nearestNeighborPathFinGenerator_spectrumEscapesRealRelations
    (k : ℕ) :
    SpectrumEscapesRealRelations
      (Set.range (spectralEnsembleMatrix
        (nearestNeighborPathFinGenerator (k + 2)))) := by
  let e := nearestNeighborPathFinEquiv (k + 2)
  apply (nearestNeighborPathLocalGenerator_spectrumEscapesRealRelations k).reindex e
  rintro H ⟨p, rfl⟩
  refine ⟨p, ?_⟩
  simpa [e, nearestNeighborPathLocalHamiltonian] using
    (spectralEnsembleMatrix_nearestNeighborPathFinGenerator (k + 2) p)

/-- Every maximally projective growth draw lies in the enumerated simple-spectrum chart. -/
theorem nearestNeighborPathFin_simple_of_mem_maximalSet
    {L : ℕ} {p : Fin (nearestNeighborPathLocalParameterCount L) → ℝ}
    (hp : p ∈ nearestNeighborPathLocalMaximalSet L) :
    p ∈ simpleEnsembleLocus (nearestNeighborPathFinGenerator_isHermitian L) := by
  have hmax := Matrix.IsHermitian.maximallyProjective_reindexAlgEquiv
      (nearestNeighborPathFinEquiv L)
      (nearestNeighborPathLocalHamiltonian_isHermitian L p)
      (maximallyProjectiveEnergy_nearestNeighborPathLocalHamiltonian hp)
  change Function.Injective
    (isHermitian_spectralEnsembleMatrix
      (nearestNeighborPathFinGenerator_isHermitian L) p).eigenvalues
  have heig := isHermitian_eigenvalues_congr
    (isHermitian_spectralEnsembleMatrix
      (nearestNeighborPathFinGenerator_isHermitian L) p)
    ((nearestNeighborPathLocalHamiltonian_isHermitian L p).reindex
      (nearestNeighborPathFinEquiv L))
    (spectralEnsembleMatrix_nearestNeighborPathFinGenerator L p)
  rw [heig]
  exact hmax.injective

/-- Lowest sorted spectral level. -/
def nearestNeighborFullProjectiveAnchor (k : ℕ) :
    Fin (2 ^ ((k + 2) * 2)) :=
  ⟨0, Nat.two_pow_pos _⟩

/-- Second sorted spectral level, used as positive physical clock. -/
def nearestNeighborFullProjectiveClock (k : ℕ) :
    Fin (2 ^ ((k + 2) * 2)) :=
  ⟨1, Nat.one_lt_pow (by omega) (by omega)⟩

/-- Every spectral level beyond the anchor and clock. -/
def nearestNeighborFullProjectiveTailIndex (k : ℕ) :
    Fin (2 ^ ((k + 2) * 2) - 2) → Fin (2 ^ ((k + 2) * 2)) :=
  fun j => ⟨j.1 + 2, by omega⟩

theorem nearestNeighborFullProjectiveTailIndex_injective (k : ℕ) :
    Function.Injective (nearestNeighborFullProjectiveTailIndex k) := by
  intro i j hij
  apply Fin.ext
  have hv := congrArg Fin.val hij
  change i.1 + 2 = j.1 + 2 at hv
  omega

theorem nearestNeighborFullProjectiveTailIndex_ne_anchor
    (k : ℕ) (j : Fin (2 ^ ((k + 2) * 2) - 2)) :
    nearestNeighborFullProjectiveTailIndex k j ≠
      nearestNeighborFullProjectiveAnchor k := by
  intro h
  have hv := congrArg Fin.val h
  simp [nearestNeighborFullProjectiveTailIndex,
    nearestNeighborFullProjectiveAnchor] at hv

theorem nearestNeighborFullProjectiveTailIndex_ne_clock
    (k : ℕ) (j : Fin (2 ^ ((k + 2) * 2) - 2)) :
    nearestNeighborFullProjectiveTailIndex k j ≠
      nearestNeighborFullProjectiveClock k := by
  intro h
  have hv := congrArg Fin.val h
  simp [nearestNeighborFullProjectiveTailIndex,
    nearestNeighborFullProjectiveClock] at hv

theorem nearestNeighborFullProjectiveAnchor_ne_clock (k : ℕ) :
    nearestNeighborFullProjectiveAnchor k ≠
      nearestNeighborFullProjectiveClock k := by
  intro h
  have hv := congrArg Fin.val h
  simp [nearestNeighborFullProjectiveAnchor,
    nearestNeighborFullProjectiveClock] at hv

def nearestNeighborFullProjectiveSpectrum (k : ℕ)
    (p : Fin (nearestNeighborPathLocalParameterCount (k + 2)) → ℝ) :
    Fin (2 ^ ((k + 2) * 2)) → ℝ :=
  sortedEnsembleSpectrum
    (nearestNeighborPathFinGenerator_isHermitian (k + 2)) p

/-- All clock-normalized spectral gaps, with no discarded level. -/
def nearestNeighborFullProjectiveRatioPacket (k : ℕ)
    (p : Fin (nearestNeighborPathLocalParameterCount (k + 2)) → ℝ) :
    Fin (2 ^ ((k + 2) * 2) - 2) → ℝ :=
  anchoredGapRatioMap (nearestNeighborFullProjectiveSpectrum k p)
    (nearestNeighborFullProjectiveAnchor k)
    (nearestNeighborFullProjectiveClock k)
    (nearestNeighborFullProjectiveTailIndex k)

def nearestNeighborFullProjectiveClockGap (k : ℕ)
    (p : Fin (nearestNeighborPathLocalParameterCount (k + 2)) → ℝ) : ℝ :=
  nearestNeighborFullProjectiveSpectrum k p
      (nearestNeighborFullProjectiveClock k) -
    nearestNeighborFullProjectiveSpectrum k p
      (nearestNeighborFullProjectiveAnchor k)

/-- Physical anchored gaps: clock first, then every remaining level. -/
def nearestNeighborFullProjectivePhysicalFrequency (k : ℕ)
    (p : Fin (nearestNeighborPathLocalParameterCount (k + 2)) → ℝ) :
    Fin ((2 ^ ((k + 2) * 2) - 2) + 1) → ℝ :=
  fullAnchoredGapFrequency (nearestNeighborFullProjectiveSpectrum k p)
    (nearestNeighborFullProjectiveAnchor k)
    (nearestNeighborFullProjectiveClock k)
    (nearestNeighborFullProjectiveTailIndex k)

theorem nearestNeighborFullProjectiveClockGap_pos
    {k : ℕ} {p : Fin (nearestNeighborPathLocalParameterCount (k + 2)) → ℝ}
    (hp : p ∈ simpleEnsembleLocus
      (nearestNeighborPathFinGenerator_isHermitian (k + 2))) :
    0 < nearestNeighborFullProjectiveClockGap k p := by
  apply sortedEnsembleSpectrum_clockGap_pos
    (nearestNeighborPathFinGenerator_isHermitian (k + 2)) hp
  exact Fin.mk_lt_mk.mpr (by norm_num)

/-- Full-projective strong extremality for the exact nearest-neighbour growth ensemble. -/
theorem volume_nearestNeighborFullProjective_vwma_eq_zero
    (k : ℕ) :
    volume {p ∈ simpleEnsembleLocus
        (nearestNeighborPathFinGenerator_isHermitian (k + 2)) |
      KleinbockMargulis.VWMA
        (nearestNeighborFullProjectiveRatioPacket k p)} = 0 := by
  letI : NeZero (nearestNeighborPathLocalParameterCount (k + 2)) :=
    ⟨(nearestNeighborPathLocalParameterCount_pos k).ne'⟩
  simpa [nearestNeighborFullProjectiveRatioPacket,
    nearestNeighborFullProjectiveSpectrum] using
    (volume_vwma_sortedGapRatio_eq_zero
      (nearestNeighborPathFinGenerator_isHermitian (k + 2))
      (nearestNeighborPathFinGenerator_spectrumEscapesRealRelations k)
      (nearestNeighborFullProjectiveTailIndex_injective k)
      (nearestNeighborFullProjectiveTailIndex_ne_anchor k)
      (nearestNeighborFullProjectiveTailIndex_ne_clock k)
      (nearestNeighborFullProjectiveAnchor_ne_clock k))

/-- Failure of the adaptive full-projective first-return law is null for the exact ensemble. -/
theorem volume_nearestNeighborFullProjective_firstReturn_bad_eq_zero
    (k : ℕ) :
    volume {p ∈ simpleEnsembleLocus
        (nearestNeighborPathFinGenerator_isHermitian (k + 2)) |
      ¬ HasFullProjectiveChoiTensorFirstReturnDichotomy
        (nearestNeighborFullProjectiveRatioPacket k p)} = 0 := by
  letI : NeZero (nearestNeighborPathLocalParameterCount (k + 2)) :=
    ⟨(nearestNeighborPathLocalParameterCount_pos k).ne'⟩
  simpa [nearestNeighborFullProjectiveRatioPacket,
    nearestNeighborFullProjectiveSpectrum] using
    (volume_not_hasFullProjectiveChoiTensorFirstReturnDichotomy_eq_zero
      (nearestNeighborPathFinGenerator_isHermitian (k + 2))
      (nearestNeighborPathFinGenerator_spectrumEscapesRealRelations k)
      (nearestNeighborFullProjectiveTailIndex_injective k)
      (nearestNeighborFullProjectiveTailIndex_ne_anchor k)
      (nearestNeighborFullProjectiveTailIndex_ne_clock k)
      (nearestNeighborFullProjectiveAnchor_ne_clock k))

/-- **Same-draw growth and full-spectrum first return.**  A positive-measure laboratory growth
event remains nonempty after deleting the strongly approximable exceptional set.  Hence one fixed
ordinary time-independent nearest-neighbour Hamiltonian simultaneously has the robust growth ramp,
a simple spectrum, a strongly extremal packet containing every spectral level, a positive physical
clock, and the complete adaptive finite-target first-return dichotomy. -/
theorem exists_nearestNeighborPath_sameDraw_growth_fullProjectiveFirstReturn
    {k : ℕ} {T ε ρ : ℝ}
    (hT : 0 ≤ T) (hε : 0 < ε) (hεmax : ε ≤ 1 / 200)
    (hρ : 0 < ρ)
    (hscale : T * (ρ * nearestNeighborPathLocalGeneratorMass (k + 2)) ≤ ε) :
    ∃ p : Fin (nearestNeighborPathLocalParameterCount (k + 2)) → ℝ,
      p ∈ nearestNeighborPathGaussianGrowthMaximalEvent (k + 2) T ε ∧
      p ∈ simpleEnsembleLocus
        (nearestNeighborPathFinGenerator_isHermitian (k + 2)) ∧
      ¬ KleinbockMargulis.VWMA
        (nearestNeighborFullProjectiveRatioPacket k p) ∧
      0 < nearestNeighborFullProjectiveClockGap k p ∧
      HasFullProjectiveChoiTensorFirstReturnDichotomy
        (nearestNeighborFullProjectiveRatioPacket k p) ∧
      clockScaledFullProjectiveFrequency
          (nearestNeighborFullProjectiveClockGap k p)
          (nearestNeighborFullProjectiveRatioPacket k p) =
        nearestNeighborFullProjectivePhysicalFrequency k p := by
  let μ := centredProductGaussian
    (Fin (nearestNeighborPathLocalParameterCount (k + 2))) 1
  let bad := {p ∈ simpleEnsembleLocus
      (nearestNeighborPathFinGenerator_isHermitian (k + 2)) |
    KleinbockMargulis.VWMA
      (nearestNeighborFullProjectiveRatioPacket k p)}
  have hbadVolume : (volume : Measure
      (Fin (nearestNeighborPathLocalParameterCount (k + 2)) → ℝ)) bad = 0 := by
    simpa only [bad] using
      volume_nearestNeighborFullProjective_vwma_eq_zero k
  have hbad : μ bad = 0 := by
    apply (productGaussian_absolutelyContinuous
      (nearestNeighborPathLocalParameterCount (k + 2)) one_ne_zero
      (fun _ => 0))
    exact hbadVolume
  have hgrowth : 0 < μ
      (nearestNeighborPathGaussianGrowthMaximalEvent (k + 2) T ε) := by
    exact measure_nearestNeighborPathGaussianGrowthMaximalEvent_pos
      (by omega) hT hε hεmax hρ hscale
  have hdiff : μ
      (nearestNeighborPathGaussianGrowthMaximalEvent (k + 2) T ε \ bad) =
      μ (nearestNeighborPathGaussianGrowthMaximalEvent (k + 2) T ε) :=
    measure_sdiff_null hbad
  have hdiffNe : μ
      (nearestNeighborPathGaussianGrowthMaximalEvent (k + 2) T ε \ bad) ≠ 0 := by
    rw [hdiff]
    exact ne_of_gt hgrowth
  obtain ⟨p, hpGrowth, hpNotBad⟩ := nonempty_of_measure_ne_zero hdiffNe
  have hpSimple := nearestNeighborPathFin_simple_of_mem_maximalSet hpGrowth.1
  have hpStrong : ¬ KleinbockMargulis.VWMA
      (nearestNeighborFullProjectiveRatioPacket k p) := by
    intro hpVWMA
    exact hpNotBad ⟨hpSimple, hpVWMA⟩
  have hgap := nearestNeighborFullProjectiveClockGap_pos hpSimple
  have hfrequency :=
    clockScaledFullProjectiveFrequency_anchoredGapRatioMap
      (nearestNeighborFullProjectiveSpectrum k p)
      (nearestNeighborFullProjectiveAnchor k)
      (nearestNeighborFullProjectiveClock k)
      (nearestNeighborFullProjectiveTailIndex k) hgap.ne'
  refine ⟨p, hpGrowth, hpSimple, hpStrong, hgap,
    hasFullProjectiveChoiTensorFirstReturnDichotomy_of_not_vwma hpStrong, ?_⟩
  simpa only [nearestNeighborFullProjectiveClockGap,
    nearestNeighborFullProjectiveRatioPacket,
    nearestNeighborFullProjectivePhysicalFrequency] using hfrequency

end

end RHTower
